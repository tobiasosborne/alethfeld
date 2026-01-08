(ns alethfeld.commands.add-node
  "CLI command for adding nodes to a semantic proof graph."
  (:require [clojure.string :as str]
            [alethfeld.io :as io]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.result :as r]))

(def cli-options
  [["-s" "--stdin" "Read node definition from stdin instead of file"]
   ["-d" "--dry-run" "Validate but don't write changes"]
   ["-o" "--output FILE" "Write to a different file"]
   ["-h" "--help" "Show help for add-node command"]])

(defn usage []
  (->> ["Add a node to a semantic proof graph."
        ""
        "Usage: alethfeld add-node [options] <graph.edn> [node.edn]"
        ""
        "Arguments:"
        "  graph.edn    The graph file to modify"
        "  node.edn     File containing node definition (EDN format)"
        ""
        "Options:"
        "  -s, --stdin      Read node definition from stdin"
        "  -d, --dry-run    Validate but don't write changes"
        "  -o, --output F   Write to different file (default: overwrite input)"
        "  -h, --help       Show this help"
        ""
        "Node format (EDN):"
        "  {:id :1-abc123"
        "   :type :claim"
        "   :statement \"The claim text\""
        "   :dependencies #{:1-dep1 :1-dep2}"
        "   :scope #{}"
        "   :justification :modus-ponens"
        "   :depth 1"
        "   :display-order 5}"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Operation failed (precondition violation)"
        "  2 - Input error (file not found, parse error)"]
       (str/join \newline)))

(defn- do-add-node
  "Execute the add-node operation with result threading."
  [graph-path node-source options]
  (r/let-ok [graph (io/read-graph graph-path)
             node node-source
             new-graph (add-node/add-node graph node)]
    (if (:dry-run options)
      (r/ok {:dry-run true
             :node-id (:id node)})
      (r/let-ok [_ (io/write-graph (or (:output options) graph-path) new-graph)]
        (r/ok {:node-id (:id node)
               :graph-version (:version new-graph)})))))

(defn- format-success [result]
  (if (:dry-run result)
    (str "OK: Validation passed (dry-run)\n  Node " (:node-id result) " would be added")
    (io/format-edn {:status :ok
                    :message (str "Node " (:node-id result) " added")
                    :graph-version (:graph-version result)})))

(defn- format-add-error [result]
  (let [errors (:error result)]
    (cond
      ;; String error from I/O
      (string? errors)
      (r/exit-err 2 (str "Error: " errors))

      ;; Vector of error maps from ops
      (vector? errors)
      (r/exit-err 1 (str "Error: Operation failed\n" (r/format-op-errors errors)))

      :else
      (r/exit-err 1 (str "Error: " errors)))))

(defn run
  "Run the add-node command."
  [args options]
  (cond
    (:help options)
    (r/exit-ok (usage))

    (empty? args)
    (r/exit-err 2 (str "Error: No graph file specified\n\n" (usage)))

    (and (not (:stdin options)) (< (count args) 2))
    (r/exit-err 2 (str "Error: No node file specified (use --stdin to read from stdin)\n\n" (usage)))

    :else
    (let [graph-path (first args)
          node-source (if (:stdin options)
                        (io/read-edn-stdin)
                        (io/read-edn (second args)))
          result (do-add-node graph-path node-source options)]
      (if (r/ok? result)
        (r/exit-ok (format-success (:ok result)))
        (format-add-error result)))))
