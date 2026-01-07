(ns alethfeld.commands.add-node
  "CLI command for adding nodes to a semantic proof graph."
  (:require [clojure.string :as str]
            [alethfeld.io :as io]
            [alethfeld.ops.add-node :as add-node]))

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

(defn run
  "Run the add-node command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No graph file specified\n\n" (usage))}

    (and (not (:stdin options)) (< (count args) 2))
    {:exit-code 2 :message (str "Error: No node file specified (use --stdin to read from stdin)\n\n" (usage))}

    :else
    (let [graph-path (first args)
          graph-result (io/read-graph graph-path)]
      (if (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (let [node-result (if (:stdin options)
                           (io/read-edn-stdin)
                           (io/read-edn (second args)))]
          (if (:error node-result)
            {:exit-code 2 :message (str "Error reading node: " (:error node-result))}

            (let [add-result (add-node/add-node (:ok graph-result) (:ok node-result))]
              (if (:error add-result)
                {:exit-code 1
                 :message (str "Error: Operation failed\n"
                               (str/join \newline
                                         (map #(str "  [" (name (:type %)) "] " (:message %))
                                              (:error add-result))))}

                (if (:dry-run options)
                  {:exit-code 0
                   :message (str "OK: Validation passed (dry-run)\n"
                                 "  Node " (:id (:ok node-result)) " would be added")}

                  (let [output-path (or (:output options) graph-path)
                        write-result (io/write-graph output-path (:ok add-result))]
                    (if (:error write-result)
                      {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
                      {:exit-code 0
                       :message (io/format-edn
                                 {:status :ok
                                  :message (str "Node " (:id (:ok node-result)) " added")
                                  :graph-version (:version (:ok add-result))})})))))))))))
