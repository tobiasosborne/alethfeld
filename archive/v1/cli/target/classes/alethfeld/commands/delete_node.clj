(ns alethfeld.commands.delete-node
  "CLI command for deleting (archiving) nodes from a graph."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.delete-node :as delete-node]
            [alethfeld.result :as r]))

(def cli-options
  [["-d" "--dry-run" "Validate but don't write changes"]
   ["-o" "--output FILE" "Write to a different file"]
   ["-h" "--help" "Show help for delete-node command"]])

(defn usage []
  (->> ["Delete (archive) a node from a semantic proof graph."
        ""
        "Usage: alethfeld delete-node [options] <graph.edn> <node-id>"
        ""
        "Arguments:"
        "  graph.edn    The graph file to modify"
        "  node-id      The node ID to delete (keyword, e.g., :1-abc123)"
        ""
        "Options:"
        "  -d, --dry-run    Validate but don't write changes"
        "  -o, --output F   Write to different file"
        "  -h, --help       Show this help"
        ""
        "Notes:"
        "  - Nodes are archived, not destroyed"
        "  - Cannot delete a node that other nodes depend on"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Operation failed"
        "  2 - Input error"]
       (str/join \newline)))

(defn- parse-node-id
  "Parse a node ID from string to keyword."
  [s]
  (try
    (let [parsed (edn/read-string s)]
      (if (keyword? parsed)
        (r/ok parsed)
        (r/err (str "Node ID must be a keyword, got: " (type parsed)))))
    (catch Exception e
      (r/err (str "Failed to parse node ID: " (.getMessage e))))))

(defn- do-delete-node
  "Execute the delete-node operation with result threading."
  [graph-path node-id options]
  (r/let-ok [graph (io/read-graph graph-path)
             new-graph (delete-node/delete-node graph node-id)]
    (if (:dry-run options)
      (r/ok {:dry-run true :node-id node-id})
      (r/let-ok [_ (io/write-graph (or (:output options) graph-path) new-graph)]
        (r/ok {:node-id node-id
               :graph-version (:version new-graph)})))))

(defn- format-success [result]
  (if (:dry-run result)
    (str "OK: Validation passed (dry-run)\n  Node " (:node-id result) " would be archived")
    (io/format-edn {:status :ok
                    :message (str "Node " (:node-id result) " archived")
                    :graph-version (:graph-version result)})))

(defn- format-delete-error [result]
  (let [errors (:error result)]
    (cond
      (string? errors) (r/exit-err 2 (str "Error: " errors))
      (vector? errors) (r/exit-err 1 (str "Error: Operation failed\n" (r/format-op-errors errors)))
      :else (r/exit-err 1 (str "Error: " errors)))))

(defn run
  "Run the delete-node command."
  [args options]
  (cond
    (:help options)
    (r/exit-ok (usage))

    (< (count args) 2)
    (r/exit-err 2 (str "Error: Missing arguments\n\n" (usage)))

    :else
    (let [[graph-path node-id-str] args
          node-id-result (parse-node-id node-id-str)]
      (if (r/err? node-id-result)
        (r/exit-err 2 (:error node-id-result))
        (let [result (do-delete-node graph-path (:ok node-id-result) options)]
          (if (r/ok? result)
            (r/exit-ok (format-success (:ok result)))
            (format-delete-error result)))))))
