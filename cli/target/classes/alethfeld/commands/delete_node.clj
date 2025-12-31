(ns alethfeld.commands.delete-node
  "CLI command for deleting (archiving) nodes from a graph."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.delete-node :as delete-node]))

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

(defn parse-node-id
  "Parse a node ID from string to keyword."
  [s]
  (try
    (let [parsed (edn/read-string s)]
      (if (keyword? parsed)
        {:ok parsed}
        {:error (str "Node ID must be a keyword, got: " (type parsed))}))
    (catch Exception e
      {:error (str "Failed to parse node ID: " (.getMessage e))})))

(defn run
  "Run the delete-node command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (< (count args) 2)
    {:exit-code 2 :message (str "Error: Missing arguments\n\n" (usage))}

    :else
    (let [[graph-path node-id-str] args
          graph-result (io/read-graph graph-path)]
      (if (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (let [node-id-result (parse-node-id node-id-str)]
          (if (:error node-id-result)
            {:exit-code 2 :message (:error node-id-result)}

            (let [delete-result (delete-node/delete-node
                                 (:ok graph-result)
                                 (:ok node-id-result))]
              (if (:error delete-result)
                {:exit-code 1
                 :message (str "Error: Operation failed\n"
                               (str/join \newline
                                         (map #(str "  [" (name (:type %)) "] " (:message %))
                                              (:error delete-result))))}

                (if (:dry-run options)
                  {:exit-code 0
                   :message (str "OK: Validation passed (dry-run)\n"
                                 "  Node " (:ok node-id-result) " would be archived")}

                  (let [output-path (or (:output options) graph-path)
                        write-result (io/write-graph output-path (:ok delete-result))]
                    (if (:error write-result)
                      {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
                      {:exit-code 0
                       :message (io/format-edn
                                 {:status :ok
                                  :message (str "Node " (:ok node-id-result) " archived")
                                  :graph-version (:version (:ok delete-result))})})))))))))))
