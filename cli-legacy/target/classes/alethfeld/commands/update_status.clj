(ns alethfeld.commands.update-status
  "CLI command for updating node verification status."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.update-status :as update-status]))

(def cli-options
  [["-d" "--dry-run" "Validate but don't write changes"]
   ["-o" "--output FILE" "Write to a different file"]
   ["-h" "--help" "Show help for update-status command"]])

(defn usage []
  (->> ["Update the verification status of a node."
        ""
        "Usage: alethfeld update-status [options] <graph.edn> <node-id> <status>"
        ""
        "Arguments:"
        "  graph.edn    The graph file to modify"
        "  node-id      The node ID (keyword, e.g., :1-abc123)"
        "  status       New status: proposed, verified, admitted, rejected"
        ""
        "Options:"
        "  -d, --dry-run    Validate but don't write changes"
        "  -o, --output F   Write to different file"
        "  -h, --help       Show this help"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Operation failed"
        "  2 - Input error"]
       (str/join \newline)))

(defn parse-node-id [s]
  (try
    (let [parsed (edn/read-string s)]
      (if (keyword? parsed)
        {:ok parsed}
        {:error (str "Node ID must be a keyword, got: " (type parsed))}))
    (catch Exception e
      {:error (str "Failed to parse node ID: " (.getMessage e))})))

(defn parse-status [s]
  (let [status (keyword s)]
    (if (contains? update-status/valid-statuses status)
      {:ok status}
      {:error (str "Invalid status '" s "'. Valid: proposed, verified, admitted, rejected")})))

(defn format-errors [errors]
  (str/join \newline
            (map (fn [e] (str "  [" (name (:type e)) "] " (:message e)))
                 errors)))

(defn run-update [graph-path node-id new-status options]
  (let [graph-result (io/read-graph graph-path)]
    (if (:error graph-result)
      {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}
      (let [update-result (update-status/update-status (:ok graph-result) node-id new-status)]
        (if (:error update-result)
          {:exit-code 1
           :message (str "Error: Operation failed\n" (format-errors (:error update-result)))}
          (if (:dry-run options)
            {:exit-code 0
             :message (str "OK: Validation passed (dry-run)\n"
                           "  Node " node-id " would be set to " new-status)}
            (let [output-path (or (:output options) graph-path)
                  write-result (io/write-graph output-path (:ok update-result))]
              (if (:error write-result)
                {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
                {:exit-code 0
                 :message (io/format-edn
                           {:status :ok
                            :message (str "Node " node-id " status updated to " new-status)
                            :graph-version (:version (:ok update-result))})}))))))))

(defn run [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (< (count args) 3)
    {:exit-code 2 :message (str "Error: Missing arguments\n\n" (usage))}

    :else
    (let [[graph-path node-id-str status-str] args
          node-id-result (parse-node-id node-id-str)
          status-result (parse-status status-str)]
      (cond
        (:error node-id-result)
        {:exit-code 2 :message (:error node-id-result)}

        (:error status-result)
        {:exit-code 2 :message (:error status-result)}

        :else
        (run-update graph-path (:ok node-id-result) (:ok status-result) options)))))
