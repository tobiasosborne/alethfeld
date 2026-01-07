(ns alethfeld.commands.update-status
  "CLI command for updating node verification status."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.result :as r]))

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
        (r/ok parsed)
        (r/err (str "Node ID must be a keyword, got: " (type parsed)))))
    (catch Exception e
      (r/err (str "Failed to parse node ID: " (.getMessage e))))))

(defn parse-status [s]
  (let [status (keyword s)]
    (if (contains? update-status/valid-statuses status)
      (r/ok status)
      (r/err (str "Invalid status '" s "'. Valid: proposed, verified, admitted, rejected")))))

(defn- do-update-status
  "Execute the update-status operation with result threading."
  [graph-path node-id new-status options]
  (r/let-ok [graph (io/read-graph graph-path)
             new-graph (update-status/update-status graph node-id new-status)]
    (if (:dry-run options)
      (r/ok {:dry-run true
             :node-id node-id
             :new-status new-status})
      (r/let-ok [_ (io/write-graph (or (:output options) graph-path) new-graph)]
        (r/ok {:node-id node-id
               :new-status new-status
               :graph-version (:version new-graph)})))))

(defn- format-success [result]
  (if (:dry-run result)
    (str "OK: Validation passed (dry-run)\n  Node " (:node-id result) " would be set to " (:new-status result))
    (io/format-edn {:status :ok
                    :message (str "Node " (:node-id result) " status updated to " (:new-status result))
                    :graph-version (:graph-version result)})))

(defn- format-update-error [result]
  (let [errors (:error result)]
    (cond
      (string? errors)
      (r/exit-err 2 (str "Error: " errors))

      (vector? errors)
      (r/exit-err 1 (str "Error: Operation failed\n" (r/format-op-errors errors)))

      :else
      (r/exit-err 1 (str "Error: " errors)))))

(defn run [args options]
  (cond
    (:help options)
    (r/exit-ok (usage))

    (< (count args) 3)
    (r/exit-err 2 (str "Error: Missing arguments\n\n" (usage)))

    :else
    (let [[graph-path node-id-str status-str] args
          parse-result (r/let-ok [node-id (parse-node-id node-id-str)
                                  new-status (parse-status status-str)]
                         (r/ok [node-id new-status]))]
      (if (r/err? parse-result)
        (r/exit-err 2 (:error parse-result))
        (let [[node-id new-status] (:ok parse-result)
              result (do-update-status graph-path node-id new-status options)]
          (if (r/ok? result)
            (r/exit-ok (format-success (:ok result)))
            (format-update-error result)))))))
