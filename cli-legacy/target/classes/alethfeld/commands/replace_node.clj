(ns alethfeld.commands.replace-node
  "CLI command for replacing rejected nodes."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.replace-node :as replace-node]))

(def cli-options
  [["-s" "--stdin" "Read new node from stdin"]
   ["-d" "--dry-run" "Validate but don't write changes"]
   ["-o" "--output FILE" "Write to different file"]
   ["-h" "--help" "Show help"]])

(defn usage []
  (->> ["Replace a rejected node with a revised version."
        ""
        "Usage: alethfeld replace-node [options] <graph.edn> <old-node-id> [new-node.edn]"
        ""
        "Arguments:"
        "  graph.edn      The graph file to modify"
        "  old-node-id    ID of the rejected node to replace"
        "  new-node.edn   File with new node definition"
        ""
        "Options:"
        "  -s, --stdin      Read new node from stdin"
        "  -d, --dry-run    Validate but don't write"
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

(defn format-errors [errors]
  (str/join \newline
            (map (fn [e] (str "  [" (name (:type e)) "] " (:message e)))
                 errors)))

(defn run [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (< (count args) 2)
    {:exit-code 2 :message (str "Error: Missing arguments\n\n" (usage))}

    (and (not (:stdin options)) (< (count args) 3))
    {:exit-code 2 :message (str "Error: No new node file (use --stdin)\n\n" (usage))}

    :else
    (let [[graph-path old-id-str] args
          graph-result (io/read-graph graph-path)
          old-id-result (parse-node-id old-id-str)]
      (cond
        (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (:error old-id-result)
        {:exit-code 2 :message (:error old-id-result)}

        :else
        (let [node-result (if (:stdin options)
                           (io/read-edn-stdin)
                           (io/read-edn (nth args 2)))]
          (if (:error node-result)
            {:exit-code 2 :message (str "Error reading node: " (:error node-result))}
            (let [result (replace-node/replace-node (:ok graph-result)
                                                    (:ok old-id-result)
                                                    (:ok node-result))]
              (if (:error result)
                {:exit-code 1 :message (str "Error:\n" (format-errors (:error result)))}
                (if (:dry-run options)
                  {:exit-code 0 :message "OK: Validation passed (dry-run)"}
                  (let [output-path (or (:output options) graph-path)
                        write-result (io/write-graph output-path (:ok result))]
                    (if (:error write-result)
                      {:exit-code 2 :message (str "Error writing: " (:error write-result))}
                      {:exit-code 0
                       :message (io/format-edn
                                 {:status :ok
                                  :message (str "Node " (:ok old-id-result) " replaced with " (:id (:ok node-result)))
                                  :graph-version (:version (:ok result))})})))))))))))
