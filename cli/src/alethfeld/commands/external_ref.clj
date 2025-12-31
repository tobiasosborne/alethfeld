(ns alethfeld.commands.external-ref
  "CLI commands for external reference operations."
  (:require [clojure.string :as str]
            [alethfeld.io :as io]
            [alethfeld.ops.external-ref :as ext-ref]))

(def cli-options
  [["-a" "--add" "Add a new external reference"]
   ["-u" "--update REF-ID" "Update an existing reference"]
   ["-s" "--stdin" "Read input from stdin"]
   ["-d" "--dry-run" "Validate but don't write"]
   ["-o" "--output FILE" "Write to different file"]
   ["-h" "--help" "Show help"]])

(defn usage []
  (->> ["Manage external references (literature citations)."
        ""
        "Usage:"
        "  alethfeld external-ref --add <graph.edn> [ref.edn]"
        "  alethfeld external-ref --update <ref-id> <graph.edn> [result.edn]"
        ""
        "Options:"
        "  -a, --add          Add new reference"
        "  -u, --update ID    Update reference ID"
        "  -s, --stdin        Read input from stdin"
        "  -d, --dry-run      Validate but don't write"
        "  -o, --output F     Write to different file"
        "  -h, --help         Show this help"
        ""
        "Reference format (for --add):"
        "  {:doi \"10.1234/example\""
        "   :claimed-statement \"The theorem states...\"}"
        ""
        "Verification result format (for --update):"
        "  {:status :verified"
        "   :verified-statement \"Actual text...\""
        "   :bibdata {:authors [\"A\"] :title \"T\" :year 2024}}"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Operation failed"
        "  2 - Input error"]
       (str/join \newline)))

(defn format-errors [errors]
  (str/join \newline
            (map (fn [e] (str "  [" (name (:type e)) "] " (:message e)))
                 errors)))

(defn run-add [graph-path input-result options]
  (let [graph-result (io/read-graph graph-path)]
    (if (:error graph-result)
      {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}
      (if (:error input-result)
        {:exit-code 2 :message (str "Error reading ref: " (:error input-result))}
        (let [result (ext-ref/add-external-ref (:ok graph-result) (:ok input-result))]
          (if (:error result)
            {:exit-code 1 :message (str "Error:\n" (format-errors (:error result)))}
            (if (:dry-run options)
              {:exit-code 0 :message (str "OK: Validation passed (dry-run)\n  Would create " (:ref-id result))}
              (let [output-path (or (:output options) graph-path)
                    write-result (io/write-graph output-path (:ok result))]
                (if (:error write-result)
                  {:exit-code 2 :message (str "Error writing: " (:error write-result))}
                  {:exit-code 0
                   :message (io/format-edn
                             {:status :ok
                              :message "External reference added"
                              :ref-id (:ref-id result)
                              :graph-version (:version (:ok result))})})))))))))

(defn run-update [ref-id graph-path input-result options]
  (let [graph-result (io/read-graph graph-path)]
    (if (:error graph-result)
      {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}
      (if (:error input-result)
        {:exit-code 2 :message (str "Error reading result: " (:error input-result))}
        (let [result (ext-ref/update-external-ref (:ok graph-result) ref-id (:ok input-result))]
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
                              :message (str "Reference " ref-id " updated")
                              :graph-version (:version (:ok result))})})))))))))

(defn run [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (:add options)
    (if (empty? args)
      {:exit-code 2 :message (str "Error: No graph file\n\n" (usage))}
      (let [graph-path (first args)
            input-result (if (:stdin options)
                          (io/read-edn-stdin)
                          (if (> (count args) 1)
                            (io/read-edn (second args))
                            {:error "No ref file specified (use --stdin)"}))]
        (run-add graph-path input-result options)))

    (:update options)
    (if (empty? args)
      {:exit-code 2 :message (str "Error: No graph file\n\n" (usage))}
      (let [ref-id (:update options)
            graph-path (first args)
            input-result (if (:stdin options)
                          (io/read-edn-stdin)
                          (if (> (count args) 1)
                            (io/read-edn (second args))
                            {:error "No result file specified (use --stdin)"}))]
        (run-update ref-id graph-path input-result options)))

    :else
    {:exit-code 2 :message (str "Error: Specify --add or --update\n\n" (usage))}))
