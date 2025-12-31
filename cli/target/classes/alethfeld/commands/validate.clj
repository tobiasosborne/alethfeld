(ns alethfeld.commands.validate
  "Validate command for semantic proof graphs."
  (:require [clojure.string :as str]
            [clojure.pprint :as pprint]
            [alethfeld.io :as io]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as validators]))

(def cli-options
  [["-v" "--verbose" "Show detailed error information"]
   ["-q" "--quiet" "Only show pass/fail, no details"]
   ["-s" "--schema-only" "Only run schema validation, skip semantic checks"]
   ["-h" "--help" "Show help for validate command"]])

(defn usage []
  (->> ["Validate Alethfeld semantic proof graph EDN files."
        ""
        "Usage: alethfeld validate [options] <file.edn>"
        ""
        "Options:"
        "  -v, --verbose      Show detailed error information"
        "  -q, --quiet        Only show pass/fail, no details"
        "  -s, --schema-only  Only run schema validation, skip semantic checks"
        "  -h, --help         Show this help message"
        ""
        "Exit codes:"
        "  0 - Validation successful"
        "  1 - Validation failed"
        "  2 - File error (not found, parse error, etc.)"]
       (str/join \newline)))

(defn format-schema-errors [errors verbose?]
  (if verbose?
    (with-out-str (pprint/pprint errors))
    (str "Schema validation failed with " (count (flatten (vals errors))) " error(s)")))

(defn format-semantic-errors [errors verbose?]
  (if verbose?
    (->> errors
         (map (fn [e]
                (str "  [" (name (:type e)) "] " (:message e))))
         (str/join \newline))
    (str (count errors) " semantic error(s) found")))

(defn validate-file
  "Validate a single EDN file.
   Returns {:exit-code N :message S}."
  [path {:keys [verbose quiet schema-only]}]
  (let [file-result (io/read-graph path)]
    (cond
      ;; File read error
      (:error file-result)
      {:exit-code 2 :message (:error file-result)}

      ;; Schema validation
      :else
      (let [graph (:ok file-result)
            schema-result (schema/validate-schema graph)]
        (cond
          ;; Schema failed
          (not (:valid schema-result))
          {:exit-code 1
           :message (if quiet
                      "FAIL: Schema validation failed"
                      (str "FAIL: Schema validation\n"
                           (format-schema-errors (:errors schema-result) verbose)))}

          ;; Schema-only mode - success
          schema-only
          {:exit-code 0
           :message (when-not quiet "OK: Schema validation passed")}

          ;; Full validation - run semantic checks
          :else
          (let [semantic-result (validators/validate-semantics graph)]
            (if (:valid semantic-result)
              {:exit-code 0
               :message (when-not quiet "OK: All validations passed")}
              {:exit-code 1
               :message (if quiet
                          "FAIL: Semantic validation failed"
                          (str "FAIL: Semantic validation\n"
                               (format-semantic-errors (:errors semantic-result) verbose)))})))))))

(defn run
  "Run the validate command.
   Returns {:exit-code N :message S}."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No input file specified\n\n" (usage))}

    :else
    (validate-file (first args) options)))
