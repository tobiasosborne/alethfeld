(ns validate-graph.main
  "CLI entry point for validating semantic proof graphs."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.tools.logging :as log]
            [clojure.string :as str]
            [validate-graph.schema :as schema]
            [validate-graph.validators :as validators])
  (:gen-class))

(def cli-options
  [["-v" "--verbose" "Show detailed error information"]
   ["-q" "--quiet" "Only show pass/fail, no details"]
   ["-s" "--schema-only" "Only run schema validation, skip semantic checks"]
   ["-h" "--help" "Show this help message"]])

(defn usage [options-summary]
  (->> ["Validate Alethfeld semantic proof graph EDN files."
        ""
        "Usage: validate-graph [options] <file.edn>"
        ""
        "Options:"
        options-summary
        ""
        "Exit codes:"
        "  0 - Validation successful"
        "  1 - Validation failed"
        "  2 - File error (not found, parse error, etc.)"]
       (str/join \newline)))

(defn error-msg [errors]
  (str "Error:\n" (str/join \newline errors)))

(defn read-edn-file [path]
  (try
    (let [content (slurp path)]
      (if (str/blank? content)
        {:error (str "Empty file: " path)}
        (let [parsed (edn/read-string content)]
          (if (nil? parsed)
            {:error (str "Failed to parse EDN: file contains nil or is invalid")}
            {:ok parsed}))))
    (catch java.io.FileNotFoundException _
      {:error (str "File not found: " path)})
    (catch Exception e
      {:error (str "Failed to parse EDN: " (.getMessage e))})))

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

(defn validate-file [path {:keys [verbose quiet schema-only]}]
  (log/debug "Starting validation of" path)
  (let [file-result (read-edn-file path)]
    (cond
      ;; File read error
      (:error file-result)
      (do
        (log/error "File read error:" (:error file-result))
        {:exit-code 2 :message (:error file-result)})

      ;; Schema validation
      :else
      (let [graph (:ok file-result)
            _ (log/debug "File parsed successfully, running schema validation")
            schema-result (schema/validate-schema graph)]
        (cond
          ;; Schema failed
          (not (:valid schema-result))
          (do
            (log/info "Schema validation failed with" (count (flatten (vals (:errors schema-result)))) "errors")
            {:exit-code 1
             :message (if quiet
                        "FAIL: Schema validation failed"
                        (str "FAIL: Schema validation\n"
                             (format-schema-errors (:errors schema-result) verbose)))})

          ;; Schema-only mode - success
          schema-only
          (do
            (log/debug "Schema validation passed (schema-only mode)")
            {:exit-code 0
             :message (when-not quiet "OK: Schema validation passed")})

          ;; Full validation - run semantic checks
          :else
          (let [_ (log/debug "Schema validation passed, running semantic validation")
                semantic-result (validators/validate-semantics graph)]
            (if (:valid semantic-result)
              (do
                (log/debug "All validations passed")
                {:exit-code 0
                 :message (when-not quiet "OK: All validations passed")})
              (do
                (log/info "Semantic validation failed with" (count (:errors semantic-result)) "errors")
                {:exit-code 1
                 :message (if quiet
                            "FAIL: Semantic validation failed"
                            (str "FAIL: Semantic validation\n"
                                 (format-semantic-errors (:errors semantic-result) verbose)))}))))))))

(defn -main [& args]
  (let [{:keys [options arguments errors summary]} (parse-opts args cli-options)]
    (cond
      (:help options)
      (do (println (usage summary))
          (System/exit 0))

      errors
      (do (println (error-msg errors))
          (System/exit 2))

      (empty? arguments)
      (do (println "Error: No input file specified")
          (println (usage summary))
          (System/exit 2))

      :else
      (let [result (validate-file (first arguments) options)]
        (when (:message result)
          (println (:message result)))
        (System/exit (:exit-code result))))))
