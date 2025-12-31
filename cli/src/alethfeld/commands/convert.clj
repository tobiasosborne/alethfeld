(ns alethfeld.commands.convert
  "CLI command for converting legacy proof format to v4 schema."
  (:require [clojure.string :as str]
            [alethfeld.io :as io]
            [alethfeld.convert :as convert]
            [alethfeld.schema :as schema]))

(def cli-options
  [["-o" "--output FILE" "Output file (default: <input>-v4.edn)"]
   ["-f" "--force" "Overwrite output file if exists"]
   ["-v" "--validate" "Validate converted graph against schema"]
   ["-h" "--help" "Show help for convert command"]])

(defn usage []
  (->> ["Convert legacy proof format to v4 semantic graph schema."
        ""
        "Usage: alethfeld convert [options] <input.edn>"
        ""
        "Arguments:"
        "  input.edn    Legacy proof file to convert"
        ""
        "Options:"
        "  -o, --output FILE   Output file (default: <input>-v4.edn)"
        "  -f, --force         Overwrite output if exists"
        "  -v, --validate      Validate converted graph"
        "  -h, --help          Show this help"
        ""
        "Legacy format:"
        "  {:meta {...}"
        "   :theorem \"...\""
        "   :assumptions [{:id :A1 :statement \"...\"}]"
        "   :definitions [{:id :D1 :name \"...\" :statement \"...\"}]"
        "   :steps [{:id :<1>1 :claim \"...\" :using [...] :substeps [...]}]}"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Validation failed"
        "  2 - Input error"]
       (str/join \newline)))

(defn- default-output-path [input-path]
  (let [base (if (str/ends-with? input-path ".edn")
               (subs input-path 0 (- (count input-path) 4))
               input-path)]
    (str base "-v4.edn")))

(defn run
  "Run the convert command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No input file specified\n\n" (usage))}

    :else
    (let [input-path (first args)
          output-path (or (:output options) (default-output-path input-path))
          result (convert/convert-file input-path)]

      (cond
        (:error result)
        {:exit-code 2 :message (str "Error: " (:error result))}

        (:already-v4 result)
        {:exit-code 0
         :message (io/format-edn
                   {:status :ok
                    :message "File is already in v4 format"
                    :input input-path})}

        :else
        (let [graph (:ok result)
              ;; Optionally validate
              validation (when (:validate options)
                           (schema/validate-schema graph))]

          (if (and (:validate options) (not (:valid validation)))
            {:exit-code 1
             :message (str "Validation failed:\n"
                           (io/format-edn (:errors validation)))}

            ;; Check if output exists
            (if (and (.exists (clojure.java.io/file output-path))
                     (not (:force options)))
              {:exit-code 2
               :message (str "Error: Output file exists: " output-path
                             "\nUse --force to overwrite")}

              ;; Write output
              (let [write-result (io/write-graph output-path graph)]
                (if (:error write-result)
                  {:exit-code 2 :message (str "Error writing: " (:error write-result))}
                  {:exit-code 0
                   :message (io/format-edn
                             {:status :ok
                              :message "Converted successfully"
                              :input input-path
                              :output output-path
                              :nodes (count (:nodes graph))
                              :validated (:validate options)})})))))))))
