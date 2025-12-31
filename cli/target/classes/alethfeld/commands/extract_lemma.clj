(ns alethfeld.commands.extract-lemma
  "CLI command for extracting a verified subgraph as a lemma."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.extract-lemma :as extract-lemma]))

(def cli-options
  [["-n" "--name NAME" "Name for the extracted lemma (required)"]
   ["-N" "--nodes NODE-IDS" "Explicit node IDs to extract (comma-separated keywords, e.g., ':1-abc,:1-def')"]
   ["-d" "--dry-run" "Validate but don't write changes"]
   ["-o" "--output FILE" "Write to a different file"]
   ["-h" "--help" "Show help for extract-lemma command"]])

(defn usage []
  (->> ["Extract a verified subgraph as an independent lemma."
        ""
        "Usage: alethfeld extract-lemma [options] <graph.edn> <root-node-id>"
        ""
        "Arguments:"
        "  graph.edn       The graph file to modify"
        "  root-node-id    The root node of the extraction (e.g., ':1-abc123')"
        ""
        "Options:"
        "  -n, --name NAME     Name for the lemma (required, e.g., 'L1-fourier')"
        "  -N, --nodes IDS     Explicit node IDs to extract (comma-separated)"
        "                      If not provided, extracts root + all ancestors"
        "  -d, --dry-run       Validate but don't write changes"
        "  -o, --output F      Write to different file (default: overwrite input)"
        "  -h, --help          Show this help"
        ""
        "Extraction rules:"
        "  - All extracted nodes must have status :verified"
        "  - Only the root node may have external dependents"
        "  - Scope must be balanced (local-assumes have matching discharges)"
        ""
        "Example:"
        "  alethfeld extract-lemma proof.edn :1-abc123 -n L1-fourier"
        "  alethfeld extract-lemma proof.edn :1-abc123 -n L2-result -N :1-abc123,:1-def456"
        ""
        "Exit codes:"
        "  0 - Success"
        "  1 - Operation failed (precondition violation)"
        "  2 - Input error (file not found, parse error)"]
       (str/join \newline)))

(defn- parse-node-ids
  "Parse comma-separated keyword strings into a set of keywords.
   Input: ':1-abc,:1-def' -> #{:1-abc :1-def}"
  [s]
  (when s
    (->> (str/split s #",")
         (map str/trim)
         (map #(if (str/starts-with? % ":")
                 (edn/read-string %)
                 (keyword %)))
         set)))

(defn run
  "Run the extract-lemma command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (< (count args) 2)
    {:exit-code 2 :message (str "Error: Need graph file and root node ID\n\n" (usage))}

    (not (:name options))
    {:exit-code 2 :message (str "Error: --name is required\n\n" (usage))}

    :else
    (let [graph-path (first args)
          root-id-str (second args)
          root-id (if (str/starts-with? root-id-str ":")
                    (edn/read-string root-id-str)
                    (keyword root-id-str))
          lemma-name (:name options)
          node-ids (parse-node-ids (:nodes options))

          graph-result (io/read-graph graph-path)]

      (if (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (let [extract-result (if node-ids
                               (extract-lemma/extract-lemma (:ok graph-result) root-id lemma-name node-ids)
                               (extract-lemma/extract-lemma (:ok graph-result) root-id lemma-name))]

          (if (:error extract-result)
            {:exit-code 1
             :message (str "Error: Extraction failed\n"
                           (str/join \newline
                                     (map #(str "  [" (name (:type %)) "] " (:message %))
                                          (:error extract-result))))}

            (if (:dry-run options)
              {:exit-code 0
               :message (str "OK: Validation passed (dry-run)\n"
                             "  Would extract lemma '" lemma-name "'\n"
                             "  Root node: " root-id "\n"
                             "  Nodes: " (count (:extracted-nodes (:lemma extract-result))))}

              (let [output-path (or (:output options) graph-path)
                    write-result (io/write-graph output-path (:ok extract-result))]
                (if (:error write-result)
                  {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
                  {:exit-code 0
                   :message (io/format-edn
                             {:status :ok
                              :message (str "Lemma '" lemma-name "' extracted")
                              :lemma-id lemma-name
                              :root-node root-id
                              :extracted-nodes (count (:extracted-nodes (:lemma extract-result)))
                              :graph-version (:version (:ok extract-result))})})))))))))
