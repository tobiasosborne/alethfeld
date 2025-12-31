(ns alethfeld.commands.init
  "CLI command for initializing a new semantic proof graph."
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [alethfeld.io :as io]
            [alethfeld.ops.init :as init]))

(def cli-options
  [["-t" "--theorem STATEMENT" "Theorem statement (LaTeX, required)"]
   ["-m" "--mode MODE" "Proof mode (strict-mathematics, formal-physics, algebraic-derivation)"
    :default :strict-mathematics
    :parse-fn keyword
    :validate [#{:strict-mathematics :formal-physics :algebraic-derivation}
               "Must be one of: strict-mathematics, formal-physics, algebraic-derivation"]]
   ["-g" "--graph-id ID" "Custom graph ID (generated if not provided)"]
   ["-T" "--max-tokens N" "Max context tokens"
    :default 100000
    :parse-fn #(Integer/parseInt %)]
   ["-h" "--help" "Show help for init command"]])

(defn usage []
  (->> ["Initialize a new semantic proof graph."
        ""
        "Usage: alethfeld init [options] <output.edn>"
        ""
        "Arguments:"
        "  output.edn    Path for the new graph file"
        ""
        "Options:"
        "  -t, --theorem STMT    Theorem statement in LaTeX (required)"
        "  -m, --mode MODE       Proof mode (default: strict-mathematics)"
        "  -g, --graph-id ID     Custom graph ID (auto-generated if omitted)"
        "  -T, --max-tokens N    Context budget limit (default: 100000)"
        "  -h, --help            Show this help"
        ""
        "Example:"
        "  alethfeld init proof.edn -t 'For all $n$, $n^2 \\geq 0$'"
        "  alethfeld init proof.edn -t 'Continuous composition' -m formal-physics"
        ""
        "Exit codes:"
        "  0 - Success"
        "  2 - Input error (missing required options)"]
       (str/join \newline)))

(defn run
  "Run the init command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No output file specified\n\n" (usage))}

    (not (:theorem options))
    {:exit-code 2 :message (str "Error: --theorem is required\n\n" (usage))}

    :else
    (let [output-path (first args)
          result (init/init-graph (:theorem options)
                                  :graph-id (:graph-id options)
                                  :proof-mode (:mode options)
                                  :max-tokens (:max-tokens options))]

      (if (:error result)
        {:exit-code 2
         :message (str "Error: " (str/join ", " (map :message (:error result))))}

        (let [write-result (io/write-graph output-path (:ok result))]
          (if (:error write-result)
            {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
            {:exit-code 0
             :message (io/format-edn
                       {:status :ok
                        :message (str "Created new graph: " output-path)
                        :graph-id (:graph-id (:ok result))
                        :theorem (subs (:theorem options) 0 (min 50 (count (:theorem options))))
                        :proof-mode (:mode options)})}))))))
