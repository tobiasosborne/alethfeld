(ns alethfeld.commands.stats
  "CLI command for displaying semantic proof graph statistics."
  (:require [clojure.string :as str]
            [clojure.data.json :as json]
            [alethfeld.io :as io]
            [alethfeld.graph :as graph]))

(def cli-options
  [["-j" "--json" "Output as JSON instead of EDN"]
   ["-q" "--quiet" "Minimal output (counts only)"]
   ["-h" "--help" "Show help for stats command"]])

(defn usage []
  (->> ["Display statistics for a semantic proof graph."
        ""
        "Usage: alethfeld stats [options] <graph.edn>"
        ""
        "Arguments:"
        "  graph.edn    The graph file to analyze"
        ""
        "Options:"
        "  -j, --json     Output as JSON format"
        "  -q, --quiet    Minimal output (counts only)"
        "  -h, --help     Show this help"
        ""
        "Output includes:"
        "  - Node counts by type and status"
        "  - Taint summary"
        "  - Dependency statistics"
        "  - Context budget usage"
        ""
        "Exit codes:"
        "  0 - Success"
        "  2 - Input error (file not found, parse error)"]
       (str/join \newline)))

(defn- count-by
  "Count nodes grouped by a key function."
  [nodes key-fn]
  (->> nodes
       (map (fn [[_ node]] (key-fn node)))
       frequencies))

(defn- compute-stats
  "Compute statistics for a graph."
  [g]
  (let [nodes (:nodes g)
        node-count (count nodes)
        archived-count (count (:archived-nodes g))

        ;; Node counts by type
        type-counts (count-by nodes :type)

        ;; Node counts by status
        status-counts (count-by nodes :status)

        ;; Taint counts
        taint-counts (count-by nodes :taint)

        ;; Dependency statistics
        dep-counts (map (fn [[_ node]] (count (:dependencies node))) nodes)
        avg-deps (if (empty? dep-counts) 0 (/ (reduce + dep-counts) (count dep-counts)))
        max-deps (if (empty? dep-counts) 0 (apply max dep-counts))

        ;; Depth statistics
        depths (map (fn [[_ node]] (:depth node)) nodes)
        max-depth (if (empty? depths) 0 (apply max depths))

        ;; External refs and lemmas
        external-ref-count (count (:external-refs g))
        lemma-count (count (:lemmas g))
        obligation-count (count (:obligations g))

        ;; Context budget
        budget (get-in g [:metadata :context-budget])
        estimated-tokens (:current-estimate budget)
        max-tokens (:max-tokens budget)
        budget-pct (if (zero? max-tokens) 0 (* 100.0 (/ estimated-tokens max-tokens)))]

    {:graph-id (:graph-id g)
     :version (:version g)
     :proof-mode (get-in g [:metadata :proof-mode])

     :nodes {:total node-count
             :archived archived-count
             :by-type type-counts
             :by-status status-counts}

     :taint {:counts taint-counts
             :clean-count (get taint-counts :clean 0)
             :tainted-count (+ (get taint-counts :tainted 0)
                               (get taint-counts :self-admitted 0))}

     :structure {:max-depth max-depth
                 :avg-dependencies (double avg-deps)
                 :max-dependencies max-deps}

     :references {:external-refs external-ref-count
                  :lemmas lemma-count
                  :obligations obligation-count}

     :context-budget {:estimated-tokens estimated-tokens
                      :max-tokens max-tokens
                      :usage-percent (double budget-pct)}}))

(defn- format-quiet
  "Format minimal output."
  [stats]
  (str (get-in stats [:nodes :total]) " nodes, "
       (get-in stats [:taint :clean-count]) " clean, "
       (get-in stats [:taint :tainted-count]) " tainted"))

(defn run
  "Run the stats command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No graph file specified\n\n" (usage))}

    :else
    (let [graph-path (first args)
          graph-result (io/read-graph graph-path)]

      (if (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (let [stats (compute-stats (:ok graph-result))]
          (cond
            (:quiet options)
            {:exit-code 0 :message (format-quiet stats)}

            (:json options)
            {:exit-code 0 :message (json/write-str stats)}

            :else
            {:exit-code 0 :message (io/format-edn stats)}))))))
