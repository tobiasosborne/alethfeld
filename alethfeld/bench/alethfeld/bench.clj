(ns alethfeld.bench
  "Performance benchmarks for Alethfeld graph operations.
   Run with: clojure -M:bench [quick|full]"
  (:require [criterium.core :as crit]
            [alethfeld.graph :as g]
            [alethfeld.validators :as v]
            [alethfeld.schema :as schema]
            [alethfeld.ops.extract-lemma :as extract-lemma]))

;; =============================================================================
;; Graph Generators
;; =============================================================================

(defn generate-linear-graph
  "Generate a linear chain graph with n nodes.
   Node i depends on node i-1."
  [n]
  (let [nodes (into {}
                    (for [i (range n)]
                      (let [id (keyword (str "1-" (format "%06x" i)))
                            deps (if (zero? i)
                                   #{}
                                   #{(keyword (str "1-" (format "%06x" (dec i))))})]
                        [id {:id id
                             :type (if (zero? i) :assumption :claim)
                             :statement (str "Statement " i)
                             :content-hash (format "%016x" i)
                             :dependencies deps
                             :scope #{}
                             :justification (if (zero? i) :assumption :modus-ponens)
                             :status :verified
                             :taint :clean
                             :depth 1
                             :parent nil
                             :display-order i
                             :provenance {:created-at "2024-01-01T00:00:00"
                                          :created-by :prover
                                          :round 1
                                          :revision-of nil}}])))]
    {:graph-id "bench-linear"
     :version 1
     :theorem {:id :theorem
               :statement "Benchmark theorem"
               :content-hash "fedcba9876543210"}
     :nodes nodes
     :symbols {}
     :external-refs {}
     :lemmas {}
     :obligations []
     :archived-nodes {}
     :metadata {:created-at "2024-01-01T00:00:00"
                :last-modified "2024-01-01T00:00:00"
                :proof-mode :strict-mathematics
                :iteration-counts {:verification {}
                                   :expansion {}
                                   :strategy 0}
                :context-budget {:max-tokens 100000
                                 :current-estimate 1000}}}))

(defn generate-binary-tree-graph
  "Generate a balanced binary tree graph with approximately n nodes.
   Each node (except leaves) has two children depending on it."
  [n]
  (let [;; Build tree level by level
        depth (int (Math/ceil (/ (Math/log (inc n)) (Math/log 2))))
        nodes (atom {})
        counter (atom 0)

        make-node (fn [level parent-id]
                    (let [i @counter
                          id (keyword (str "1-" (format "%06x" i)))
                          deps (if parent-id #{parent-id} #{})]
                      (swap! counter inc)
                      (swap! nodes assoc id
                             {:id id
                              :type (if parent-id :claim :assumption)
                              :statement (str "Statement " i)
                              :content-hash (format "%016x" i)
                              :dependencies deps
                              :scope #{}
                              :justification (if parent-id :modus-ponens :assumption)
                              :status :verified
                              :taint :clean
                              :depth level
                              :parent parent-id
                              :display-order i
                              :provenance {:created-at "2024-01-01T00:00:00"
                                           :created-by :prover
                                           :round 1
                                           :revision-of nil}})
                      id))]

    ;; Build tree recursively
    (letfn [(build-tree [level parent-id]
              (when (and (< @counter n) (<= level depth))
                (let [id (make-node level parent-id)]
                  (build-tree (inc level) id)
                  (build-tree (inc level) id))))]
      (build-tree 0 nil))

    {:graph-id "bench-tree"
     :version 1
     :theorem {:id :theorem
               :statement "Benchmark theorem"
               :content-hash "fedcba9876543210"}
     :nodes @nodes
     :symbols {}
     :external-refs {}
     :lemmas {}
     :obligations []
     :archived-nodes {}
     :metadata {:created-at "2024-01-01T00:00:00"
                :last-modified "2024-01-01T00:00:00"
                :proof-mode :strict-mathematics
                :iteration-counts {:verification {}
                                   :expansion {}
                                   :strategy 0}
                :context-budget {:max-tokens 100000
                                 :current-estimate 1000}}}))

(defn generate-diamond-graph
  "Generate a graph with diamond patterns.
   Creates n/4 diamonds connected in sequence."
  [n]
  (let [num-diamonds (max 1 (quot n 4))
        nodes (atom {})
        counter (atom 0)

        make-node (fn [deps]
                    (let [i @counter
                          id (keyword (str "1-" (format "%06x" i)))]
                      (swap! counter inc)
                      (swap! nodes assoc id
                             {:id id
                              :type (if (empty? deps) :assumption :claim)
                              :statement (str "Statement " i)
                              :content-hash (format "%016x" i)
                              :dependencies (set deps)
                              :scope #{}
                              :justification (if (empty? deps) :assumption :modus-ponens)
                              :status :verified
                              :taint :clean
                              :depth 1
                              :parent nil
                              :display-order i
                              :provenance {:created-at "2024-01-01T00:00:00"
                                           :created-by :prover
                                           :round 1
                                           :revision-of nil}})
                      id))]

    ;; Build diamond chain: A -> B,C -> D -> E,F -> G -> ...
    (loop [prev-id nil
           remaining num-diamonds]
      (when (pos? remaining)
        (let [top (make-node (if prev-id [prev-id] []))
              left (make-node [top])
              right (make-node [top])
              bottom (make-node [left right])]
          (recur bottom (dec remaining)))))

    {:graph-id "bench-diamond"
     :version 1
     :theorem {:id :theorem
               :statement "Benchmark theorem"
               :content-hash "fedcba9876543210"}
     :nodes @nodes
     :symbols {}
     :external-refs {}
     :lemmas {}
     :obligations []
     :archived-nodes {}
     :metadata {:created-at "2024-01-01T00:00:00"
                :last-modified "2024-01-01T00:00:00"
                :proof-mode :strict-mathematics
                :iteration-counts {:verification {}
                                   :expansion {}
                                   :strategy 0}
                :context-budget {:max-tokens 100000
                                 :current-estimate 1000}}}))

;; =============================================================================
;; Benchmark Suites
;; =============================================================================

(defmacro run-bench
  "Run benchmark with either quick-bench or bench based on quick? flag."
  [quick? expr]
  `(if ~quick?
     (crit/quick-bench ~expr)
     (crit/bench ~expr)))

(defn bench-get-ancestors
  "Benchmark get-ancestors on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking get-ancestors ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)
          last-node (keyword (str "1-" (format "%06x" (dec n))))]
      (println (str "\nLinear graph (" n " nodes), query last node:"))
      (if quick?
        (crit/quick-bench (g/get-ancestors graph last-node))
        (crit/bench (g/get-ancestors graph last-node))))))

(defn bench-get-descendants
  "Benchmark get-descendants on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking get-descendants ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)
          first-node :1-000000]
      (println (str "\nLinear graph (" n " nodes), query first node:"))
      (if quick?
        (crit/quick-bench (g/get-descendants graph first-node))
        (crit/bench (g/get-descendants graph first-node))))))

(defn bench-topological-sort
  "Benchmark topological-sort on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking topological-sort ===")
  (doseq [[name gen-fn] [["linear" generate-linear-graph]
                          ["tree" generate-binary-tree-graph]
                          ["diamond" generate-diamond-graph]]]
    (doseq [n [50 100 500]]
      (let [graph (gen-fn n)
            actual-size (count (:nodes graph))]
        (println (str "\n" (clojure.string/capitalize name) " graph (~" n " nodes, actual " actual-size "):"))
        (if quick?
          (crit/quick-bench (g/topological-sort graph))
          (crit/bench (g/topological-sort graph)))))))

(defn bench-topological-sort-partial
  "Benchmark partial topological sort (single target)."
  [quick?]
  (println "\n=== Benchmarking topological-sort (partial, single target) ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)
          mid-node (keyword (str "1-" (format "%06x" (quot n 2))))]
      (println (str "\nLinear graph (" n " nodes), sort for middle node:"))
      (if quick?
        (crit/quick-bench (g/topological-sort graph :targets #{mid-node}))
        (crit/bench (g/topological-sort graph :targets #{mid-node}))))))

(defn bench-compute-all-scopes
  "Benchmark compute-all-scopes on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking compute-all-scopes ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)]
      (println (str "\nLinear graph (" n " nodes):"))
      (if quick?
        (crit/quick-bench (g/compute-all-scopes graph))
        (crit/bench (g/compute-all-scopes graph))))))

(defn bench-validate-semantics
  "Benchmark semantic validation on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking validate-semantics ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)]
      (println (str "\nLinear graph (" n " nodes):"))
      (if quick?
        (crit/quick-bench (v/validate-semantics graph))
        (crit/bench (v/validate-semantics graph))))))

(defn bench-validate-schema
  "Benchmark schema validation on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking validate-schema ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)]
      (println (str "\nLinear graph (" n " nodes):"))
      (if quick?
        (crit/quick-bench (schema/validate-schema graph))
        (crit/bench (schema/validate-schema graph))))))

(defn bench-find-cycle
  "Benchmark cycle detection on different graph sizes."
  [quick?]
  (println "\n=== Benchmarking find-cycle ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-diamond-graph n)
          actual-size (count (:nodes graph))]
      (println (str "\nDiamond graph (~" n " nodes, actual " actual-size "):"))
      (if quick?
        (crit/quick-bench (v/find-cycle graph))
        (crit/bench (v/find-cycle graph))))))

;; =============================================================================
;; Main Entry Point
;; =============================================================================

(defn run-all-benchmarks
  "Run all benchmarks."
  [quick?]
  (println "===============================================")
  (println "  Alethfeld Performance Benchmarks")
  (println (str "  Mode: " (if quick? "Quick" "Full")))
  (println "===============================================")

  (bench-get-ancestors quick?)
  (bench-get-descendants quick?)
  (bench-topological-sort quick?)
  (bench-topological-sort-partial quick?)
  (bench-compute-all-scopes quick?)
  (bench-validate-semantics quick?)
  (bench-validate-schema quick?)
  (bench-find-cycle quick?)

  (println "\n===============================================")
  (println "  Benchmarks Complete")
  (println "==============================================="))

(defn -main
  "Run benchmarks. Args: 'quick' for quick mode, 'full' for full mode (default)."
  [& args]
  (let [mode (first args)
        quick? (= "quick" mode)]
    (run-all-benchmarks quick?)))
