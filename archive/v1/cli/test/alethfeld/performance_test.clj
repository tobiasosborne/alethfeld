(ns alethfeld.performance-test
  "Performance regression tests with timing gates for graph operations.

   These tests guard against performance degradation by:
   1. Setting maximum time budgets for operations
   2. Verifying near-linear scaling (detecting O(n²) regressions)

   Run with: clojure -M:test"
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.graph :as g]
            [alethfeld.validators :as v]))

;; =============================================================================
;; Graph Generators (same as bench.clj for consistency)
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
    {:graph-id "perf-linear"
     :version 1
     :theorem {:id :theorem
               :statement "Performance test theorem"
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

    {:graph-id "perf-diamond"
     :version 1
     :theorem {:id :theorem
               :statement "Performance test theorem"
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

(defn generate-wide-graph
  "Generate a wide graph: one root with n-1 direct children.
   Good for testing descendant queries."
  [n]
  (let [root-id :1-000000
        nodes (into {root-id {:id root-id
                              :type :assumption
                              :statement "Root"
                              :content-hash "0000000000000000"
                              :dependencies #{}
                              :scope #{}
                              :justification :assumption
                              :status :verified
                              :taint :clean
                              :depth 0
                              :parent nil
                              :display-order 0
                              :provenance {:created-at "2024-01-01T00:00:00"
                                           :created-by :prover
                                           :round 1
                                           :revision-of nil}}}
                    (for [i (range 1 n)]
                      (let [id (keyword (str "1-" (format "%06x" i)))]
                        [id {:id id
                             :type :claim
                             :statement (str "Child " i)
                             :content-hash (format "%016x" i)
                             :dependencies #{root-id}
                             :scope #{}
                             :justification :modus-ponens
                             :status :verified
                             :taint :clean
                             :depth 1
                             :parent nil
                             :display-order i
                             :provenance {:created-at "2024-01-01T00:00:00"
                                          :created-by :prover
                                          :round 1
                                          :revision-of nil}}])))]
    {:graph-id "perf-wide"
     :version 1
     :theorem {:id :theorem
               :statement "Performance test theorem"
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

;; =============================================================================
;; Timing Utilities
;; =============================================================================

(defmacro time-ms
  "Execute body and return [result elapsed-ms]."
  [& body]
  `(let [start# (System/nanoTime)
         result# (do ~@body)
         elapsed# (/ (- (System/nanoTime) start#) 1000000.0)]
     [result# elapsed#]))

(defn median
  "Calculate median of a sequence of numbers."
  [xs]
  (let [sorted (sort xs)
        n (count sorted)]
    (if (odd? n)
      (nth sorted (quot n 2))
      (/ (+ (nth sorted (dec (quot n 2)))
            (nth sorted (quot n 2)))
         2.0))))

(defn run-timed
  "Run f multiple times and return median elapsed time in ms.
   Includes warmup iterations to allow JIT compilation."
  [f iterations]
  ;; Warmup: run twice to trigger JIT
  (dotimes [_ 2] (f))
  (let [times (for [_ (range iterations)]
                (second (time-ms (f))))]
    (median times)))

(defn run-warmed
  "Run f once after warmup and return [result elapsed-ms]."
  [f]
  ;; Warmup
  (dotimes [_ 3] (f))
  (time-ms (f)))

;; =============================================================================
;; Scaling Analysis
;; =============================================================================

(defn check-scaling
  "Check if operation scales within expected bounds.
   Returns true if time ratio is within acceptable bounds.

   For O(n) algorithm: time(4n) / time(n) ≈ 4
   For O(n²) algorithm: time(4n) / time(n) ≈ 16
   For O(n³) algorithm: time(4n) / time(n) ≈ 64

   The max-ratio parameter sets the acceptable upper bound.
   Use 5.0 to guard O(n) against regression to O(n²).
   Use 20.0 to guard O(n²) against regression to O(n³)."
  [time-small time-large max-ratio]
  (let [time-ratio (/ time-large (max 0.001 time-small))]
    (<= time-ratio max-ratio)))

(defn check-linear-scaling
  "Check if operation scales linearly (O(n)).
   Catches regression to O(n²) or worse."
  [time-small time-large size-ratio max-multiplier]
  (check-scaling time-small time-large (* max-multiplier size-ratio)))

(defn check-quadratic-scaling
  "Check if operation scales at most quadratically (O(n²)).
   Catches regression to O(n³) or worse.
   Some operations are inherently O(n²) due to algorithm design."
  [time-small time-large size-ratio]
  ;; For 4x size increase, O(n²) gives 16x time increase
  ;; Allow 25x to account for variance while catching O(n³) (would be 64x)
  (check-scaling time-small time-large (* 25.0 1.0)))

;; =============================================================================
;; Performance Tests with Timing Gates
;; =============================================================================

(deftest topological-sort-timing-test
  (testing "topological-sort completes within time budget"
    (let [graph (generate-linear-graph 1000)
          [_ elapsed] (run-warmed #(g/topological-sort graph))]
      ;; 1000 nodes should sort in under 300ms (after JIT warmup)
      (is (< elapsed 300)
          (format "topological-sort took %.2fms, expected <300ms" elapsed))))

  (testing "topological-sort scaling does not regress beyond O(n²)"
    ;; NOTE: Current implementation has O(n²) complexity due to inner filter loop.
    ;; This test guards against regression to O(n³) or worse.
    (let [small-graph (generate-linear-graph 200)
          large-graph (generate-linear-graph 800)
          time-small (run-timed #(g/topological-sort small-graph) 5)
          time-large (run-timed #(g/topological-sort large-graph) 5)]
      (is (check-quadratic-scaling time-small time-large 4.0)
          (format "topological-sort scaling regression: %.2fms (200) vs %.2fms (800), ratio=%.1fx (expected <25x for O(n²))"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest partial-topological-sort-timing-test
  (testing "partial topological-sort is faster than full sort"
    (let [graph (generate-linear-graph 1000)
          mid-node (keyword (str "1-" (format "%06x" 500)))
          time-full (run-timed #(g/topological-sort graph) 5)
          time-partial (run-timed #(g/topological-sort graph nil :targets #{mid-node}) 5)]
      ;; Partial sort for middle node should be significantly faster
      ;; (only needs to sort ~500 nodes instead of 1000)
      (is (< time-partial (* 0.75 time-full))
          (format "partial sort (%.2fms) not faster than full (%.2fms)"
                  time-partial time-full)))))

(deftest cycle-detection-timing-test
  (testing "find-cycle completes within time budget"
    (let [graph (generate-diamond-graph 1000)
          [_ elapsed] (run-warmed #(v/find-cycle graph))]
      ;; ~1000 nodes should check in under 100ms (after warmup)
      (is (< elapsed 100)
          (format "find-cycle took %.2fms, expected <100ms" elapsed))))

  (testing "find-cycle scales linearly"
    (let [small-graph (generate-diamond-graph 200)
          large-graph (generate-diamond-graph 800)
          time-small (run-timed #(v/find-cycle small-graph) 5)
          time-large (run-timed #(v/find-cycle large-graph) 5)]
      (is (check-linear-scaling time-small time-large 4.0 3.0)
          (format "find-cycle scaling suspicious: %.2fms (200) vs %.2fms (800), ratio=%.1fx"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest taint-propagation-timing-test
  (testing "recompute-all-taints completes within time budget"
    (let [graph (generate-diamond-graph 500)
          [_ elapsed] (run-warmed #(g/recompute-all-taints graph))]
      ;; ~500 nodes should propagate in under 300ms (after warmup)
      (is (< elapsed 300)
          (format "recompute-all-taints took %.2fms, expected <300ms" elapsed))))

  (testing "recompute-all-taints scaling does not regress beyond O(n²)"
    ;; NOTE: Inherits O(n²) from topological-sort.
    ;; This test guards against regression to O(n³) or worse.
    (let [small-graph (generate-diamond-graph 200)
          large-graph (generate-diamond-graph 800)
          time-small (run-timed #(g/recompute-all-taints small-graph) 5)
          time-large (run-timed #(g/recompute-all-taints large-graph) 5)]
      (is (check-quadratic-scaling time-small time-large 4.0)
          (format "recompute-all-taints scaling regression: %.2fms (200) vs %.2fms (800), ratio=%.1fx (expected <25x for O(n²))"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest get-ancestors-timing-test
  (testing "get-ancestors completes within time budget"
    (let [graph (generate-linear-graph 1000)
          last-node (keyword (str "1-" (format "%06x" 999)))
          [result elapsed] (run-warmed #(g/get-ancestors graph last-node))]
      ;; Querying ancestors of last node in 1000-node chain
      (is (< elapsed 100)
          (format "get-ancestors took %.2fms, expected <100ms" elapsed))
      ;; Verify result correctness
      (is (= 999 (count result)))))

  (testing "get-ancestors scales linearly"
    (let [small-graph (generate-linear-graph 200)
          large-graph (generate-linear-graph 800)
          small-last (keyword (str "1-" (format "%06x" 199)))
          large-last (keyword (str "1-" (format "%06x" 799)))
          time-small (run-timed #(g/get-ancestors small-graph small-last) 5)
          time-large (run-timed #(g/get-ancestors large-graph large-last) 5)]
      (is (check-linear-scaling time-small time-large 4.0 3.0)
          (format "get-ancestors scaling suspicious: %.2fms (200) vs %.2fms (800), ratio=%.1fx"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest get-descendants-timing-test
  (testing "get-descendants completes within time budget"
    (let [graph (generate-wide-graph 1000)
          [result elapsed] (run-warmed #(g/get-descendants graph :1-000000))]
      ;; Querying descendants of root in wide graph
      (is (< elapsed 100)
          (format "get-descendants took %.2fms, expected <100ms" elapsed))
      ;; Verify result correctness
      (is (= 999 (count result)))))

  (testing "get-descendants scales linearly"
    (let [small-graph (generate-wide-graph 200)
          large-graph (generate-wide-graph 800)
          time-small (run-timed #(g/get-descendants small-graph :1-000000) 5)
          time-large (run-timed #(g/get-descendants large-graph :1-000000) 5)]
      (is (check-linear-scaling time-small time-large 4.0 3.0)
          (format "get-descendants scaling suspicious: %.2fms (200) vs %.2fms (800), ratio=%.1fx"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest compute-all-scopes-timing-test
  (testing "compute-all-scopes completes within time budget"
    (let [graph (generate-diamond-graph 500)
          [_ elapsed] (run-warmed #(g/compute-all-scopes graph))]
      ;; ~500 nodes should compute scopes in under 500ms
      (is (< elapsed 500)
          (format "compute-all-scopes took %.2fms, expected <500ms" elapsed))))

  (testing "compute-all-scopes scaling does not regress beyond O(n²)"
    ;; NOTE: Inherits O(n²) from topological-sort.
    ;; This test guards against regression to O(n³) or worse.
    (let [small-graph (generate-diamond-graph 200)
          large-graph (generate-diamond-graph 800)
          time-small (run-timed #(g/compute-all-scopes small-graph) 5)
          time-large (run-timed #(g/compute-all-scopes large-graph) 5)]
      (is (check-quadratic-scaling time-small time-large 4.0)
          (format "compute-all-scopes scaling regression: %.2fms (200) vs %.2fms (800), ratio=%.1fx (expected <25x for O(n²))"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

(deftest validate-semantics-timing-test
  (testing "validate-semantics completes within time budget"
    (let [graph (generate-diamond-graph 400)
          [result elapsed] (run-warmed #(v/validate-semantics graph))]
      ;; Full validation of ~400 nodes should complete in under 500ms
      (is (< elapsed 500)
          (format "validate-semantics took %.2fms, expected <500ms" elapsed))
      ;; Verify result
      (is (:valid result))))

  (testing "validate-semantics scaling does not regress beyond O(n²)"
    ;; NOTE: Dominated by O(n²) operations (topological-sort, scope computation).
    ;; This test guards against regression to O(n³) or worse.
    (let [small-graph (generate-diamond-graph 100)
          large-graph (generate-diamond-graph 400)
          time-small (run-timed #(v/validate-semantics small-graph) 3)
          time-large (run-timed #(v/validate-semantics large-graph) 3)]
      (is (check-quadratic-scaling time-small time-large 4.0)
          (format "validate-semantics scaling regression: %.2fms (100) vs %.2fms (400), ratio=%.1fx (expected <25x for O(n²))"
                  time-small time-large (/ time-large (max 0.001 time-small)))))))

;; =============================================================================
;; Stress Tests for Edge Cases
;; =============================================================================

(deftest stress-deeply-nested-graph-test
  (testing "Operations handle deeply nested graphs efficiently"
    (let [;; 500-node deep linear chain (pathological case for recursion)
          graph (generate-linear-graph 500)
          last-node (keyword (str "1-" (format "%06x" 499)))]
      ;; These should not blow the stack
      (let [[ancestors elapsed-anc] (run-warmed #(g/get-ancestors graph last-node))]
        (is (= 499 (count ancestors)))
        (is (< elapsed-anc 100) "get-ancestors on deep graph too slow"))
      (let [[sorted elapsed-sort] (run-warmed #(g/topological-sort graph))]
        (is (= 500 (count sorted)))
        (is (< elapsed-sort 100) "topological-sort on deep graph too slow")))))

(deftest stress-wide-fanout-graph-test
  (testing "Operations handle wide fanout efficiently"
    (let [;; 1000 children of single root
          graph (generate-wide-graph 1001)
          root :1-000000]
      (let [[descendants elapsed] (run-warmed #(g/get-descendants graph root))]
        (is (= 1000 (count descendants)))
        (is (< elapsed 100) "get-descendants on wide graph too slow")))))
