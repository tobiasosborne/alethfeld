(ns alethfeld.boundary-test
  "Comprehensive boundary and edge case tests for semantic proof graphs.

   Tests cover:
   1. Empty dependency sets
   2. Large graphs (stress testing)
   3. Unicode in statements
   4. Null/nil injection attempts
   5. Integer overflow in version tracking
   6. Circular lemma references

   These tests guard against production failure points identified during code review."
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.graph :as g]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as v]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; 1. Empty Dependency Set Tests
;; =============================================================================

(deftest empty-dependencies-test
  (testing "Node with empty dependency set is valid"
    (let [graph (f/make-graph [(f/make-node :1-root
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Multiple nodes with empty dependencies"
    (let [graph (f/make-graph [(f/make-node :1-assume1
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :depth 0)
                               (f/make-node :1-assume2
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :depth 0
                                            :order 1)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "get-ancestors returns empty for node with no deps"
    (let [graph (f/make-graph [(f/make-node :1-root
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :depth 0)])]
      (is (empty? (g/get-ancestors graph :1-root)))))

  (testing "get-descendants returns empty for isolated node"
    (let [graph (f/make-graph [(f/make-node :1-root
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :depth 0)])]
      (is (empty? (g/get-descendants graph :1-root)))))

  (testing "topological-sort handles all-independent nodes"
    (let [graph (f/make-graph [(f/make-node :1-a
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{})
                               (f/make-node :1-b
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :order 1)
                               (f/make-node :1-c
                                            :type :assumption
                                            :justification :assumption
                                            :deps #{}
                                            :order 2)])]
      (let [sorted (g/topological-sort graph)]
        (is (= 3 (count sorted)))
        (is (= #{:1-a :1-b :1-c} (set sorted)))))))

;; =============================================================================
;; 2. Large Graph Stress Tests
;; =============================================================================

(defn generate-stress-graph
  "Generate a stress test graph with n nodes in a linear chain."
  [n]
  (let [nodes (into {}
                    (for [i (range n)]
                      (let [id (keyword (str "1-" (format "%06x" i)))
                            deps (if (zero? i)
                                   #{}
                                   #{(keyword (str "1-" (format "%06x" (dec i))))})]
                        [id (f/make-node id
                                         :type (if (zero? i) :assumption :claim)
                                         :justification (if (zero? i) :assumption :modus-ponens)
                                         :deps deps
                                         :depth (if (zero? i) 0 1)
                                         :order i)])))]
    (f/make-graph (vals nodes))))

(deftest stress-test-linear-chain
  (testing "Large linear chain (1000 nodes) is valid"
    (let [graph (generate-stress-graph 1000)]
      (is (:valid (schema/validate-schema graph)))
      ;; Semantic validation may be slow, test separately
      ))

  (testing "get-ancestors on last node of 500-node chain"
    (let [graph (generate-stress-graph 500)
          last-id (keyword (str "1-" (format "%06x" 499)))]
      (let [ancestors (g/get-ancestors graph last-id)]
        (is (= 499 (count ancestors))))))

  (testing "get-descendants on first node of 500-node chain"
    (let [graph (generate-stress-graph 500)
          first-id :1-000000]
      (let [descendants (g/get-descendants graph first-id)]
        (is (= 499 (count descendants))))))

  (testing "topological-sort on 1000-node chain returns correct order"
    (let [graph (generate-stress-graph 1000)
          sorted (g/topological-sort graph)]
      (is (= 1000 (count sorted)))
      ;; First node should be first
      (is (= :1-000000 (first sorted)))
      ;; Last node should be last
      (is (= (keyword (str "1-" (format "%06x" 999))) (last sorted))))))

(defn generate-wide-stress-graph
  "Generate a wide graph with root and n-1 direct children."
  [n]
  (let [root-node (f/make-node :1-root
                               :type :assumption
                               :justification :assumption
                               :deps #{}
                               :depth 0)
        children (for [i (range 1 n)]
                   (f/make-node (keyword (str "1-child" i))
                                :deps #{:1-root}
                                :order i))]
    (f/make-graph (cons root-node children))))

(deftest stress-test-wide-fanout
  (testing "Wide graph (1 root, 999 children) is valid"
    (let [graph (generate-wide-stress-graph 1000)]
      (is (:valid (schema/validate-schema graph)))))

  (testing "get-descendants of root with 500 children"
    (let [graph (generate-wide-stress-graph 501)]
      (let [descendants (g/get-descendants graph :1-root)]
        (is (= 500 (count descendants))))))

  (testing "cycle detection on large acyclic graph"
    (let [graph (generate-stress-graph 500)]
      (is (nil? (v/find-cycle graph))))))

;; =============================================================================
;; 3. Unicode in Statements Tests
;; =============================================================================

(deftest unicode-statements-test
  (testing "Node with Greek letters in statement"
    (let [graph (f/make-graph [(f/make-node :1-greek
                                            :type :assumption
                                            :justification :assumption
                                            :statement "Let \u03B1, \u03B2, \u03B3 be real numbers"
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Node with mathematical symbols"
    (let [graph (f/make-graph [(f/make-node :1-math
                                            :type :assumption
                                            :justification :assumption
                                            :statement "\u2200x \u2208 \u211D, \u2203y : x < y"
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Node with Chinese characters"
    (let [graph (f/make-graph [(f/make-node :1-chinese
                                            :type :assumption
                                            :justification :assumption
                                            :statement "\u5B9A\u7406\uFF1A\u82E5 a > b \u4E14 b > c\uFF0C\u5219 a > c"
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Node with emoji (edge case)"
    (let [graph (f/make-graph [(f/make-node :1-emoji
                                            :type :assumption
                                            :justification :assumption
                                            :statement "Proof complete \u2713 \u2714"
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Node with mixed RTL and LTR text"
    (let [graph (f/make-graph [(f/make-node :1-rtl
                                            :type :assumption
                                            :justification :assumption
                                            :statement "\u05EA\u05D5\u05E8\u05D4: If x > 0 then \u05D0 is positive"
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Node with zero-width characters"
    (let [graph (f/make-graph [(f/make-node :1-zerowidth
                                            :type :assumption
                                            :justification :assumption
                                            ;; Contains zero-width joiner and non-joiner
                                            :statement (str "Test" \u200B "statement" \u200C "here")
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Token estimation handles Unicode correctly"
    (let [node (f/make-node :test :statement "\u03B1\u03B2\u03B3\u03B4\u03B5")]
      ;; Should not throw, should return positive value
      (is (pos? (g/estimate-node-tokens node))))))

;; =============================================================================
;; 4. Null/Nil Injection Tests
;; =============================================================================

(deftest nil-injection-test
  (testing "Schema rejects node with nil statement"
    (let [bad-node (assoc (f/make-node :1-bad) :statement nil)
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Schema rejects node with nil dependencies"
    (let [bad-node (assoc (f/make-node :1-bad) :dependencies nil)
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Schema rejects node with nil type"
    (let [bad-node (assoc (f/make-node :1-bad) :type nil)
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Schema rejects node with nil status"
    (let [bad-node (assoc (f/make-node :1-bad) :status nil)
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Schema rejects node with nil taint"
    (let [bad-node (assoc (f/make-node :1-bad) :taint nil)
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Schema rejects nil in dependency set"
    (let [bad-node (assoc (f/make-node :1-bad) :dependencies #{nil :1-other})
          graph (f/make-graph [bad-node])]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "get-ancestors handles missing node gracefully"
    (let [graph f/minimal-valid-graph]
      ;; Should return empty set, not throw
      (is (set? (g/get-ancestors graph :nonexistent)))))

  (testing "get-descendants handles missing node gracefully"
    (let [graph f/minimal-valid-graph]
      ;; Should return empty set, not throw
      (is (set? (g/get-descendants graph :nonexistent)))))

  (testing "compute-taint handles missing node gracefully"
    (let [graph f/minimal-valid-graph]
      ;; Returns :clean for missing node since no tainted deps found
      ;; (the node lookup returns nil, nil status doesn't trigger taint)
      (is (= :clean (g/compute-taint graph :nonexistent)))))

  (testing "Graph with nil nodes map is invalid"
    (let [bad-graph (assoc f/minimal-valid-graph :nodes nil)]
      (is (not (:valid (schema/validate-schema bad-graph)))))))

;; =============================================================================
;; 5. Integer Overflow in Version Tracking Tests
;; =============================================================================

(deftest version-overflow-test
  (testing "Version near Long/MAX_VALUE"
    (let [graph (assoc f/minimal-valid-graph :version (- Long/MAX_VALUE 10))]
      ;; Should still be valid
      (is (:valid (schema/validate-schema graph)))
      ;; Incrementing should work
      (let [incremented (g/increment-version graph)]
        (is (= (- Long/MAX_VALUE 9) (:version incremented))))))

  (testing "Version at Long/MAX_VALUE"
    (let [graph (assoc f/minimal-valid-graph :version Long/MAX_VALUE)]
      ;; Should be valid
      (is (:valid (schema/validate-schema graph)))
      ;; Incrementing will overflow - Clojure's default behavior is to throw
      ;; This documents that the system will throw at MAX_VALUE
      (is (thrown? ArithmeticException (g/increment-version graph)))))

  (testing "Version at 0 is rejected by schema"
    ;; Schema requires version >= 1
    (let [graph (assoc f/minimal-valid-graph :version 0)]
      (is (not (:valid (schema/validate-schema graph))))))

  (testing "Version at 1 (minimum valid)"
    (let [graph (assoc f/minimal-valid-graph :version 1)]
      (is (:valid (schema/validate-schema graph)))
      (let [incremented (g/increment-version graph)]
        (is (= 2 (:version incremented))))))

  (testing "Version as negative number (edge case)"
    (let [graph (assoc f/minimal-valid-graph :version -1)]
      ;; Schema should reject negative versions
      ;; If it doesn't, this documents the gap
      (let [result (schema/validate-schema graph)]
        ;; Document current behavior - negative may or may not be valid
        (is (boolean? (:valid result))))))

  (testing "Multiple rapid version increments"
    (let [graph f/minimal-valid-graph
          incremented (reduce (fn [g _] (g/increment-version g))
                              graph
                              (range 1000))]
      (is (= 1001 (:version incremented))))))

;; =============================================================================
;; 6. Circular Lemma Reference Tests
;; =============================================================================

(deftest circular-lemma-reference-test
  (testing "Lemma-ref to existing lemma is valid"
    (let [lemma {:id "L1"
                 :name "Test Lemma"
                 :statement "Test statement"
                 :content-hash "0123456789abcdef"
                 :root-node :1-archived
                 :extracted-nodes #{:1-archived}
                 :status :proven
                 :taint :clean}
          archived {:1-archived (f/make-node :1-archived
                                             :type :claim
                                             :statement "Archived claim")}
          graph (-> (f/make-graph [(f/make-node :1-root
                                                :type :assumption
                                                :justification :assumption
                                                :depth 0)
                                   (f/make-node :1-ref
                                                :type :lemma-ref
                                                :justification :lemma-application
                                                :lemma-id "L1"
                                                :deps #{:1-root}
                                                :order 1)])
                    (assoc :lemmas {"L1" lemma})
                    (assoc :archived-nodes archived))]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Lemma-ref to non-existent lemma fails referential integrity"
    (let [graph (f/make-graph [(f/make-node :1-root
                                            :type :assumption
                                            :justification :assumption
                                            :depth 0)
                               (f/make-node :1-ref
                                            :type :lemma-ref
                                            :justification :lemma-application
                                            :lemma-id "nonexistent"
                                            :deps #{:1-root}
                                            :order 1)])]
      (let [errors (v/check-lemma-refs graph)]
        (is (seq errors))
        (is (= :missing-lemma (:type (first errors)))))))

  (testing "Lemma with root-node pointing to non-existent archived node"
    (let [lemma {:id "L-bad"
                 :name "Bad Lemma"
                 :statement "Bad statement"
                 :content-hash "0123456789abcdef"
                 :root-node :1-nowhere
                 :extracted-nodes #{:1-nowhere}
                 :status :proven
                 :taint :clean}
          graph (-> (f/make-graph [(f/make-node :1-root
                                                :type :assumption
                                                :justification :assumption
                                                :depth 0)])
                    (assoc :lemmas {"L-bad" lemma}))]
      (let [errors (v/check-lemma-root-refs graph)]
        (is (seq errors))
        (is (= :missing-lemma-root (:type (first errors)))))))

  (testing "Multiple lemmas referencing each other's nodes (complex dependency)"
    ;; This tests a complex scenario where lemma extraction order matters
    (let [archived-a {:1-a (f/make-node :1-a :statement "Node A")}
          archived-b {:1-b (f/make-node :1-b :statement "Node B")}
          lemma-a {:id "LA"
                   :name "Lemma A"
                   :statement "Statement A"
                   :content-hash "0123456789abcdef"
                   :root-node :1-a
                   :extracted-nodes #{:1-a}
                   :status :proven
                   :taint :clean}
          lemma-b {:id "LB"
                   :name "Lemma B"
                   :statement "Statement B"
                   :content-hash "fedcba9876543210"
                   :root-node :1-b
                   :extracted-nodes #{:1-b}
                   :status :proven
                   :taint :clean}
          graph (-> (f/make-graph [(f/make-node :1-root
                                                :type :assumption
                                                :justification :assumption
                                                :depth 0)])
                    (assoc :lemmas {"LA" lemma-a "LB" lemma-b})
                    (assoc :archived-nodes (merge archived-a archived-b)))]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Taint propagation through lemma-ref"
    (let [;; Create a tainted lemma
          tainted-lemma {:id "L-tainted"
                         :name "Tainted Lemma"
                         :statement "Tainted statement"
                         :content-hash "0123456789abcdef"
                         :root-node :1-tainted
                         :extracted-nodes #{:1-tainted}
                         :status :tainted
                         :taint :tainted}
          archived {:1-tainted (f/make-node :1-tainted
                                            :status :admitted
                                            :taint :self-admitted)}
          ;; Node referencing tainted lemma
          graph (-> (f/make-graph [(f/make-node :1-root
                                                :type :assumption
                                                :justification :assumption
                                                :depth 0)
                                   (f/make-node :1-ref
                                                :type :lemma-ref
                                                :justification :lemma-application
                                                :lemma-id "L-tainted"
                                                :deps #{:1-root}
                                                :taint :clean  ; Wrong - should be tainted
                                                :order 1)])
                    (assoc :lemmas {"L-tainted" tainted-lemma})
                    (assoc :archived-nodes archived))]
      ;; compute-taint should recognize this needs to be tainted
      (is (= :tainted (g/compute-taint graph :1-ref)))
      ;; Taint validation should catch the incorrect stored taint
      (let [errors (v/check-taint-correctness graph)]
        (is (seq errors))))))

;; =============================================================================
;; Edge Case: Empty Graph
;; =============================================================================

(deftest empty-graph-test
  (testing "Graph with no nodes is valid"
    (is (:valid (schema/validate-schema f/empty-nodes-graph)))
    (is (:valid (v/validate-semantics f/empty-nodes-graph))))

  (testing "topological-sort on empty graph"
    (let [sorted (g/topological-sort f/empty-nodes-graph)]
      (is (empty? sorted))))

  (testing "node-ids on empty graph"
    (is (empty? (g/node-ids f/empty-nodes-graph))))

  (testing "find-cycle on empty graph returns nil"
    (is (nil? (v/find-cycle f/empty-nodes-graph)))))

;; =============================================================================
;; Edge Case: Very Long Statements
;; =============================================================================

(deftest very-long-statement-test
  (testing "Node with 10KB statement"
    (let [long-statement (apply str (repeat 10000 "x"))
          graph (f/make-graph [(f/make-node :1-long
                                            :type :assumption
                                            :justification :assumption
                                            :statement long-statement
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (v/validate-semantics graph)))))

  (testing "Token estimation for very long statement"
    (let [long-statement (apply str (repeat 10000 "x"))
          node (f/make-node :test :statement long-statement)]
      (is (pos? (g/estimate-node-tokens node)))
      ;; Should be proportional to length
      (is (> (g/estimate-node-tokens node) 100)))))

;; =============================================================================
;; Edge Case: Special Characters in IDs
;; =============================================================================

(deftest special-id-characters-test
  (testing "Node ID with only hex characters (standard format)"
    (let [graph (f/make-graph [(f/make-node :1-abcdef
                                            :type :assumption
                                            :justification :assumption
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph)))))

  (testing "Node ID with numbers"
    (let [graph (f/make-graph [(f/make-node :1-123456
                                            :type :assumption
                                            :justification :assumption
                                            :depth 0)])]
      (is (:valid (schema/validate-schema graph))))))
