(ns validate-graph.referential-test
  "Tests for referential integrity validation."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.validators :as v]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Dependency Reference Tests
;; =============================================================================

(deftest valid-dependencies-test
  (testing "Valid dependencies pass"
    (let [errors (v/check-dependency-refs fix/linear-chain-graph)]
      (is (empty? errors)))))

(deftest missing-dependency-test
  (testing "Missing dependency is detected"
    (let [errors (v/check-dependency-refs fix/missing-dependency-graph)]
      (is (= 1 (count errors)))
      (is (= :missing-dependency (:type (first errors))))
      (is (= :1-nonexistent (:missing-ref (first errors)))))))

(deftest self-dependency-test
  (testing "Self-dependency is detected as referential issue (cycle check is separate)"
    (let [errors (v/check-dependency-refs fix/self-loop-graph)]
      ;; Self-loop is referentially valid (node exists), cycle check catches it
      (is (empty? errors)))))

(deftest empty-dependencies-valid-test
  (testing "Empty dependencies set is valid"
    (let [graph (fix/make-graph [(fix/make-node :1-alone :deps #{})])
          errors (v/check-dependency-refs graph)]
      (is (empty? errors)))))

(deftest multiple-valid-deps-test
  (testing "Node with multiple valid dependencies passes"
    (let [errors (v/check-dependency-refs fix/diamond-graph)]
      (is (empty? errors)))))

(deftest multiple-missing-deps-test
  (testing "Multiple missing dependencies are all detected"
    (let [graph (fix/make-graph [(fix/make-node :1-bad
                                                :deps #{:1-missing1 :1-missing2 :1-missing3})])
          errors (v/check-dependency-refs graph)]
      (is (= 3 (count errors)))
      (is (every? #(= :missing-dependency (:type %)) errors)))))

;; =============================================================================
;; Parent Reference Tests
;; =============================================================================

(deftest valid-parent-test
  (testing "Valid parent reference passes"
    (let [graph (fix/make-graph [(fix/make-node :1-parent :depth 1)
                                 (fix/make-node :2-child :depth 2 :parent :1-parent)])
          errors (v/check-parent-refs graph)]
      (is (empty? errors)))))

(deftest nil-parent-valid-test
  (testing "Nil parent (root node) is valid"
    (let [errors (v/check-parent-refs fix/minimal-valid-graph)]
      (is (empty? errors)))))

(deftest missing-parent-test
  (testing "Missing parent is detected"
    (let [errors (v/check-parent-refs fix/missing-parent-graph)]
      (is (= 1 (count errors)))
      (is (= :missing-parent (:type (first errors))))
      (is (= :1-nonexistent (:missing-ref (first errors)))))))

;; =============================================================================
;; Lemma Reference Tests
;; =============================================================================

(deftest valid-lemma-ref-test
  (testing "Valid lemma-ref passes"
    (let [errors (v/check-lemma-refs fix/all-node-types-graph)]
      ;; all-node-types-graph has valid lemma setup
      (is (empty? errors)))))

(deftest missing-lemma-ref-test
  (testing "Missing lemma reference is detected"
    (let [errors (v/check-lemma-refs fix/missing-lemma-ref-graph)]
      (is (= 1 (count errors)))
      (is (= :missing-lemma (:type (first errors))))
      (is (= "nonexistent-lemma" (:missing-ref (first errors)))))))

(deftest non-lemma-ref-ignored-test
  (testing "Non-lemma-ref nodes without lemma-id are ignored"
    (let [errors (v/check-lemma-refs fix/minimal-valid-graph)]
      (is (empty? errors)))))

;; =============================================================================
;; External Reference Tests
;; =============================================================================

(deftest valid-external-ref-test
  (testing "Valid external-ref passes"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-ext]
                              (fix/make-node :1-ext
                                             :type :external-ref
                                             :justification :external-application
                                             :external-id "ext-001"))
                    (assoc :external-refs {"ext-001" {:id "ext-001"
                                                      :doi "10.1234/test"
                                                      :claimed-statement "claim"
                                                      :verification-status :verified}}))
          errors (v/check-external-refs graph)]
      (is (empty? errors)))))

(deftest missing-external-ref-test
  (testing "Missing external reference is detected"
    (let [errors (v/check-external-refs fix/missing-external-ref-graph)]
      (is (= 1 (count errors)))
      (is (= :missing-external-ref (:type (first errors))))
      (is (= "nonexistent-external" (:missing-ref (first errors)))))))

;; =============================================================================
;; Symbol Reference Tests
;; =============================================================================

(deftest valid-symbol-intro-test
  (testing "Valid symbol introduced-at passes"
    (let [graph (assoc fix/minimal-valid-graph :symbols
                       {:sym-x {:id :sym-x
                                :name "x"
                                :type "Real"
                                :tex "x"
                                :scope :global
                                :introduced-at :1-abc123}})
          errors (v/check-symbol-refs graph)]
      (is (empty? errors)))))

(deftest missing-symbol-intro-test
  (testing "Missing symbol introduced-at node is detected"
    (let [graph (assoc fix/minimal-valid-graph :symbols
                       {:sym-x {:id :sym-x
                                :name "x"
                                :type "Real"
                                :tex "x"
                                :scope :global
                                :introduced-at :1-nonexistent}})
          errors (v/check-symbol-refs graph)]
      (is (= 1 (count errors)))
      (is (= :missing-symbol-intro (:type (first errors)))))))

;; =============================================================================
;; Lemma Root Node Tests
;; =============================================================================

(deftest valid-lemma-root-in-archived-test
  (testing "Lemma root in archived-nodes passes"
    (let [errors (v/check-lemma-root-refs fix/all-node-types-graph)]
      (is (empty? errors)))))

(deftest valid-lemma-root-in-nodes-test
  (testing "Lemma root in active nodes also passes"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc :lemmas {"lem-001" {:id "lem-001"
                                               :name "Test"
                                               :statement "stmt"
                                               :content-hash "0123456789abcdef"
                                               :root-node :1-abc123  ; exists in :nodes
                                               :status :proven
                                               :taint :clean
                                               :extracted-nodes #{:1-abc123}}}))
          errors (v/check-lemma-root-refs graph)]
      (is (empty? errors)))))

(deftest missing-lemma-root-test
  (testing "Missing lemma root node is detected"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc :lemmas {"lem-001" {:id "lem-001"
                                               :name "Test"
                                               :statement "stmt"
                                               :content-hash "0123456789abcdef"
                                               :root-node :1-nonexistent
                                               :status :proven
                                               :taint :clean
                                               :extracted-nodes #{}}}))
          errors (v/check-lemma-root-refs graph)]
      (is (= 1 (count errors)))
      (is (= :missing-lemma-root (:type (first errors)))))))

;; =============================================================================
;; Combined Referential Integrity Tests
;; =============================================================================

(deftest all-refs-valid-test
  (testing "Graph with all valid references passes all checks"
    (let [errors (v/check-referential-integrity fix/all-node-types-graph)]
      (is (empty? errors)))))

(deftest multiple-ref-errors-test
  (testing "Multiple referential errors are all detected"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-bad1]
                              (fix/make-node :1-bad1 :deps #{:1-missing}))
                    (assoc-in [:nodes :1-bad2]
                              (fix/make-node :1-bad2 :parent :1-missing-parent))
                    (assoc :symbols {:sym-bad {:id :sym-bad
                                               :name "bad"
                                               :type "T"
                                               :tex "b"
                                               :scope :global
                                               :introduced-at :1-missing-sym}}))
          errors (v/check-referential-integrity graph)]
      (is (>= (count errors) 3)))))

(deftest empty-graph-refs-valid-test
  (testing "Empty nodes graph has no referential errors"
    (let [errors (v/check-referential-integrity fix/empty-nodes-graph)]
      (is (empty? errors)))))
