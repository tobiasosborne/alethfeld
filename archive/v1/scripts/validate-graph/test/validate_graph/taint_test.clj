(ns validate-graph.taint-test
  "Tests for taint propagation validation."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.validators :as v]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Basic Taint Rules Tests
;; =============================================================================

(deftest verified-clean-deps-is-clean-test
  (testing "Verified node with clean deps is clean"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root
                                 :type :assumption
                                 :justification :assumption
                                 :status :verified
                                 :taint :clean
                                 :depth 0)
                  (fix/make-node :1-child
                                 :deps #{:1-root}
                                 :status :verified
                                 :taint :clean)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest admitted-is-self-admitted-test
  (testing "Admitted node should be self-admitted"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest admitted-wrong-taint-detected-test
  (testing "Admitted node with wrong taint is detected"
    (let [errors (v/check-taint-correctness fix/incorrect-taint-admitted-graph)]
      (is (= 1 (count errors)))
      (is (= :incorrect-taint (:type (first errors))))
      (is (= :clean (:actual (first errors))))
      (is (= :self-admitted (:expected (first errors)))))))

(deftest rejected-is-tainted-test
  (testing "Rejected node should be tainted"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-rejected
                                 :status :rejected
                                 :taint :tainted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest rejected-wrong-taint-detected-test
  (testing "Rejected node with wrong taint is detected"
    (let [errors (v/check-taint-correctness fix/incorrect-taint-rejected-graph)]
      (is (= 1 (count errors)))
      (is (= :incorrect-taint (:type (first errors))))
      (is (= :tainted (:expected (first errors)))))))

(deftest proposed-clean-deps-is-clean-test
  (testing "Proposed node with clean deps is clean"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root
                                 :type :assumption
                                 :justification :assumption
                                 :status :verified
                                 :taint :clean
                                 :depth 0)
                  (fix/make-node :1-proposed
                                 :deps #{:1-root}
                                 :status :proposed
                                 :taint :clean)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

;; =============================================================================
;; Taint Propagation Tests
;; =============================================================================

(deftest taint-propagates-from-admitted-test
  (testing "Taint propagates from admitted dependency"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-child
                                 :deps #{:1-admitted}
                                 :status :verified
                                 :taint :tainted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest taint-propagation-not-happening-detected-test
  (testing "Missing taint propagation is detected"
    (let [errors (v/check-taint-correctness fix/incorrect-taint-chain-graph)]
      (is (= 1 (count errors)))
      (is (= :incorrect-taint (:type (first errors))))
      (is (= :1-bbb222 (:node-id (first errors))))
      (is (= :tainted (:expected (first errors)))))))

(deftest taint-propagates-through-chain-test
  (testing "Taint propagates through long chain"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-level1
                                 :deps #{:1-admitted}
                                 :status :verified
                                 :taint :tainted)
                  (fix/make-node :1-level2
                                 :deps #{:1-level1}
                                 :status :verified
                                 :taint :tainted)
                  (fix/make-node :1-level3
                                 :deps #{:1-level2}
                                 :status :verified
                                 :taint :tainted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest chain-with-wrong-taint-at-end-test
  (testing "Chain with wrong taint at end is detected"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-level1
                                 :deps #{:1-admitted}
                                 :status :verified
                                 :taint :tainted)
                  (fix/make-node :1-level2
                                 :deps #{:1-level1}
                                 :status :verified
                                 :taint :clean)])  ; Should be tainted
          errors (v/check-taint-correctness graph)]
      (is (= 1 (count errors)))
      (is (= :1-level2 (:node-id (first errors)))))))

(deftest multiple-taint-sources-test
  (testing "Node with multiple taint sources is tainted"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted1
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-admitted2
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-child
                                 :deps #{:1-admitted1 :1-admitted2}
                                 :status :verified
                                 :taint :tainted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest clean-subtree-remains-clean-test
  (testing "Clean subtree with no taint sources remains clean"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root
                                 :type :assumption
                                 :justification :assumption
                                 :status :verified
                                 :taint :clean
                                 :depth 0)
                  (fix/make-node :1-b
                                 :deps #{:1-root}
                                 :status :verified
                                 :taint :clean)
                  (fix/make-node :1-c
                                 :deps #{:1-b}
                                 :status :verified
                                 :taint :clean)
                  (fix/make-node :1-d
                                 :deps #{:1-b :1-c}
                                 :status :verified
                                 :taint :clean)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest mixed-clean-and-tainted-deps-test
  (testing "Node with mixed clean/tainted deps is tainted"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-clean
                                 :status :verified
                                 :taint :clean)
                  (fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-mixed
                                 :deps #{:1-clean :1-admitted}
                                 :status :verified
                                 :taint :tainted)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest mixed-deps-wrong-taint-detected-test
  (testing "Node with mixed deps but wrong taint is detected"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-clean
                                 :status :verified
                                 :taint :clean)
                  (fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-mixed
                                 :deps #{:1-clean :1-admitted}
                                 :status :verified
                                 :taint :clean)])  ; Should be tainted
          errors (v/check-taint-correctness graph)]
      (is (= 1 (count errors))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest empty-deps-is-clean-test
  (testing "Node with no dependencies is clean if verified"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-alone
                                 :deps #{}
                                 :status :verified
                                 :taint :clean)])
          errors (v/check-taint-correctness graph)]
      (is (empty? errors)))))

(deftest empty-graph-taint-valid-test
  (testing "Empty nodes graph has no taint errors"
    (let [errors (v/check-taint-correctness fix/empty-nodes-graph)]
      (is (empty? errors)))))

(deftest self-admitted-doesnt-propagate-as-self-admitted-test
  (testing "Dependent of self-admitted is tainted, not self-admitted"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-admitted
                                 :status :admitted
                                 :taint :self-admitted)
                  (fix/make-node :1-child
                                 :deps #{:1-admitted}
                                 :status :verified
                                 :taint :self-admitted)])  ; Should be :tainted, not :self-admitted
          errors (v/check-taint-correctness graph)]
      (is (= 1 (count errors)))
      (is (= :tainted (:expected (first errors)))))))

;; =============================================================================
;; Helper Function Tests
;; =============================================================================

(deftest compute-taint-admitted-test
  (testing "compute-taint returns :self-admitted for admitted status"
    (let [graph (fix/make-graph [(fix/make-node :1-node :status :admitted)])]
      (is (= :self-admitted (v/compute-taint graph :1-node))))))

(deftest compute-taint-rejected-test
  (testing "compute-taint returns :tainted for rejected status"
    (let [graph (fix/make-graph [(fix/make-node :1-node :status :rejected)])]
      (is (= :tainted (v/compute-taint graph :1-node))))))

(deftest compute-taint-verified-clean-test
  (testing "compute-taint returns :clean for verified with clean deps"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :status :verified :taint :clean)
                  (fix/make-node :1-child :deps #{:1-root} :status :verified)])]
      (is (= :clean (v/compute-taint graph :1-child))))))

(deftest compute-taint-verified-tainted-dep-test
  (testing "compute-taint returns :tainted for verified with tainted dep"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :status :admitted :taint :self-admitted)
                  (fix/make-node :1-child :deps #{:1-root} :status :verified)])]
      (is (= :tainted (v/compute-taint graph :1-child))))))
