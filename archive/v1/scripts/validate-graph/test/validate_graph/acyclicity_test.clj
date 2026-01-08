(ns validate-graph.acyclicity-test
  "Tests for dependency graph acyclicity validation."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.validators :as v]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Valid DAG Tests
;; =============================================================================

(deftest linear-chain-acyclic-test
  (testing "Linear chain A->B->C is acyclic"
    (let [errors (v/check-acyclicity fix/linear-chain-graph)]
      (is (empty? errors)))))

(deftest diamond-pattern-acyclic-test
  (testing "Diamond pattern is acyclic"
    (let [errors (v/check-acyclicity fix/diamond-graph)]
      (is (empty? errors)))))

(deftest single-node-acyclic-test
  (testing "Single node with no deps is acyclic"
    (let [errors (v/check-acyclicity fix/minimal-valid-graph)]
      (is (empty? errors)))))

(deftest empty-graph-acyclic-test
  (testing "Empty nodes graph is trivially acyclic"
    (let [errors (v/check-acyclicity fix/empty-nodes-graph)]
      (is (empty? errors)))))

(deftest tree-structure-acyclic-test
  (testing "Tree structure is acyclic"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-c1 :deps #{:1-root})
                  (fix/make-node :1-c2 :deps #{:1-root})
                  (fix/make-node :1-c11 :deps #{:1-c1})
                  (fix/make-node :1-c12 :deps #{:1-c1})
                  (fix/make-node :1-c21 :deps #{:1-c2})])
          errors (v/check-acyclicity graph)]
      (is (empty? errors)))))

(deftest complex-dag-acyclic-test
  (testing "Complex DAG with multiple paths is acyclic"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-a :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-b :deps #{:1-a})
                  (fix/make-node :1-c :deps #{:1-a})
                  (fix/make-node :1-d :deps #{:1-b :1-c})
                  (fix/make-node :1-e :deps #{:1-b})
                  (fix/make-node :1-f :deps #{:1-d :1-e})
                  (fix/make-node :1-g :deps #{:1-c :1-f})])
          errors (v/check-acyclicity graph)]
      (is (empty? errors)))))

(deftest deeply-nested-acyclic-test
  (testing "Deeply nested graph is acyclic"
    (let [errors (v/check-acyclicity fix/deeply-nested-graph)]
      (is (empty? errors)))))

(deftest wide-graph-acyclic-test
  (testing "Wide graph with many siblings is acyclic"
    (let [errors (v/check-acyclicity fix/wide-graph)]
      (is (empty? errors)))))

;; =============================================================================
;; Cycle Detection Tests
;; =============================================================================

(deftest self-loop-detected-test
  (testing "Self-loop A->A is detected"
    (let [errors (v/check-acyclicity fix/self-loop-graph)]
      (is (= 1 (count errors)))
      (is (= :dependency-cycle (:type (first errors))))
      (is (vector? (:cycle (first errors)))))))

(deftest direct-cycle-detected-test
  (testing "Direct cycle A->B->A is detected"
    (let [errors (v/check-acyclicity fix/direct-cycle-graph)]
      (is (= 1 (count errors)))
      (is (= :dependency-cycle (:type (first errors))))
      (let [cycle (:cycle (first errors))]
        (is (= 2 (count cycle)))))))

(deftest triangle-cycle-detected-test
  (testing "Triangle cycle A->B->C->A is detected"
    (let [errors (v/check-acyclicity fix/triangle-cycle-graph)]
      (is (= 1 (count errors)))
      (is (= :dependency-cycle (:type (first errors))))
      (let [cycle (:cycle (first errors))]
        (is (= 3 (count cycle)))))))

(deftest long-cycle-detected-test
  (testing "Long 5-node cycle is detected"
    (let [errors (v/check-acyclicity fix/long-cycle-graph)]
      (is (= 1 (count errors)))
      (is (= :dependency-cycle (:type (first errors))))
      (let [cycle (:cycle (first errors))]
        (is (= 5 (count cycle)))))))

(deftest cycle-in-subgraph-test
  (testing "Cycle in subgraph is detected even with valid main graph"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-good1 :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-good2 :deps #{:1-good1})
                  ;; Isolated cycle
                  (fix/make-node :1-cyc1 :deps #{:1-cyc2})
                  (fix/make-node :1-cyc2 :deps #{:1-cyc1})])
          errors (v/check-acyclicity graph)]
      (is (= 1 (count errors)))
      (is (= :dependency-cycle (:type (first errors)))))))

(deftest cycle-message-includes-path-test
  (testing "Cycle error message includes the cycle path"
    (let [errors (v/check-acyclicity fix/triangle-cycle-graph)
          message (:message (first errors))]
      (is (clojure.string/includes? message "->")))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest disconnected-components-no-cycle-test
  (testing "Disconnected acyclic components are valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-comp1-a :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-comp1-b :deps #{:1-comp1-a})
                  (fix/make-node :1-comp2-a :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-comp2-b :deps #{:1-comp2-a})])
          errors (v/check-acyclicity graph)]
      (is (empty? errors)))))

(deftest deps-to-external-nodes-test
  (testing "Dependencies to nodes not in graph (assumptions) don't cause issues"
    ;; This tests robustness when deps reference things that might not be in :nodes
    (let [graph (fix/make-graph
                 [(fix/make-node :1-node1
                                 :deps #{:external-assumption}
                                 :type :assumption
                                 :justification :assumption)])
          errors (v/check-acyclicity graph)]
      ;; Should not error on acyclicity (referential check catches missing deps)
      (is (empty? errors)))))

(deftest find-cycle-returns-nil-for-dag-test
  (testing "find-cycle returns nil for valid DAG"
    (is (nil? (v/find-cycle fix/linear-chain-graph)))))

(deftest find-cycle-returns-cycle-vector-test
  (testing "find-cycle returns vector of node IDs for cycle"
    (let [cycle (v/find-cycle fix/direct-cycle-graph)]
      (is (vector? cycle))
      (is (every? keyword? cycle)))))
