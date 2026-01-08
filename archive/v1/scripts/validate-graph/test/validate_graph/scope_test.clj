(ns validate-graph.scope-test
  "Tests for scope validation (local-assume/local-discharge)."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.validators :as v]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Valid Scope Tests
;; =============================================================================

(deftest empty-scope-for-root-test
  (testing "Empty scope for root nodes is valid"
    (let [errors (v/check-scope-validity fix/minimal-valid-graph)]
      (is (empty? errors)))))

(deftest valid-scoped-graph-test
  (testing "Valid scoped graph passes"
    (let [errors (v/check-scopes fix/scoped-graph)]
      (is (empty? errors)))))

(deftest scope-contains-ancestor-assume-test
  (testing "Scope containing ancestor local-assume is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  (fix/make-node :1-child
                                 :deps #{:1-assume}
                                 :scope #{:1-assume})])
          errors (v/check-scope-validity graph)]
      (is (empty? errors)))))

(deftest nested-assumes-in-scope-test
  (testing "Nested local-assumes both in scope is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-assume1
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  (fix/make-node :1-assume2
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "Q"
                                 :deps #{:1-assume1}
                                 :scope #{:1-assume1})
                  (fix/make-node :1-child
                                 :deps #{:1-assume2}
                                 :scope #{:1-assume1 :1-assume2})])
          errors (v/check-scope-validity graph)]
      (is (empty? errors)))))

(deftest scope-excludes-discharged-test
  (testing "Scope correctly excludes discharged assumptions"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  (fix/make-node :1-discharge
                                 :type :local-discharge
                                 :justification :discharge
                                 :discharges :1-assume
                                 :deps #{:1-assume}
                                 :scope #{:1-assume})
                  (fix/make-node :1-after
                                 :deps #{:1-discharge}
                                 :scope #{})])  ; :1-assume is discharged
          errors (v/check-scope-validity graph)]
      (is (empty? errors)))))

;; =============================================================================
;; Invalid Scope Tests
;; =============================================================================

(deftest scope-contains-non-ancestor-test
  (testing "Scope containing non-ancestor local-assume is invalid"
    (let [errors (v/check-scope-validity fix/invalid-scope-non-ancestor-graph)]
      (is (= 1 (count errors)))
      (is (= :invalid-scope (:type (first errors))))
      (is (contains? (:invalid-entries (first errors)) :1-aaa111)))))

(deftest scope-contains-discharged-test
  (testing "Scope containing already-discharged assumption is invalid"
    (let [errors (v/check-scope-validity fix/invalid-scope-discharged-graph)]
      (is (= 1 (count errors)))
      (is (= :invalid-scope (:type (first errors)))))))

(deftest scope-contains-non-local-assume-test
  (testing "Scope containing non-local-assume node is invalid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-claim :deps #{:1-root})
                  (fix/make-node :1-bad :deps #{:1-claim} :scope #{:1-claim})])  ; :1-claim is not local-assume
          errors (v/check-scope-validity graph)]
      (is (= 1 (count errors)))
      (is (= :invalid-scope (:type (first errors)))))))

;; =============================================================================
;; Discharge Validity Tests
;; =============================================================================

(deftest valid-discharge-test
  (testing "Valid discharge passes"
    (let [errors (v/check-discharge-validity fix/scoped-graph)]
      (is (empty? errors)))))

(deftest discharge-not-ancestor-test
  (testing "Discharge of non-ancestor is invalid"
    (let [errors (v/check-discharge-validity fix/invalid-discharge-not-ancestor-graph)]
      (is (= 1 (count errors)))
      (is (= :discharge-not-ancestor (:type (first errors)))))))

(deftest discharge-targets-existing-assume-test
  (testing "Discharge targets an existing local-assume"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P")
                  (fix/make-node :1-claim :deps #{:1-assume} :scope #{:1-assume})
                  (fix/make-node :1-discharge
                                 :type :local-discharge
                                 :justification :discharge
                                 :discharges :1-assume
                                 :deps #{:1-claim}
                                 :scope #{:1-assume})])
          errors (v/check-discharge-validity graph)]
      (is (empty? errors)))))

;; =============================================================================
;; Complex Scope Scenarios
;; =============================================================================

(deftest nested-assume-discharge-pairs-test
  (testing "Nested assume-discharge pairs are valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  ;; Outer assume
                  (fix/make-node :1-outer-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  ;; Inner assume
                  (fix/make-node :1-inner-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "Q"
                                 :deps #{:1-outer-assume}
                                 :scope #{:1-outer-assume})
                  ;; Claim using both
                  (fix/make-node :1-claim
                                 :deps #{:1-inner-assume}
                                 :scope #{:1-outer-assume :1-inner-assume})
                  ;; Discharge inner
                  (fix/make-node :1-inner-discharge
                                 :type :local-discharge
                                 :justification :discharge
                                 :discharges :1-inner-assume
                                 :deps #{:1-claim}
                                 :scope #{:1-outer-assume :1-inner-assume})
                  ;; Claim after inner discharge (only outer in scope)
                  (fix/make-node :1-after-inner
                                 :deps #{:1-inner-discharge}
                                 :scope #{:1-outer-assume})
                  ;; Discharge outer
                  (fix/make-node :1-outer-discharge
                                 :type :local-discharge
                                 :justification :discharge
                                 :discharges :1-outer-assume
                                 :deps #{:1-after-inner}
                                 :scope #{:1-outer-assume})])
          errors (v/check-scopes graph)]
      (is (empty? errors)))))

(deftest sibling-branches-independent-scopes-test
  (testing "Sibling branches have independent scopes"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  ;; Branch A
                  (fix/make-node :1-assume-a
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  (fix/make-node :1-claim-a :deps #{:1-assume-a} :scope #{:1-assume-a})
                  ;; Branch B (different assume, sibling)
                  (fix/make-node :1-assume-b
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "Q"
                                 :deps #{:1-root})
                  (fix/make-node :1-claim-b :deps #{:1-assume-b} :scope #{:1-assume-b})])
          errors (v/check-scopes graph)]
      (is (empty? errors)))))

(deftest assumption-discharged-in-one-branch-test
  (testing "Assumption discharged in one branch is not in sibling's scope"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-root :type :assumption :justification :assumption :depth 0)
                  (fix/make-node :1-assume
                                 :type :local-assume
                                 :justification :local-assumption
                                 :introduces "P"
                                 :deps #{:1-root})
                  ;; Branch A: uses and discharges
                  (fix/make-node :1-use-a :deps #{:1-assume} :scope #{:1-assume})
                  (fix/make-node :1-discharge-a
                                 :type :local-discharge
                                 :justification :discharge
                                 :discharges :1-assume
                                 :deps #{:1-use-a}
                                 :scope #{:1-assume})
                  ;; Branch B: also uses (before discharge in A)
                  (fix/make-node :1-use-b :deps #{:1-assume} :scope #{:1-assume})])
          errors (v/check-scopes graph)]
      (is (empty? errors)))))

;; =============================================================================
;; Helper Function Tests
;; =============================================================================

(deftest get-ancestors-linear-test
  (testing "get-ancestors returns all ancestors in linear chain"
    (let [ancestors (v/get-ancestors fix/linear-chain-graph :1-ccc333)]
      (is (= #{:1-aaa111 :1-bbb222} ancestors)))))

(deftest get-ancestors-diamond-test
  (testing "get-ancestors returns all ancestors in diamond"
    (let [ancestors (v/get-ancestors fix/diamond-graph :1-ddd444)]
      (is (= #{:1-aaa111 :1-bbb222 :1-ccc333} ancestors)))))

(deftest get-ancestors-root-test
  (testing "get-ancestors of root returns empty set"
    (let [ancestors (v/get-ancestors fix/minimal-valid-graph :1-abc123)]
      (is (empty? ancestors)))))

(deftest compute-valid-scope-no-assumes-test
  (testing "compute-valid-scope with no local-assumes returns empty"
    (let [scope (v/compute-valid-scope fix/linear-chain-graph :1-ccc333)]
      (is (empty? scope)))))

(deftest compute-valid-scope-with-assume-test
  (testing "compute-valid-scope with local-assume returns it"
    (let [scope (v/compute-valid-scope fix/scoped-graph :1-ccc333)]
      (is (= #{:1-bbb222} scope)))))
