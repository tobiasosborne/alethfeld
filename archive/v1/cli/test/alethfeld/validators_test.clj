(ns alethfeld.validators-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.validators :as v]
            [alethfeld.graph :as g]
            [alethfeld.fixtures :as f]))

(deftest referential-integrity-test
  (testing "Valid graphs have no referential errors"
    (is (empty? (v/check-referential-integrity f/minimal-valid-graph)))
    (is (empty? (v/check-referential-integrity f/linear-chain-graph)))
    (is (empty? (v/check-referential-integrity f/diamond-graph))))

  (testing "Missing dependency detected"
    (let [errors (v/check-dependency-refs f/missing-dependency-graph)]
      (is (= 1 (count errors)))
      (is (= :missing-dependency (:type (first errors)))))))

(deftest acyclicity-test
  (testing "Valid DAGs have no cycles"
    (is (nil? (v/find-cycle f/minimal-valid-graph)))
    (is (nil? (v/find-cycle f/linear-chain-graph)))
    (is (nil? (v/find-cycle f/diamond-graph))))

  (testing "Self-loop detected"
    (let [cycle (v/find-cycle f/self-loop-graph)]
      (is (some? cycle))
      (is (contains? (set cycle) :1-aaa111))))

  (testing "Direct cycle detected"
    (let [cycle (v/find-cycle f/direct-cycle-graph)]
      (is (some? cycle))
      (is (>= (count cycle) 2)))))

(deftest scope-validation-test
  (testing "Valid scoped graph passes"
    (is (empty? (v/check-scopes f/scoped-graph))))

  (testing "Valid scope computation via graph module"
    (let [scope (g/compute-valid-scope f/scoped-graph :1-ccc333)]
      (is (contains? scope :1-bbb222)))))

(deftest taint-validation-test
  (testing "Valid graphs have correct taint"
    (is (empty? (v/check-taint-correctness f/minimal-valid-graph)))
    (is (empty? (v/check-taint-correctness f/linear-chain-graph))))

  (testing "Admitted node taint check"
    (let [errors (v/check-taint-correctness f/incorrect-taint-admitted-graph)]
      (is (= 1 (count errors)))
      (is (= :incorrect-taint (:type (first errors))))
      (is (= :self-admitted (:expected (first errors))))))

  (testing "Taint propagation check"
    (let [errors (v/check-taint-correctness f/incorrect-taint-chain-graph)]
      (is (= 1 (count errors)))
      (is (= :incorrect-taint (:type (first errors))))
      (is (= :tainted (:expected (first errors)))))))

(deftest full-validation-test
  (testing "Valid graphs pass full validation"
    (is (:valid (v/validate-semantics f/minimal-valid-graph)))
    (is (:valid (v/validate-semantics f/linear-chain-graph)))
    (is (:valid (v/validate-semantics f/diamond-graph)))
    (is (:valid (v/validate-semantics f/scoped-graph))))

  (testing "Invalid graphs fail validation"
    (is (not (:valid (v/validate-semantics f/missing-dependency-graph))))
    (is (not (:valid (v/validate-semantics f/self-loop-graph))))
    (is (not (:valid (v/validate-semantics f/incorrect-taint-admitted-graph))))))
