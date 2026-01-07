(ns alethfeld.mutation-assertions-test
  "Mutation assertion tests - verify test suite catches semantic errors
   by checking that mutations in code logic would cause test failures.
   
   Rather than running true mutation testing (which is limited in Clojure),
   these tests verify that our test suite can catch common semantic errors:
   - Boundary condition changes
   - Operator inversions
   - Logic inversions
   - Return value modifications"
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.graph :as graph]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as validators]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; Mutation: Acyclicity Check Evasion
;; =============================================================================

(deftest mutation-cycle-detection-coverage-test
  (testing "Tests would fail if cycle detection were bypassed"
    ;; If validators/find-cycle was mutated to return nil always:
    (let [cycle (validators/find-cycle f/self-loop-graph)]
      (is (some? cycle) "Cycle detection must catch self-loops")
      (is (contains? (set cycle) :1-aaa111) "Cycle path must include self-referencing node")))

  (testing "Tests would fail if cycle detection inverted logic"
    ;; If find-cycle returned result when none exists:
    (let [cycle (validators/find-cycle f/linear-chain-graph)]
      (is (nil? cycle) "Valid DAGs must not report cycles"))))

;; =============================================================================
;; Mutation: Referential Integrity Check Evasion
;; =============================================================================

(deftest mutation-referential-integrity-coverage-test
  (testing "Tests would fail if dependency checking were skipped"
    ;; If check-referential-integrity was mutated to always return []:
    (let [errors (validators/check-referential-integrity f/missing-dependency-graph)]
      (is (not (empty? errors))
          "Missing dependencies must be caught")
      (is (some #(= :missing-dependency (:type %)) errors)
          "Error type must be :missing-dependency")))

  (testing "Tests would fail if valid refs were rejected"
    ;; If validation inverted the check:
    (let [errors (validators/check-referential-integrity f/linear-chain-graph)]
      (is (empty? errors)
          "Valid dependency references must not error"))))

;; =============================================================================
;; Mutation: Taint Propagation Logic Inversion
;; =============================================================================

(deftest mutation-taint-propagation-coverage-test
  (testing "Tests would fail if admitted status → self-admitted mapping were removed"
    ;; If admitted nodes were not marked :self-admitted:
    (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :admitted)
          taint (graph/compute-taint graph :1-abc123)]
      (is (= :self-admitted taint)
          "Admitted nodes must have :self-admitted taint")))

  (testing "Tests would fail if taint propagation were disabled"
    ;; If tainted dependencies were ignored:
    (let [graph (-> f/linear-chain-graph
                    (assoc-in [:nodes :1-aaa111 :status] :admitted)
                    (assoc-in [:nodes :1-aaa111 :taint] :self-admitted))
          dependent-taint (graph/compute-taint graph :1-bbb222)]
      (is (= :tainted dependent-taint)
          "Nodes depending on admitted must be tainted")))

  (testing "Tests would fail if clean status were misreported"
    ;; If taint was always returned as :clean:
    (let [taint (graph/compute-taint f/minimal-valid-graph :1-abc123)]
      (is (= :clean taint)
          "Clean nodes must report :clean taint"))))

;; =============================================================================
;; Mutation: Operator Inversions in Dependency Logic
;; =============================================================================

(deftest mutation-would-create-cycle-coverage-test
  (testing "Tests would fail if cycle detection inverted check"
    ;; If would-create-cycle? returned false for actual cycles:
    (is (graph/would-create-cycle? f/linear-chain-graph :1-aaa111 #{:1-ccc333})
        "Adding reverse dependency should be detected as cycle")))

(deftest mutation-cycle-prevention-boundary-test
  (testing "Tests would fail if cycle detection were completely disabled"
    ;; Direct cycle attempt:
    (is (graph/would-create-cycle? f/linear-chain-graph :1-aaa111 #{:1-ccc333})
        "Adding reverse edge in DAG creates cycle"))

  (testing "Tests would fail if valid additions were rejected"
    ;; Valid additions should not be flagged:
    (is (not (graph/would-create-cycle? f/linear-chain-graph :1-new #{:1-ccc333}))
        "Adding new leaf node should not create cycle")))

;; =============================================================================
;; Mutation: Version Increment Removal
;; =============================================================================

(deftest mutation-version-tracking-coverage-test
  (testing "Tests would fail if version wasn't incremented"
    (let [before-version (:version f/linear-chain-graph)
          result (add-node/add-node f/linear-chain-graph
                                   {:id :1-new001
                                    :type :claim
                                    :statement "Test"
                                    :dependencies #{}
                                    :scope #{}
                                    :justification :modus-ponens
                                    :depth 1
                                    :display-order 3})
          after-version (:version (:ok result))]
      (is (:ok result) "Add should succeed")
      (is (= (inc before-version) after-version)
          "Version must increment by exactly 1")))

  (testing "Tests would fail if version stayed same"
    ;; If add-node forgot to increment:
    (let [before-version (:version f/linear-chain-graph)
          result (add-node/add-node f/linear-chain-graph
                                   {:id :1-new002
                                    :type :claim
                                    :statement "Test"
                                    :dependencies #{}
                                    :scope #{}
                                    :justification :modus-ponens
                                    :depth 1
                                    :display-order 3})
          after-version (:version (:ok result))]
      (is (not (= before-version after-version))
          "Version cannot remain unchanged after mutation"))))

;; =============================================================================
;; Mutation: Error Detection Evasion
;; =============================================================================

(deftest mutation-error-detection-coverage-test
  (testing "Tests would fail if duplicate ID check were removed"
    (let [result (add-node/add-node f/linear-chain-graph
                                   {:id :1-aaa111  ; Already exists
                                    :type :claim
                                    :statement "Duplicate"
                                    :dependencies #{}
                                    :scope #{}
                                    :justification :modus-ponens
                                    :depth 1
                                    :display-order 10})]
      (is (:error result) "Duplicate ID must be rejected")
      (is (some #(= :duplicate-id (:type %)) (:error result))
          "Error type must specifically be :duplicate-id")))

  (testing "Tests would fail if missing dependency check were disabled"
    (let [result (add-node/add-node f/linear-chain-graph
                                   {:id :1-orphan
                                    :type :claim
                                    :statement "Orphaned"
                                    :dependencies #{:nonexistent}
                                    :scope #{}
                                    :justification :modus-ponens
                                    :depth 1
                                    :display-order 10})]
      (is (:error result) "Missing dependencies must be rejected")
      (is (some #(= :missing-dependencies (:type %)) (:error result))
          "Error type must be :missing-dependencies"))))

;; =============================================================================
;; Mutation: Schema Validation Evasion
;; =============================================================================

(deftest mutation-schema-validation-coverage-test
  (testing "Tests would fail if schema validation were bypassed"
    ;; Valid graph must pass:
    (is (:valid (schema/validate-schema f/linear-chain-graph))
        "Valid graph must pass schema validation"))

  (testing "Tests would fail if invalid graphs were accepted"
    ;; Invalid graph (missing required fields in node):
    (let [bad-node {:id :bad} ;; Missing required fields
          bad-graph (assoc-in f/minimal-valid-graph [:nodes :bad] bad-node)
          result (schema/validate-schema bad-graph)]
      (is (not (:valid result))
          "Graph with incomplete node must fail validation"))))

;; =============================================================================
;; Mutation: Ancestor/Descendant Query Evasion
;; =============================================================================

(deftest mutation-ancestor-descendant-coverage-test
  (testing "Tests would fail if ancestor computation were reversed"
    ;; If get-ancestors returned descendants instead:
    (let [ancestors (graph/get-ancestors f/linear-chain-graph :1-ccc333)]
      (is (contains? ancestors :1-aaa111) "Ancestors must include transitive deps")
      (is (not (contains? ancestors :1-ccc333)) "Cannot be own ancestor")))

  (testing "Tests would fail if descendant computation were reversed"
    (let [descendants (graph/get-descendants f/linear-chain-graph :1-aaa111)]
      (is (contains? descendants :1-ccc333) "Descendants must include transitive dependents")
      (is (not (contains? descendants :1-aaa111)) "Cannot be own descendant")))

  (testing "Tests would fail if transitive closure were broken"
    ;; Root has transitive descendants:
    (let [descendants (graph/get-descendants f/diamond-graph :1-aaa111)]
      (is (= 3 (count descendants))
          "Root should have 3 descendants (not including itself)")
      (is (contains? descendants :1-ddd444)
          "Transitive descendants must be included"))))

;; =============================================================================
;; Mutation: Topological Sort Evasion
;; =============================================================================

(deftest mutation-topological-sort-coverage-test
  (testing "Tests would fail if topo sort returned random order"
    (let [sorted (graph/topological-sort f/linear-chain-graph)]
      ;; Order matters: dependencies come before dependents
      (is (< (.indexOf sorted :1-aaa111) (.indexOf sorted :1-bbb222))
          "Dependencies must come before dependents")
      (is (< (.indexOf sorted :1-bbb222) (.indexOf sorted :1-ccc333))
          "Transitive order must be respected")))

  (testing "Tests would fail if topo sort inverted order"
    ;; If somehow inverted:
    (let [sorted (graph/topological-sort f/diamond-graph)]
      (is (< (.indexOf sorted :1-aaa111) (.indexOf sorted :1-ddd444))
          "Root must come before leaf"))))

;; =============================================================================
;; Mutation: Node Type Filtering Evasion
;; =============================================================================

(deftest mutation-node-type-filtering-coverage-test
  (testing "Tests would fail if node-type filtering were inverted"
    ;; If nodes-of-type returned all types instead of filtering:
    (let [claims (graph/nodes-of-type f/linear-chain-graph :claim)]
      (is (every? #(= :claim (:type %)) (vals claims))
          "All returned nodes must be :claim type")
      (is (not (empty? claims))
          "Linear chain has claim nodes")))

  (testing "Tests would fail if filters didn't exclude other types"
    (let [assumptions (graph/nodes-of-type f/linear-chain-graph :assumption)]
      (is (not (empty? assumptions))
          "Linear chain has assumption node")
      (let [claims (graph/nodes-of-type f/linear-chain-graph :claim)]
        ;; Assumptions and claims are different sets:
        (is (empty? (filter #(= :assumption (:type %)) (vals claims)))
            "Claims should not include assumptions")))))

;; =============================================================================
;; Mutation: Token Estimation Evasion
;; =============================================================================

(deftest mutation-token-estimation-coverage-test
  (testing "Tests would fail if token estimation always returned 0"
    (let [short-node (f/make-node :test :statement "Short")
          tokens (graph/estimate-node-tokens short-node)]
      (is (pos? tokens)
          "Token estimation must return positive number")))

  (testing "Tests would fail if longer statements weren't estimated higher"
    (let [short-node (f/make-node :test1 :statement "A")
          long-node (f/make-node :test2 :statement (apply str (repeat 100 "word ")))
          short-tokens (graph/estimate-node-tokens short-node)
          long-tokens (graph/estimate-node-tokens long-node)]
      (is (< short-tokens long-tokens)
          "Longer statements must estimate to more tokens"))))
