(ns alethfeld.integration-test
  "Integration tests for complete proof graph workflows."
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.init :as init]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.ops.delete-node :as delete-node]
            [alethfeld.ops.replace-node :as replace-node]
            [alethfeld.ops.extract-lemma :as extract-lemma]
            [alethfeld.ops.external-ref :as external-ref]
            [alethfeld.graph :as graph]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as validators]))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn make-node
  "Create a partial node for add-node."
  [id & {:keys [type statement deps scope justification depth order
                introduces discharges external-id]
         :or {type :claim
              statement "Test statement"
              deps #{}
              scope #{}
              justification :modus-ponens
              depth 1
              order 0}}]
  (cond-> {:id id
           :type type
           :statement statement
           :dependencies deps
           :scope scope
           :justification justification
           :depth depth
           :display-order order}
    introduces (assoc :introduces introduces)
    discharges (assoc :discharges discharges)
    external-id (assoc :external-id external-id)))

(defn assert-ok [result]
  (is (:ok result) (str "Expected success, got: " (pr-str (:error result))))
  (:ok result))

(defn assert-error [result expected-type]
  (is (:error result) "Expected error")
  (when expected-type
    (is (some #(= expected-type (:type %)) (:error result))
        (str "Expected error type " expected-type ", got: " (pr-str (:error result)))))
  result)

;; =============================================================================
;; Full Workflow Integration Tests
;; =============================================================================

(deftest complete-proof-workflow-test
  (testing "Complete workflow: init -> add nodes -> verify -> extract lemma"
    (let [;; Step 1: Initialize graph
          init-result (init/init-graph "For all $n \\in \\mathbb{N}$, $n^2 \\geq 0$")
          graph (assert-ok init-result)
          _ (is (= 1 (:version graph)))

          ;; Step 2: Add assumption node
          assume-node (make-node :0-A1
                                 :type :assumption
                                 :statement "Let $n \\in \\mathbb{N}$"
                                 :justification :assumption
                                 :depth 0
                                 :order 0)
          graph (assert-ok (add-node/add-node graph assume-node))
          _ (is (= 2 (:version graph)))

          ;; Step 3: Add proof step depending on assumption
          step1-node (make-node :1-step1
                                :type :claim
                                :statement "$n^2 = n \\cdot n$"
                                :deps #{:0-A1}
                                :justification :definition-expansion
                                :order 1)
          graph (assert-ok (add-node/add-node graph step1-node))

          ;; Step 4: Add another step
          step2-node (make-node :1-step2
                                :type :claim
                                :statement "$n \\cdot n \\geq 0$ since $n \\geq 0$"
                                :deps #{:1-step1}
                                :justification :algebraic-rewrite
                                :order 2)
          graph (assert-ok (add-node/add-node graph step2-node))

          ;; Step 5: Add QED
          qed-node (make-node :1-qed
                              :type :qed
                              :statement "$n^2 \\geq 0$"
                              :deps #{:1-step2}
                              :justification :qed
                              :order 3)
          graph (assert-ok (add-node/add-node graph qed-node))
          _ (is (= 5 (:version graph)))
          _ (is (= 4 (count (:nodes graph))))

          ;; Step 6: Verify all nodes
          graph (assert-ok (update-status/update-status graph :1-step1 :verified))
          graph (assert-ok (update-status/update-status graph :1-step2 :verified))
          graph (assert-ok (update-status/update-status graph :1-qed :verified))

          ;; Step 7: Extract as lemma
          extract-result (extract-lemma/extract-lemma graph :1-qed "L1-squares")
          graph (assert-ok extract-result)
          lemma (:lemma extract-result)]

      ;; Verify final state
      (is (contains? (:lemmas graph) "L1-squares"))
      (is (= :1-qed (:root-node lemma)))
      (is (= :proven (:status lemma)))
      (is (= :clean (:taint lemma)))

      ;; Extracted nodes should be archived
      (is (contains? (:archived-nodes graph) :1-qed))
      (is (contains? (:archived-nodes graph) :1-step2))
      (is (contains? (:archived-nodes graph) :1-step1))

      ;; Assumption should remain (external dependency)
      (is (contains? (:nodes graph) :0-A1))

      ;; Lemma-ref should exist
      (is (some #(= :lemma-ref (:type %)) (vals (:nodes graph))))

      ;; Graph should still validate
      (is (:valid (schema/validate-schema graph))))))

(deftest reject-and-replace-workflow-test
  (testing "Workflow: add node -> reject -> replace"
    (let [;; Initialize with assumption
          graph (assert-ok (init/init-graph "Test theorem"))
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))

          ;; Add a flawed claim
          bad-claim (make-node :1-bad
                               :statement "Incorrect claim"
                               :deps #{:0-A1}
                               :order 1)
          graph (assert-ok (add-node/add-node graph bad-claim))

          ;; Reject it
          graph (assert-ok (update-status/update-status graph :1-bad :rejected))
          _ (is (= :rejected (:status (graph/get-node graph :1-bad))))

          ;; Replace with corrected version
          good-claim (make-node :1-good
                                :statement "Corrected claim"
                                :deps #{:0-A1}
                                :order 1)
          graph (assert-ok (replace-node/replace-node graph :1-bad good-claim))]

      ;; Old node should be archived
      (is (contains? (:archived-nodes graph) :1-bad))
      (is (not (contains? (:nodes graph) :1-bad)))

      ;; New node should exist with revision-of
      (is (contains? (:nodes graph) :1-good))
      (is (= :1-bad (get-in graph [:nodes :1-good :provenance :revision-of])))

      ;; Graph should validate
      (is (:valid (schema/validate-schema graph))))))

(deftest scoped-proof-workflow-test
  (testing "Workflow with local assumptions and discharge"
    (let [graph (assert-ok (init/init-graph "Test with scope"))

          ;; Add global assumption
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))

          ;; Add local assumption (suppose P)
          local-assume (make-node :1-LA
                                  :type :local-assume
                                  :statement "Suppose $P$"
                                  :justification :local-assumption
                                  :introduces "P"
                                  :deps #{:0-A1}
                                  :order 1)
          graph (assert-ok (add-node/add-node graph local-assume))

          ;; Add step using local assumption (in scope)
          step (make-node :1-step
                          :statement "Under $P$, we have $Q$"
                          :deps #{:1-LA}
                          :scope #{:1-LA}
                          :order 2)
          graph (assert-ok (add-node/add-node graph step))

          ;; Discharge the local assumption
          discharge (make-node :1-discharge
                               :type :local-discharge
                               :statement "$P \\Rightarrow Q$"
                               :justification :discharge
                               :discharges :1-LA
                               :deps #{:1-step}
                               :scope #{:1-LA}
                               :order 3)
          graph (assert-ok (add-node/add-node graph discharge))]

      ;; Verify scope is tracked
      (is (= #{:1-LA} (:scope (graph/get-node graph :1-step))))
      (is (= :1-LA (:discharges (graph/get-node graph :1-discharge))))

      ;; Verify all nodes exist
      (is (= 4 (count (:nodes graph))))

      ;; Graph should validate
      (is (:valid (schema/validate-schema graph))))))

(deftest taint-propagation-workflow-test
  (testing "Taint propagates through admitted nodes"
    (let [graph (assert-ok (init/init-graph "Test taint"))

          ;; Add assumption
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))

          ;; Add admitted step
          admitted (make-node :1-admitted
                              :statement "Admitted claim"
                              :deps #{:0-A1}
                              :justification :admitted
                              :order 1)
          graph (assert-ok (add-node/add-node graph admitted))
          graph (assert-ok (update-status/update-status graph :1-admitted :admitted))

          ;; Add dependent step
          dependent (make-node :1-dep
                               :statement "Depends on admitted"
                               :deps #{:1-admitted}
                               :order 2)
          graph (assert-ok (add-node/add-node graph dependent))]

      ;; Admitted node should have self-admitted taint
      (is (= :self-admitted (:taint (graph/get-node graph :1-admitted))))

      ;; Dependent node should be tainted
      (is (= :tainted (:taint (graph/get-node graph :1-dep))))

      ;; Recompute should preserve these values
      (let [recomputed (graph/recompute-all-taints graph)]
        (is (= :self-admitted (:taint (graph/get-node recomputed :1-admitted))))
        (is (= :tainted (:taint (graph/get-node recomputed :1-dep))))))))

(deftest external-reference-workflow-test
  (testing "Add and use external references"
    (let [graph (assert-ok (init/init-graph "Using external results"))

          ;; Add external reference
          ext-ref {:id "cauchy-schwarz"
                   :doi "10.1000/example"
                   :claimed-statement "Cauchy-Schwarz inequality"
                   :verification-status :pending}
          graph (assert-ok (external-ref/add-external-ref graph ext-ref))

          ;; Add node using external ref
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))

          ext-node (make-node :1-ext
                              :type :external-ref
                              :statement "By Cauchy-Schwarz..."
                              :deps #{:0-A1}
                              :justification :external-application
                              :external-id "cauchy-schwarz"
                              :order 1)
          graph (assert-ok (add-node/add-node graph ext-node))]

      ;; External ref should exist
      (is (contains? (:external-refs graph) "cauchy-schwarz"))

      ;; Node should reference it
      (is (= "cauchy-schwarz" (:external-id (graph/get-node graph :1-ext))))

      ;; Graph should validate
      (is (:valid (schema/validate-schema graph))))))

;; =============================================================================
;; Error Handling Integration Tests
;; =============================================================================

(deftest error-handling-test
  (testing "Proper error handling across operations"
    (let [graph (assert-ok (init/init-graph "Error test"))
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))]

      ;; Cannot add duplicate node
      (assert-error (add-node/add-node graph assume) :duplicate-id)

      ;; Cannot add node with missing dependency
      (let [bad-node (make-node :1-bad :deps #{:nonexistent})]
        (assert-error (add-node/add-node graph bad-node) :missing-dependencies))

      ;; Cannot replace non-rejected node
      (let [replacement (make-node :1-new)]
        (assert-error (replace-node/replace-node graph :0-A1 replacement) :not-rejected))

      ;; Cannot extract unverified nodes (proposed status)
      (let [proposed (make-node :1-proposed :deps #{:0-A1} :order 1)
            g (assert-ok (add-node/add-node graph proposed))]
        (assert-error (extract-lemma/extract-lemma g :1-proposed "L-fail") :node-not-verified)))))

(deftest delete-node-test
  (testing "Cannot delete node with dependents"
    (let [graph (assert-ok (init/init-graph "Delete test"))

          ;; Build chain: A -> B -> C
          a (make-node :0-A :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph a))

          b (make-node :1-B :deps #{:0-A} :order 1)
          graph (assert-ok (add-node/add-node graph b))

          c (make-node :1-C :deps #{:1-B} :order 2)
          graph (assert-ok (add-node/add-node graph c))]

      ;; Cannot delete middle node that has dependents
      (assert-error (delete-node/delete-node graph :1-B) :has-dependents)

      ;; Can delete leaf node
      (let [graph (assert-ok (delete-node/delete-node graph :1-C))]
        (is (contains? (:archived-nodes graph) :1-C))
        (is (not (contains? (:nodes graph) :1-C)))

        ;; Now can delete B
        (let [graph (assert-ok (delete-node/delete-node graph :1-B))]
          (is (contains? (:archived-nodes graph) :1-B))
          (is (not (contains? (:nodes graph) :1-B)))

          ;; Graph should validate
          (is (:valid (schema/validate-schema graph))))))))

;; =============================================================================
;; Version and Metadata Tests
;; =============================================================================

(deftest version-tracking-test
  (testing "Version increments correctly"
    (let [graph (assert-ok (init/init-graph "Version test"))
          _ (is (= 1 (:version graph)))

          ;; Each mutation increments version
          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))
          _ (is (= 2 (:version graph)))

          graph (assert-ok (update-status/update-status graph :0-A1 :verified))
          _ (is (= 3 (:version graph)))

          graph (assert-ok (delete-node/delete-node graph :0-A1))
          _ (is (= 4 (:version graph)))]

      (is (= 4 (:version graph))))))

(deftest context-budget-tracking-test
  (testing "Context budget is updated"
    (let [graph (assert-ok (init/init-graph "Budget test"))
          initial-estimate (get-in graph [:metadata :context-budget :current-estimate])

          ;; Add a node with long statement
          assume (make-node :0-A1
                            :type :assumption
                            :justification :assumption
                            :depth 0
                            :statement (apply str (repeat 500 "x")))
          graph (assert-ok (add-node/add-node graph assume))
          new-estimate (get-in graph [:metadata :context-budget :current-estimate])]

      ;; Estimate should increase
      (is (> new-estimate initial-estimate)))))

;; =============================================================================
;; Full Validation Tests
;; =============================================================================

(deftest full-semantic-validation-test
  (testing "Complete graph passes all validators"
    (let [graph (assert-ok (init/init-graph "Full validation test"))

          assume (make-node :0-A1 :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume))

          step (make-node :1-step :deps #{:0-A1} :order 1)
          graph (assert-ok (add-node/add-node graph step))

          graph (assert-ok (update-status/update-status graph :1-step :verified))]

      ;; Schema validation
      (is (:valid (schema/validate-schema graph)))

      ;; Full semantic validation
      (is (:valid (validators/validate-semantics graph))))))
