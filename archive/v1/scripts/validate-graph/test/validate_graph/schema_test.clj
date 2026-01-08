(ns validate-graph.schema-test
  "Tests for Malli schema validation."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.schema :as schema]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Valid Graph Structure Tests
;; =============================================================================

(deftest valid-minimal-graph-test
  (testing "Minimal valid graph passes validation"
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result) (str "Expected valid but got errors: " (:errors result))))))

(deftest valid-linear-chain-test
  (testing "Linear chain graph passes validation"
    (let [result (schema/validate-schema fix/linear-chain-graph)]
      (is (:valid result)))))

(deftest valid-diamond-graph-test
  (testing "Diamond pattern graph passes validation"
    (let [result (schema/validate-schema fix/diamond-graph)]
      (is (:valid result)))))

(deftest valid-scoped-graph-test
  (testing "Graph with local-assume/discharge passes validation"
    (let [result (schema/validate-schema fix/scoped-graph)]
      (is (:valid result)))))

(deftest valid-all-node-types-test
  (testing "Graph with all node types passes validation"
    (let [result (schema/validate-schema fix/all-node-types-graph)]
      (is (:valid result)))))

(deftest valid-all-justifications-test
  (testing "Graph with various justifications passes validation"
    (let [result (schema/validate-schema fix/all-justifications-graph)]
      (is (:valid result)))))

;; =============================================================================
;; Invalid Node Structure Tests
;; =============================================================================

(deftest invalid-node-type-test
  (testing "Invalid node type fails validation"
    (let [result (schema/validate-schema fix/invalid-node-type-graph)]
      (is (not (:valid result)))
      (is (some? (:errors result))))))

(deftest invalid-justification-test
  (testing "Invalid justification fails validation"
    (let [result (schema/validate-schema fix/invalid-justification-graph)]
      (is (not (:valid result))))))

(deftest invalid-status-test
  (testing "Invalid status fails validation"
    (let [result (schema/validate-schema fix/invalid-status-graph)]
      (is (not (:valid result))))))

(deftest invalid-taint-test
  (testing "Invalid taint value fails validation"
    (let [result (schema/validate-schema fix/invalid-taint-graph)]
      (is (not (:valid result))))))

(deftest missing-statement-test
  (testing "Missing statement fails validation"
    (let [result (schema/validate-schema fix/missing-statement-graph)]
      (is (not (:valid result))))))

(deftest missing-id-test
  (testing "Missing node id fails validation"
    (let [graph (assoc-in fix/minimal-valid-graph [:nodes :1-abc123]
                          (dissoc (get-in fix/minimal-valid-graph [:nodes :1-abc123]) :id))]
      (let [result (schema/validate-schema graph)]
        (is (not (:valid result)))))))

(deftest wrong-deps-type-test
  (testing "Dependencies as vector instead of set fails validation"
    (let [result (schema/validate-schema fix/wrong-deps-type-graph)]
      (is (not (:valid result))))))

(deftest negative-depth-test
  (testing "Negative depth fails validation"
    (let [result (schema/validate-schema fix/negative-depth-graph)]
      (is (not (:valid result))))))

(deftest invalid-content-hash-test
  (testing "Invalid content hash format fails validation"
    (let [result (schema/validate-schema fix/invalid-content-hash-graph)]
      (is (not (:valid result))))))

;; =============================================================================
;; Metadata Validation Tests
;; =============================================================================

(deftest invalid-proof-mode-test
  (testing "Invalid proof mode fails validation"
    (let [result (schema/validate-schema fix/invalid-proof-mode-graph)]
      (is (not (:valid result))))))

(deftest valid-proof-modes-test
  (testing "All valid proof modes pass"
    (doseq [mode [:strict-mathematics :formal-physics :algebraic-derivation]]
      (let [graph (assoc-in fix/minimal-valid-graph [:metadata :proof-mode] mode)
            result (schema/validate-schema graph)]
        (is (:valid result) (str "Mode " mode " should be valid"))))))

(deftest missing-graph-id-test
  (testing "Missing graph-id fails validation"
    (let [graph (dissoc fix/minimal-valid-graph :graph-id)
          result (schema/validate-schema graph)]
      (is (not (:valid result))))))

(deftest missing-version-test
  (testing "Missing version fails validation"
    (let [graph (dissoc fix/minimal-valid-graph :version)
          result (schema/validate-schema graph)]
      (is (not (:valid result))))))

(deftest zero-version-test
  (testing "Zero version fails validation (must be >= 1)"
    (let [graph (assoc fix/minimal-valid-graph :version 0)
          result (schema/validate-schema graph)]
      (is (not (:valid result))))))

;; =============================================================================
;; Symbol Validation Tests
;; =============================================================================

(deftest valid-symbol-test
  (testing "Valid symbol passes validation"
    (let [graph (assoc fix/minimal-valid-graph :symbols
                       {:sym-x {:id :sym-x
                                :name "x"
                                :type "Real"
                                :tex "\\mathbf{x}"
                                :scope :global
                                :introduced-at :1-abc123}})
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest symbol-missing-name-test
  (testing "Symbol missing name fails validation"
    (let [graph (assoc fix/minimal-valid-graph :symbols
                       {:sym-x {:id :sym-x
                                :type "Real"
                                :tex "\\mathbf{x}"
                                :scope :global
                                :introduced-at :1-abc123}})
          result (schema/validate-schema graph)]
      (is (not (:valid result))))))

(deftest symbol-with-constraints-test
  (testing "Symbol with optional constraints passes"
    (let [graph (assoc fix/minimal-valid-graph :symbols
                       {:sym-x {:id :sym-x
                                :name "x"
                                :type "Real"
                                :tex "\\mathbf{x}"
                                :constraints "x > 0"
                                :scope :global
                                :introduced-at :1-abc123}})
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; External Refs Validation Tests
;; =============================================================================

(deftest valid-external-ref-doi-test
  (testing "External ref with DOI passes validation"
    (let [graph (assoc fix/minimal-valid-graph :external-refs
                       {"ext-001" {:id "ext-001"
                                   :doi "10.1234/test.2024"
                                   :claimed-statement "Some claim"
                                   :verification-status :pending}})
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest valid-external-ref-arxiv-test
  (testing "External ref with arXiv passes validation"
    (let [graph (assoc fix/minimal-valid-graph :external-refs
                       {"ext-001" {:id "ext-001"
                                   :arxiv "2301.12345"
                                   :claimed-statement "Some claim"
                                   :verification-status :verified}})
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest external-ref-all-statuses-test
  (testing "All external verification statuses are valid"
    (doseq [status [:pending :verified :mismatch :not-found :metadata-only]]
      (let [graph (assoc fix/minimal-valid-graph :external-refs
                         {"ext-001" {:id "ext-001"
                                     :doi "10.1234/test"
                                     :claimed-statement "Some claim"
                                     :verification-status status}})
            result (schema/validate-schema graph)]
        (is (:valid result) (str "Status " status " should be valid"))))))

(deftest external-ref-with-bibdata-test
  (testing "External ref with bibdata passes"
    (let [graph (assoc fix/minimal-valid-graph :external-refs
                       {"ext-001" {:id "ext-001"
                                   :doi "10.1234/test"
                                   :claimed-statement "Some claim"
                                   :verification-status :verified
                                   :verified-statement "Verified statement"
                                   :bibdata {:authors ["Author One" "Author Two"]
                                             :title "Paper Title"
                                             :year 2024
                                             :journal "Some Journal"}
                                   :notes "Note about this ref"}})
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; Lemma Validation Tests
;; =============================================================================

(deftest valid-lemma-test
  (testing "Valid lemma passes validation"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc :lemmas
                           {"lem-001" {:id "lem-001"
                                       :name "Test Lemma"
                                       :statement "Lemma statement"
                                       :content-hash "abcdef0123456789"
                                       :root-node :archived-root
                                       :status :proven
                                       :taint :clean
                                       :extracted-nodes #{:archived-root}
                                       :proof-graph-id nil}})
                    (assoc :archived-nodes
                           {:archived-root (fix/make-node :archived-root)}))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest lemma-all-statuses-test
  (testing "All lemma statuses are valid"
    (doseq [status [:pending :proven :tainted]]
      (let [graph (-> fix/minimal-valid-graph
                      (assoc :lemmas
                             {"lem-001" {:id "lem-001"
                                         :name "Test"
                                         :statement "Statement"
                                         :content-hash "abcdef0123456789"
                                         :root-node :archived-root
                                         :status status
                                         :taint :clean
                                         :extracted-nodes #{:archived-root}}})
                      (assoc :archived-nodes
                             {:archived-root (fix/make-node :archived-root)}))
            result (schema/validate-schema graph)]
        (is (:valid result) (str "Lemma status " status " should be valid"))))))

;; =============================================================================
;; Provenance Validation Tests
;; =============================================================================

(deftest valid-provenance-test
  (testing "All created-by values are valid"
    (doseq [created-by [:prover :orchestrator :extraction]]
      (let [node (assoc-in (fix/make-node :1-test) [:provenance :created-by] created-by)
            graph (assoc-in fix/minimal-valid-graph [:nodes :1-test] node)
            result (schema/validate-schema graph)]
        (is (:valid result) (str "created-by " created-by " should be valid"))))))

(deftest provenance-with-revision-test
  (testing "Provenance with revision-of passes"
    (let [archived (fix/make-node :old-node)
          new-node (assoc-in (fix/make-node :1-new) [:provenance :revision-of] :old-node)
          graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-new] new-node)
                    (assoc-in [:archived-nodes :old-node] archived))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; Obligation Validation Tests
;; =============================================================================

(deftest valid-obligation-test
  (testing "Valid obligation passes validation"
    (let [graph (assoc fix/minimal-valid-graph :obligations
                       [{:node-id :1-abc123
                         :claim "Some claim"
                         :context {:assumptions []
                                   :scope []}}])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; Node Type-Specific Field Tests
;; =============================================================================

(deftest local-assume-with-introduces-test
  (testing "Local-assume with introduces field passes"
    (let [node (fix/make-node :1-assume
                              :type :local-assume
                              :justification :local-assumption
                              :introduces "P holds")
          graph (assoc-in fix/minimal-valid-graph [:nodes :1-assume] node)
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest local-discharge-with-discharges-test
  (testing "Local-discharge with discharges field passes"
    (let [assume-node (fix/make-node :1-assume
                                     :type :local-assume
                                     :justification :local-assumption
                                     :introduces "P")
          discharge-node (fix/make-node :1-discharge
                                        :type :local-discharge
                                        :justification :discharge
                                        :discharges :1-assume
                                        :deps #{:1-assume}
                                        :scope #{:1-assume})
          graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-assume] assume-node)
                    (assoc-in [:nodes :1-discharge] discharge-node))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest lemma-ref-with-lemma-id-test
  (testing "Lemma-ref with lemma-id field passes"
    (let [node (fix/make-node :1-lemref
                              :type :lemma-ref
                              :justification :lemma-application
                              :lemma-id "lem-001")
          graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-lemref] node)
                    (assoc :lemmas {"lem-001" {:id "lem-001"
                                               :name "Test"
                                               :statement "stmt"
                                               :content-hash "0123456789abcdef"
                                               :root-node :archived
                                               :status :proven
                                               :taint :clean
                                               :extracted-nodes #{:archived}}})
                    (assoc :archived-nodes {:archived (fix/make-node :archived)}))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest external-ref-node-with-external-id-test
  (testing "External-ref node with external-id field passes"
    (let [node (fix/make-node :1-extref
                              :type :external-ref
                              :justification :external-application
                              :external-id "ext-001")
          graph (-> fix/minimal-valid-graph
                    (assoc-in [:nodes :1-extref] node)
                    (assoc :external-refs {"ext-001" {:id "ext-001"
                                                      :doi "10.1234/test"
                                                      :claimed-statement "claim"
                                                      :verification-status :verified}}))
          result (schema/validate-schema graph)]
      (is (:valid result)))))
