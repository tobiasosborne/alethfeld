(ns validate-graph.edge-cases-test
  "Tests for edge cases: empty graphs, large graphs, unicode, etc."
  (:require [clojure.test :refer [deftest testing is are]]
            [validate-graph.schema :as schema]
            [validate-graph.validators :as v]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Empty and Minimal Graph Tests
;; =============================================================================

(deftest empty-nodes-graph-schema-valid-test
  (testing "Graph with empty :nodes passes schema validation"
    (let [result (schema/validate-schema fix/empty-nodes-graph)]
      (is (:valid result)))))

(deftest empty-nodes-graph-semantic-valid-test
  (testing "Graph with empty :nodes passes semantic validation"
    (let [result (v/validate-semantics fix/empty-nodes-graph)]
      (is (:valid result)))))

(deftest single-assumption-valid-test
  (testing "Single assumption node is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :0-only
                                 :type :assumption
                                 :justification :assumption
                                 :depth 0)])
          schema-result (schema/validate-schema graph)
          semantic-result (v/validate-semantics graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest single-claim-no-deps-valid-test
  (testing "Single claim with no dependencies is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-only
                                 :deps #{})])
          schema-result (schema/validate-schema graph)
          semantic-result (v/validate-semantics graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest empty-symbols-valid-test
  (testing "Empty symbols map is valid"
    (is (= {} (:symbols fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest empty-lemmas-valid-test
  (testing "Empty lemmas map is valid"
    (is (= {} (:lemmas fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest empty-external-refs-valid-test
  (testing "Empty external-refs map is valid"
    (is (= {} (:external-refs fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest empty-archived-nodes-valid-test
  (testing "Empty archived-nodes map is valid"
    (is (= {} (:archived-nodes fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest empty-obligations-valid-test
  (testing "Empty obligations vector is valid"
    (is (= [] (:obligations fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

;; =============================================================================
;; Large and Deep Graph Tests
;; =============================================================================

(deftest deeply-nested-graph-valid-test
  (testing "Deeply nested graph (10 levels) passes validation"
    (let [schema-result (schema/validate-schema fix/deeply-nested-graph)
          semantic-result (v/validate-semantics fix/deeply-nested-graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest wide-graph-valid-test
  (testing "Wide graph with many siblings passes validation"
    (let [schema-result (schema/validate-schema fix/wide-graph)
          semantic-result (v/validate-semantics fix/wide-graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest large-graph-100-nodes-test
  (testing "Graph with 100+ nodes passes validation"
    (let [nodes (cons (fix/make-node :0-root
                                     :type :assumption
                                     :justification :assumption
                                     :depth 0)
                      (for [i (range 100)]
                        (fix/make-node (keyword (str "1-node" i))
                                       :deps #{:0-root}
                                       :order i)))
          graph (fix/make-graph nodes)
          schema-result (schema/validate-schema graph)
          semantic-result (v/validate-semantics graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest graph-with-many-lemmas-test
  (testing "Graph with many lemmas passes validation"
    (let [lemmas (into {}
                       (for [i (range 20)]
                         [(str "lem-" i)
                          {:id (str "lem-" i)
                           :name (str "Lemma " i)
                           :statement (str "Statement " i)
                           :content-hash "0123456789abcdef"
                           :root-node (keyword (str "archived-" i))
                           :status :proven
                           :taint :clean
                           :extracted-nodes #{(keyword (str "archived-" i))}}]))
          archived (into {}
                         (for [i (range 20)]
                           [(keyword (str "archived-" i))
                            (fix/make-node (keyword (str "archived-" i)))]))
          graph (-> fix/minimal-valid-graph
                    (assoc :lemmas lemmas)
                    (assoc :archived-nodes archived))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest graph-with-many-external-refs-test
  (testing "Graph with many external refs passes validation"
    (let [ext-refs (into {}
                         (for [i (range 20)]
                           [(str "ext-" i)
                            {:id (str "ext-" i)
                             :doi (str "10.1234/test" i)
                             :claimed-statement (str "Claim " i)
                             :verification-status :verified}]))
          graph (assoc fix/minimal-valid-graph :external-refs ext-refs)
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; Unicode and Special Characters Tests
;; =============================================================================

(deftest unicode-statement-valid-test
  (testing "Unicode in statements is valid"
    (let [result (schema/validate-schema fix/unicode-statement-graph)]
      (is (:valid result)))))

(deftest greek-letters-in-statement-test
  (testing "Greek letters in statement are valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-greek
                                 :statement "Let α, β, γ ∈ ℝ and ∀ε>0 ∃δ>0: |x-a|<δ ⟹ |f(x)-L|<ε")])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest math-symbols-in-statement-test
  (testing "Mathematical symbols in statement are valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-math
                                 :statement "∫₀^∞ e^(-x²) dx = √π/2 and ∑_{n=1}^∞ 1/n² = π²/6")])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest long-statement-valid-test
  (testing "Very long statement is valid"
    (let [result (schema/validate-schema fix/long-statement-graph)]
      (is (:valid result)))))

(deftest latex-commands-in-statement-test
  (testing "LaTeX commands in statement are valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-latex
                                 :statement "\\frac{d}{dx}\\left(\\int_{a}^{x} f(t)\\,dt\\right) = f(x)")])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest multiline-statement-test
  (testing "Multiline statement is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-multi
                                 :statement "Line 1: f(x) = x²\nLine 2: g(x) = 2x\nLine 3: (f∘g)(x) = 4x²")])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

;; =============================================================================
;; Nil and Missing Values Tests
;; =============================================================================

(deftest nil-parent-valid-test
  (testing "Nil parent (root node) is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (nil? (:parent node)))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest nil-revision-of-valid-test
  (testing "Nil revision-of is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (nil? (get-in node [:provenance :revision-of])))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest nil-proof-graph-id-in-lemma-valid-test
  (testing "Nil proof-graph-id in lemma is valid"
    (let [graph (-> fix/minimal-valid-graph
                    (assoc :lemmas {"lem-001" {:id "lem-001"
                                               :name "Test"
                                               :statement "stmt"
                                               :content-hash "0123456789abcdef"
                                               :root-node :1-abc123
                                               :status :proven
                                               :taint :clean
                                               :extracted-nodes #{:1-abc123}
                                               :proof-graph-id nil}}))
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest optional-introduces-not-present-test
  (testing "Optional :introduces field not present on non-local-assume is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (not (contains? node :introduces)))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest optional-discharges-not-present-test
  (testing "Optional :discharges field not present on non-local-discharge is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (not (contains? node :discharges)))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest optional-lemma-id-not-present-test
  (testing "Optional :lemma-id field not present on non-lemma-ref is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (not (contains? node :lemma-id)))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest optional-external-id-not-present-test
  (testing "Optional :external-id field not present on non-external-ref is valid"
    (let [node (get-in fix/minimal-valid-graph [:nodes :1-abc123])]
      (is (not (contains? node :external-id)))
      (let [result (schema/validate-schema fix/minimal-valid-graph)]
        (is (:valid result))))))

(deftest optional-constraints-in-symbol-test
  (testing "Optional :constraints in symbol can be present or absent"
    (let [sym-without {:id :sym-x
                       :name "x"
                       :type "Real"
                       :tex "x"
                       :scope :global
                       :introduced-at :1-abc123}
          sym-with (assoc sym-without :constraints "x > 0")
          graph1 (assoc fix/minimal-valid-graph :symbols {:sym-x sym-without})
          graph2 (assoc fix/minimal-valid-graph :symbols {:sym-x sym-with})]
      (is (:valid (schema/validate-schema graph1)))
      (is (:valid (schema/validate-schema graph2))))))

;; =============================================================================
;; Boundary Value Tests
;; =============================================================================

(deftest version-one-valid-test
  (testing "Version 1 is valid (minimum)"
    (is (= 1 (:version fix/minimal-valid-graph)))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest large-version-number-test
  (testing "Large version number is valid"
    (let [graph (assoc fix/minimal-valid-graph :version 999999)
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest depth-zero-valid-test
  (testing "Depth 0 is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :0-root :depth 0 :type :assumption :justification :assumption)])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest large-depth-valid-test
  (testing "Large depth is valid"
    (let [graph (fix/make-graph
                 [(fix/make-node :99-deep :depth 99)])
          result (schema/validate-schema graph)]
      (is (:valid result)))))

(deftest display-order-zero-valid-test
  (testing "Display order 0 is valid"
    (is (= 0 (get-in fix/minimal-valid-graph [:nodes :1-abc123 :display-order])))
    (let [result (schema/validate-schema fix/minimal-valid-graph)]
      (is (:valid result)))))

(deftest negative-display-order-valid-test
  (testing "Negative display order is valid (for reordering)"
    (let [graph (fix/make-graph
                 [(fix/make-node :1-neg :display-order -5)])
          result (schema/validate-schema graph)]
      ;; display-order is just :int, no constraints
      (is (:valid result)))))

;; =============================================================================
;; Combined Validation Tests
;; =============================================================================

(deftest all-node-types-full-validation-test
  (testing "Graph with all node types passes full validation"
    (let [schema-result (schema/validate-schema fix/all-node-types-graph)
          semantic-result (v/validate-semantics fix/all-node-types-graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest all-justifications-full-validation-test
  (testing "Graph with all justifications passes full validation"
    (let [schema-result (schema/validate-schema fix/all-justifications-graph)
          semantic-result (v/validate-semantics fix/all-justifications-graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))

(deftest scoped-graph-full-validation-test
  (testing "Scoped graph passes full validation"
    (let [schema-result (schema/validate-schema fix/scoped-graph)
          semantic-result (v/validate-semantics fix/scoped-graph)]
      (is (:valid schema-result))
      (is (:valid semantic-result)))))
