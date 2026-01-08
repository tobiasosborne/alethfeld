(ns alethfeld.ops.extract-lemma-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.extract-lemma :as extract-lemma]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def extractable-graph
  "Graph with a verified chain suitable for extraction."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-step1
                              :deps #{:1-assume}
                              :order 1)
                 (f/make-node :1-step2
                              :deps #{:1-step1}
                              :order 2)
                 (f/make-node :1-result
                              :deps #{:1-step2}
                              :order 3)]))

(def not-verified-graph
  "Graph with an unverified node."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-step1
                              :deps #{:1-assume}
                              :status :proposed  ; Not verified!
                              :order 1)
                 (f/make-node :1-step2
                              :deps #{:1-step1}
                              :order 2)]))

(def with-external-dep-graph
  "Graph where internal node has external dependent."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-step1
                              :deps #{:1-assume}
                              :order 1)
                 (f/make-node :1-step2
                              :deps #{:1-step1}
                              :order 2)
                 (f/make-node :1-external
                              :deps #{:1-step1}  ; Depends on internal node
                              :order 3)]))

;; =============================================================================
;; Basic Extraction Tests
;; =============================================================================

(deftest extract-lemma-basic-test
  (testing "Extract simple verified chain"
    (let [result (extract-lemma/extract-lemma extractable-graph :1-result "L1-test")]
      (is (:ok result) (str "Expected success, got: " result))
      (let [graph (:ok result)
            lemma (:lemma result)]
        ;; Lemma was created
        (is (= "L1-test" (:id lemma)))
        (is (= :1-result (:root-node lemma)))
        (is (= :proven (:status lemma)))
        (is (= :clean (:taint lemma)))

        ;; Graph has lemma entry
        (is (contains? (:lemmas graph) "L1-test"))

        ;; Extracted nodes are archived
        (is (contains? (:archived-nodes graph) :1-result))
        (is (contains? (:archived-nodes graph) :1-step2))
        (is (contains? (:archived-nodes graph) :1-step1))

        ;; Extracted nodes removed from active nodes
        (is (not (contains? (:nodes graph) :1-result)))
        (is (not (contains? (:nodes graph) :1-step2)))
        (is (not (contains? (:nodes graph) :1-step1)))

        ;; Assumption remains (external dependency)
        (is (contains? (:nodes graph) :1-assume))

        ;; Lemma-ref node was added
        (is (some #(= :lemma-ref (:type (val %))) (:nodes graph)))))))

(deftest extract-lemma-with-explicit-nodes-test
  (testing "Extract with explicit node set"
    (let [result (extract-lemma/extract-lemma
                  extractable-graph
                  :1-step2
                  "L2-partial"
                  #{:1-step1 :1-step2})]
      (is (:ok result))
      (let [lemma (:lemma result)]
        (is (= #{:1-step1 :1-step2} (:extracted-nodes lemma)))
        (is (= :1-step2 (:root-node lemma)))))))

;; =============================================================================
;; Validation Tests
;; =============================================================================

(deftest extract-lemma-validation-tests
  (testing "Reject extraction of unverified nodes"
    (let [result (extract-lemma/extract-lemma not-verified-graph :1-step2 "L-fail")]
      (is (:error result))
      (is (some #(= :node-not-verified (:type %)) (:error result)))))

  (testing "Reject extraction where internal node has external dependent"
    ;; Try to extract just :1-step1 and :1-step2, but :1-external depends on :1-step1
    (let [result (extract-lemma/extract-lemma
                  with-external-dep-graph
                  :1-step2
                  "L-fail"
                  #{:1-step1 :1-step2})]
      (is (:error result))
      (is (some #(= :external-dependency-on-non-root (:type %)) (:error result)))))

  (testing "Reject non-existent root node"
    (let [result (extract-lemma/extract-lemma extractable-graph :nonexistent "L-fail")]
      (is (:error result))
      (is (some #(= :node-not-found (:type %)) (:error result)))))

  (testing "Reject root not in extraction set"
    (let [result (extract-lemma/extract-lemma
                  extractable-graph
                  :1-result
                  "L-fail"
                  #{:1-step1 :1-step2})]  ; root not included
      (is (:error result))
      (is (some #(= :root-not-in-set (:type %)) (:error result))))))

;; =============================================================================
;; Taint Propagation Tests
;; =============================================================================

(def tainted-graph
  "Graph with admitted node causing taint."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-admitted
                              :deps #{:1-assume}
                              :status :admitted
                              :taint :self-admitted
                              :order 1)
                 (f/make-node :1-result
                              :deps #{:1-admitted}
                              :taint :tainted
                              :order 2)]))

(deftest extract-lemma-taint-test
  (testing "Extracted lemma inherits taint"
    (let [result (extract-lemma/extract-lemma tainted-graph :1-result "L-tainted")]
      (is (:ok result))
      (let [lemma (:lemma result)]
        (is (= :tainted (:status lemma)))
        (is (= :tainted (:taint lemma)))))))

;; =============================================================================
;; Version & Metadata Tests
;; =============================================================================

(deftest extract-lemma-version-test
  (testing "Version is incremented"
    (let [result (extract-lemma/extract-lemma extractable-graph :1-result "L1")]
      (is (:ok result))
      (is (= 2 (:version (:ok result)))))))

(deftest extract-lemma-schema-test
  (testing "Output validates against schema"
    (let [result (extract-lemma/extract-lemma extractable-graph :1-result "L1")]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))

;; =============================================================================
;; Scoped Extraction Tests
;; =============================================================================

(def scoped-extractable-graph
  "Graph with balanced scope for extraction."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-local-assume
                              :type :local-assume
                              :justification :local-assumption
                              :introduces "P"
                              :deps #{:1-assume}
                              :order 1)
                 (f/make-node :1-step
                              :deps #{:1-local-assume}
                              :scope #{:1-local-assume}
                              :order 2)
                 (f/make-node :1-discharge
                              :type :local-discharge
                              :justification :discharge
                              :discharges :1-local-assume
                              :deps #{:1-step}
                              :scope #{:1-local-assume}
                              :order 3)]))

(deftest extract-lemma-balanced-scope-test
  (testing "Extract with balanced local scope"
    (let [result (extract-lemma/extract-lemma
                  scoped-extractable-graph
                  :1-discharge
                  "L-scoped")]
      (is (:ok result)))))

(def unbalanced-scope-graph
  "Graph with unbalanced scope - assume without discharge."
  (f/make-graph [(f/make-node :1-assume
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-local-assume
                              :type :local-assume
                              :justification :local-assumption
                              :introduces "P"
                              :deps #{:1-assume}
                              :order 1)
                 (f/make-node :1-result
                              :deps #{:1-local-assume}
                              :scope #{:1-local-assume}
                              :order 2)]))

(deftest extract-lemma-unbalanced-scope-test
  (testing "Reject extraction with unbalanced scope"
    (let [result (extract-lemma/extract-lemma
                  unbalanced-scope-graph
                  :1-result
                  "L-fail"
                  #{:1-local-assume :1-result})]  ; No discharge
      (is (:error result))
      (is (some #(= :unbalanced-scope (:type %)) (:error result))))))

;; =============================================================================
;; Lemma Name Generation Test
;; =============================================================================

(deftest generate-lemma-name-test
  (testing "Generate unique lemma name"
    (let [name (extract-lemma/generate-lemma-name extractable-graph nil)]
      (is (string? name))
      (is (re-matches #"L1-[a-f0-9]{6}" name)))))
