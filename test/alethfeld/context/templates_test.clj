(ns alethfeld.context.templates-test
  "Tests for orchestrator context templates.

   Tests verify:
   - All template files exist in resources/templates/
   - Templates are valid markdown
   - Templates contain expected interpolation markers
   - Template loading functions work correctly"
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [alethfeld.context.templates :as templates]))

;; -----------------------------------------------------------------------------
;; Constants - Expected Templates
;; -----------------------------------------------------------------------------

(def expected-templates
  "List of all expected template names (without extension)."
  ["init"
   "theorem-audit"
   "strategy"
   "skeleton"
   "skeleton-review"
   "decomposition"
   "expand-verify-loop"
   "reference-check"
   "finalization"
   "complete"
   "escalated"])

;; -----------------------------------------------------------------------------
;; Template Path Tests
;; -----------------------------------------------------------------------------

(deftest template-path-test
  (testing "template-path returns correct path"
    (is (= "templates/init.md" (templates/template-path "init")))
    (is (= "templates/theorem-audit.md" (templates/template-path "theorem-audit")))
    (is (= "templates/skeleton-review.md" (templates/template-path "skeleton-review")))))

;; -----------------------------------------------------------------------------
;; Template File Existence Tests
;; -----------------------------------------------------------------------------

(deftest templates-exist-test
  (testing "all expected template files exist"
    (doseq [name expected-templates]
      (testing (str "template: " name)
        (let [path (templates/template-path name)
              resource (io/resource path)]
          (is (some? resource)
              (str "Template file not found: " path)))))))

;; -----------------------------------------------------------------------------
;; Template Loading Tests
;; -----------------------------------------------------------------------------

(deftest load-template-test
  (testing "load-template returns string content"
    (let [content (templates/load-template "init")]
      (is (string? content))
      (is (pos? (count content)))))

  (testing "load-template returns nil for missing template"
    (is (nil? (templates/load-template "nonexistent-template"))))

  (testing "all templates load successfully"
    (doseq [name expected-templates]
      (testing (str "loading: " name)
        (let [content (templates/load-template name)]
          (is (string? content)
              (str "Failed to load template: " name))
          (is (pos? (count content))
              (str "Template is empty: " name)))))))

;; -----------------------------------------------------------------------------
;; Template Content Validation Tests
;; -----------------------------------------------------------------------------

(deftest templates-are-markdown-test
  (testing "templates contain markdown headers"
    (doseq [name expected-templates]
      (testing (str "markdown check: " name)
        (let [content (templates/load-template name)]
          (is (re-find #"^#\s+" content)
              (str "Template missing markdown header: " name)))))))

(deftest templates-have-phase-headers-test
  (testing "templates have phase identification"
    (doseq [name expected-templates]
      (testing (str "phase header: " name)
        (let [content (templates/load-template name)]
          ;; Each template should identify its phase
          (is (or (str/includes? content "# ")
                  (str/includes? content "## Phase"))
              (str "Template missing phase identification: " name)))))))

;; -----------------------------------------------------------------------------
;; Interpolation Marker Tests
;; -----------------------------------------------------------------------------

(defn has-marker?
  "Check if content contains an interpolation marker."
  [content marker]
  (str/includes? content marker))

(deftest init-template-markers-test
  (testing "init template has expected markers"
    (let [content (templates/load-template "init")]
      (is (has-marker? content "<THEOREM_STATEMENT>"))
      (is (has-marker? content "<PROOF_GRAPH_PATH>")))))

(deftest theorem-audit-template-markers-test
  (testing "theorem-audit template has expected markers"
    (let [content (templates/load-template "theorem-audit")]
      (is (has-marker? content "<THEOREM_STATEMENT>")))))

(deftest strategy-template-markers-test
  (testing "strategy template has expected markers"
    (let [content (templates/load-template "strategy")]
      (is (has-marker? content "<THEOREM_STATEMENT>"))
      (is (has-marker? content "<N>"))
      (is (has-marker? content "<LIMIT>")))))

(deftest skeleton-template-markers-test
  (testing "skeleton template has expected markers"
    (let [content (templates/load-template "skeleton")]
      (is (has-marker? content "<THEOREM_STATEMENT>")))))

(deftest skeleton-review-template-markers-test
  (testing "skeleton-review template has expected markers"
    (let [content (templates/load-template "skeleton-review")]
      (is (has-marker? content "<THEOREM_STATEMENT>"))
      (is (has-marker? content "<LIST_OF_DEPTH_1_NODES>")))))

(deftest decomposition-template-markers-test
  (testing "decomposition template has expected markers"
    (let [content (templates/load-template "decomposition")]
      (is (has-marker? content "<THEOREM_STATEMENT>")))))

(deftest expand-verify-loop-template-markers-test
  (testing "expand-verify-loop template has expected markers"
    (let [content (templates/load-template "expand-verify-loop")]
      (is (has-marker? content "<N>"))
      (is (has-marker? content "<LIMIT>"))
      (is (has-marker? content "<SUBGRAPH_STATUS_LIST>")))))

(deftest reference-check-template-markers-test
  (testing "reference-check template has expected markers"
    (let [content (templates/load-template "reference-check")]
      (is (has-marker? content "<THEOREM_STATEMENT>")))))

(deftest finalization-template-markers-test
  (testing "finalization template has expected markers"
    (let [content (templates/load-template "finalization")]
      (is (has-marker? content "<CURRENT_STATUS>")))))

(deftest complete-template-markers-test
  (testing "complete template has expected markers"
    (let [content (templates/load-template "complete")]
      (is (has-marker? content "<THEOREM_STATEMENT>"))
      (is (has-marker? content "<CURRENT_STATUS>")))))

(deftest escalated-template-markers-test
  (testing "escalated template has expected markers"
    (let [content (templates/load-template "escalated")]
      (is (has-marker? content "<THEOREM_STATEMENT>"))
      (is (has-marker? content "<CURRENT_STATUS>")))))

;; -----------------------------------------------------------------------------
;; List Templates Test
;; -----------------------------------------------------------------------------

(deftest list-templates-test
  (testing "list-templates returns all template names"
    (let [templates (templates/list-templates)]
      (is (set? templates))
      (is (= (set expected-templates) templates))))

  (testing "list-templates returns non-empty set"
    (is (pos? (count (templates/list-templates))))))

;; -----------------------------------------------------------------------------
;; Interpolation Tests
;; -----------------------------------------------------------------------------

(deftest interpolate-test
  (testing "interpolate replaces single marker"
    (is (= "The theorem: X + Y = Z"
           (templates/interpolate "The theorem: <THEOREM_STATEMENT>"
                                  {"<THEOREM_STATEMENT>" "X + Y = Z"}))))

  (testing "interpolate replaces multiple markers"
    (is (= "Iteration 5 of 10"
           (templates/interpolate "Iteration <N> of <LIMIT>"
                                  {"<N>" "5"
                                   "<LIMIT>" "10"}))))

  (testing "interpolate preserves unmatched markers"
    (is (= "Value: 42, Unknown: <MISSING>"
           (templates/interpolate "Value: <VALUE>, Unknown: <MISSING>"
                                  {"<VALUE>" "42"}))))

  (testing "interpolate with empty vars returns original"
    (is (= "No changes <HERE>"
           (templates/interpolate "No changes <HERE>" {}))))

  (testing "interpolate handles multiple occurrences"
    (is (= "A then A again"
           (templates/interpolate "<X> then <X> again"
                                  {"<X>" "A"})))))

(deftest interpolate-template-test
  (testing "can load and interpolate a template"
    (let [content (templates/load-template "init")
          result (templates/interpolate content
                                        {"<THEOREM_STATEMENT>" "For all x, P(x)"
                                         "<PROOF_GRAPH_PATH>" "/path/to/graph.edn"})]
      (is (string? result))
      (is (str/includes? result "For all x, P(x)"))
      (is (str/includes? result "/path/to/graph.edn"))
      (is (not (str/includes? result "<THEOREM_STATEMENT>")))
      (is (not (str/includes? result "<PROOF_GRAPH_PATH>"))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest edge-cases-test
  (testing "template-path with nil returns nil"
    (is (nil? (templates/template-path nil))))

  (testing "load-template with nil returns nil"
    (is (nil? (templates/load-template nil))))

  (testing "interpolate with nil content returns nil"
    (is (nil? (templates/interpolate nil {"<X>" "Y"}))))

  (testing "interpolate with nil vars returns original"
    (is (= "unchanged" (templates/interpolate "unchanged" nil)))))
