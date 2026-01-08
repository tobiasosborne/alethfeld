(ns validate-graph.cli-test
  "Tests for CLI entry point and file handling."
  (:require [clojure.test :refer [deftest testing is are use-fixtures]]
            [clojure.java.io :as io]
            [clojure.edn :as edn]
            [validate-graph.main :as main]
            [validate-graph.fixtures :as fix]))

;; =============================================================================
;; Test Fixture Setup
;; =============================================================================

(def ^:dynamic *temp-dir* nil)

(defn create-temp-dir []
  (let [dir (io/file (System/getProperty "java.io.tmpdir")
                     (str "validate-graph-test-" (System/currentTimeMillis)))]
    (.mkdirs dir)
    dir))

(defn delete-recursively [f]
  (when (.isDirectory f)
    (doseq [child (.listFiles f)]
      (delete-recursively child)))
  (.delete f))

(defn temp-dir-fixture [f]
  (let [dir (create-temp-dir)]
    (binding [*temp-dir* dir]
      (try
        (f)
        (finally
          (delete-recursively dir))))))

(use-fixtures :each temp-dir-fixture)

(defn write-edn-file [filename content]
  (let [file (io/file *temp-dir* filename)]
    (spit file (pr-str content))
    (.getAbsolutePath file)))

(defn write-string-file [filename content]
  (let [file (io/file *temp-dir* filename)]
    (spit file content)
    (.getAbsolutePath file)))

;; =============================================================================
;; File Reading Tests
;; =============================================================================

(deftest read-valid-edn-file-test
  (testing "Reading valid EDN file succeeds"
    (let [path (write-edn-file "valid.edn" fix/minimal-valid-graph)
          result (main/read-edn-file path)]
      (is (:ok result))
      (is (map? (:ok result)))
      (is (= "test-graph-001" (:graph-id (:ok result)))))))

(deftest read-nonexistent-file-test
  (testing "Reading non-existent file returns error"
    (let [result (main/read-edn-file "/nonexistent/path/file.edn")]
      (is (:error result))
      (is (clojure.string/includes? (:error result) "not found")))))

(deftest read-invalid-edn-syntax-test
  (testing "Reading file with invalid EDN syntax returns error"
    (let [path (write-string-file "invalid.edn" "{:foo [unclosed")
          result (main/read-edn-file path)]
      (is (:error result))
      (is (clojure.string/includes? (:error result) "parse")))))

(deftest read-empty-file-test
  (testing "Reading empty file returns error"
    (let [path (write-string-file "empty.edn" "")
          result (main/read-edn-file path)]
      (is (:error result)))))

(deftest read-non-map-edn-test
  (testing "Reading non-map EDN returns ok (schema catches it)"
    (let [path (write-string-file "vector.edn" "[1 2 3]")
          result (main/read-edn-file path)]
      ;; File reads successfully, schema validation will catch the issue
      (is (:ok result))
      (is (vector? (:ok result))))))

;; =============================================================================
;; Validation Integration Tests
;; =============================================================================

(deftest validate-valid-file-test
  (testing "Validating valid file returns exit code 0"
    (let [path (write-edn-file "valid.edn" fix/minimal-valid-graph)
          result (main/validate-file path {})]
      (is (= 0 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "OK")))))

(deftest validate-schema-invalid-file-test
  (testing "Validating schema-invalid file returns exit code 1"
    (let [path (write-edn-file "invalid-schema.edn" fix/invalid-node-type-graph)
          result (main/validate-file path {})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "FAIL")))))

(deftest validate-semantic-invalid-file-test
  (testing "Validating semantically invalid file returns exit code 1"
    (let [path (write-edn-file "invalid-semantic.edn" fix/missing-dependency-graph)
          result (main/validate-file path {})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "FAIL")))))

(deftest validate-nonexistent-file-test
  (testing "Validating non-existent file returns exit code 2"
    (let [result (main/validate-file "/nonexistent/file.edn" {})]
      (is (= 2 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "not found")))))

(deftest validate-invalid-edn-syntax-file-test
  (testing "Validating file with invalid EDN returns exit code 2"
    (let [path (write-string-file "bad-syntax.edn" "{broken")
          result (main/validate-file path {})]
      (is (= 2 (:exit-code result))))))

;; =============================================================================
;; CLI Options Tests
;; =============================================================================

(deftest quiet-mode-success-test
  (testing "Quiet mode shows minimal output on success"
    (let [path (write-edn-file "valid.edn" fix/minimal-valid-graph)
          result (main/validate-file path {:quiet true})]
      (is (= 0 (:exit-code result)))
      (is (nil? (:message result))))))

(deftest quiet-mode-failure-test
  (testing "Quiet mode shows minimal output on failure"
    (let [path (write-edn-file "invalid.edn" fix/invalid-node-type-graph)
          result (main/validate-file path {:quiet true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "FAIL"))
      (is (not (clojure.string/includes? (:message result) "\n"))))))

(deftest verbose-mode-success-test
  (testing "Verbose mode works on success"
    (let [path (write-edn-file "valid.edn" fix/minimal-valid-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 0 (:exit-code result))))))

(deftest verbose-mode-failure-test
  (testing "Verbose mode shows detailed errors on failure"
    (let [path (write-edn-file "invalid.edn" fix/missing-dependency-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "missing-dependency")))))

(deftest schema-only-mode-test
  (testing "Schema-only mode skips semantic validation"
    ;; This graph has valid schema but invalid semantics (missing dep)
    (let [path (write-edn-file "schema-valid.edn" fix/missing-dependency-graph)
          ;; Full validation should fail
          full-result (main/validate-file path {})
          ;; Schema-only should pass
          schema-result (main/validate-file path {:schema-only true})]
      (is (= 1 (:exit-code full-result)))
      (is (= 0 (:exit-code schema-result))))))

;; =============================================================================
;; Error Reporting Tests
;; =============================================================================

(deftest multiple-schema-errors-reported-test
  (testing "Multiple schema errors are reported"
    (let [bad-graph (-> fix/minimal-valid-graph
                        (assoc-in [:nodes :1-abc123 :type] :invalid-type)
                        (assoc-in [:nodes :1-abc123 :status] :invalid-status))
          path (write-edn-file "multi-error.edn" bad-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "Schema")))))

(deftest multiple-semantic-errors-reported-test
  (testing "Multiple semantic errors are reported"
    (let [bad-graph (-> fix/minimal-valid-graph
                        (assoc-in [:nodes :1-bad1]
                                  (fix/make-node :1-bad1 :deps #{:missing1}))
                        (assoc-in [:nodes :1-bad2]
                                  (fix/make-node :1-bad2 :deps #{:missing2})))
          path (write-edn-file "multi-semantic.edn" bad-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "missing-dependency")))))

(deftest error-message-includes-node-id-test
  (testing "Error message includes relevant node ID"
    (let [path (write-edn-file "with-bad-node.edn" fix/missing-dependency-graph)
          result (main/validate-file path {:verbose true})]
      (is (clojure.string/includes? (:message result) "1-aaa111")))))

;; =============================================================================
;; Usage and Help Tests
;; =============================================================================

(deftest usage-message-test
  (testing "Usage message is informative"
    (let [usage (main/usage "options summary here")]
      (is (clojure.string/includes? usage "validate-graph"))
      (is (clojure.string/includes? usage "Options"))
      (is (clojure.string/includes? usage "Exit codes")))))

(deftest error-message-formatting-test
  (testing "Error messages are formatted correctly"
    (let [msg (main/error-msg ["Error 1" "Error 2"])]
      (is (clojure.string/includes? msg "Error 1"))
      (is (clojure.string/includes? msg "Error 2")))))

;; =============================================================================
;; Complex File Tests
;; =============================================================================

(deftest validate-all-node-types-graph-test
  (testing "Complex graph with all node types validates"
    (let [path (write-edn-file "all-types.edn" fix/all-node-types-graph)
          result (main/validate-file path {})]
      (is (= 0 (:exit-code result))))))

(deftest validate-scoped-graph-test
  (testing "Graph with scopes validates"
    (let [path (write-edn-file "scoped.edn" fix/scoped-graph)
          result (main/validate-file path {})]
      (is (= 0 (:exit-code result))))))

(deftest validate-diamond-graph-test
  (testing "Diamond dependency graph validates"
    (let [path (write-edn-file "diamond.edn" fix/diamond-graph)
          result (main/validate-file path {})]
      (is (= 0 (:exit-code result))))))

;; =============================================================================
;; Cycle Detection via CLI Tests
;; =============================================================================

(deftest cli-detects-cycle-test
  (testing "CLI detects and reports cycles"
    (let [path (write-edn-file "cycle.edn" fix/direct-cycle-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "cycle")))))

(deftest cli-detects-self-loop-test
  (testing "CLI detects and reports self-loops"
    (let [path (write-edn-file "self-loop.edn" fix/self-loop-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "cycle")))))

;; =============================================================================
;; Taint Error Detection via CLI Tests
;; =============================================================================

(deftest cli-detects-incorrect-taint-test
  (testing "CLI detects incorrect taint values"
    (let [path (write-edn-file "bad-taint.edn" fix/incorrect-taint-chain-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "incorrect-taint")))))

;; =============================================================================
;; Scope Error Detection via CLI Tests
;; =============================================================================

(deftest cli-detects-invalid-scope-test
  (testing "CLI detects invalid scope entries"
    (let [path (write-edn-file "bad-scope.edn" fix/invalid-scope-non-ancestor-graph)
          result (main/validate-file path {:verbose true})]
      (is (= 1 (:exit-code result)))
      (is (clojure.string/includes? (:message result) "invalid-scope")))))
