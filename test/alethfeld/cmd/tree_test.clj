(ns alethfeld.cmd.tree-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-tree-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-test-repo
  "Initialize a test repository."
  []
  (store/init-repo! *temp-dir*))

(defn- create-test-mote
  "Create and save a test mote."
  [& {:keys [id claim status priority difficulty parent children taint]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3
           parent nil
           children []}}]
  (let [base-mote (mote/make-mote id claim "test-agent"
                                  :status status
                                  :priority priority
                                  :difficulty difficulty)
        with-parent (if parent (assoc base-mote :parent parent) base-mote)
        with-children (assoc with-parent :children children)
        with-taints (if (seq taint)
                      (reduce mote/add-taint with-children taint)
                      with-children)]
    (store/save-mote! *temp-dir* with-taints)
    with-taints))

(defn- tree-mote
  "Call tree command for a mote in the temp directory.
   Since cmd-tree uses '.' we need to test the underlying rendering logic."
  [id & {:keys [depth]}]
  (let [mote (store/load-mote *temp-dir* id)]
    (when-not mote
      (throw (ex-info "Mote not found"
                      {:type :not-found
                       :mote-id id})))
    (let [motes (store/load-all-motes *temp-dir*)
          lines (#'cmd/render-tree mote motes "" true 0 depth 60)]
      {:lines (vec lines)
       :mote-count (count lines)})))

;; =============================================================================
;; Basic Tree Tests
;; =============================================================================

(deftest tree-single-mote-test
  (testing "tree renders a single mote"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root claim" :status :verified)
    (let [result (tree-mote "1")]
      (is (= 1 (:mote-count result)))
      (is (= 1 (count (:lines result))))
      (is (str/includes? (first (:lines result)) "1"))
      (is (str/includes? (first (:lines result)) "[verified]"))
      (is (str/includes? (first (:lines result)) "Root claim")))))

(deftest tree-status-verified-test
  (testing "tree shows [verified] status indicator"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Verified claim" :status :verified)
    (let [result (tree-mote "1")]
      (is (str/includes? (first (:lines result)) "[verified]")))))

(deftest tree-status-fixed-test
  (testing "tree shows [fixed] status indicator"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Fixed claim" :status :fixed)
    (let [result (tree-mote "1")]
      (is (str/includes? (first (:lines result)) "[fixed]")))))

(deftest tree-status-proposed-test
  (testing "tree shows [proposed] status indicator"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Proposed claim" :status :proposed)
    (let [result (tree-mote "1")]
      (is (str/includes? (first (:lines result)) "[proposed]")))))

(deftest tree-taint-indicators-test
  (testing "tree shows taint indicators"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Tainted claim" :taint #{:needs-decomposition :needs-verification})
    (let [result (tree-mote "1")
          line (first (:lines result))]
      (is (str/includes? line "needs-decomposition"))
      (is (str/includes? line "needs-verification")))))

;; =============================================================================
;; Hierarchy Tests
;; =============================================================================

(deftest tree-parent-child-test
  (testing "tree renders parent with children"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Parent" :children ["1.1" "1.2"])
    (create-test-mote :id "1.1" :claim "First child" :parent "1")
    (create-test-mote :id "1.2" :claim "Second child" :parent "1")
    (let [result (tree-mote "1")]
      (is (= 3 (:mote-count result)))
      (is (some #(str/includes? % "1.1") (:lines result)))
      (is (some #(str/includes? % "1.2") (:lines result)))
      (is (some #(str/includes? % "First child") (:lines result)))
      (is (some #(str/includes? % "Second child") (:lines result))))))

(deftest tree-nested-hierarchy-test
  (testing "tree renders deeply nested structure"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "Level 1" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Level 2" :parent "1.1" :children ["1.1.1.1"])
    (create-test-mote :id "1.1.1.1" :claim "Level 3" :parent "1.1.1")
    (let [result (tree-mote "1")]
      (is (= 4 (:mote-count result)))
      (is (some #(str/includes? % "1.1.1.1") (:lines result)))
      (is (some #(str/includes? % "Level 3") (:lines result))))))

(deftest tree-multiple-children-test
  (testing "tree renders multiple children correctly"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1" "1.2" "1.3"])
    (create-test-mote :id "1.1" :claim "Child 1" :parent "1")
    (create-test-mote :id "1.2" :claim "Child 2" :parent "1")
    (create-test-mote :id "1.3" :claim "Child 3" :parent "1")
    (let [result (tree-mote "1")]
      (is (= 4 (:mote-count result)))
      (is (some #(str/includes? % "+--") (:lines result)) "Should have +-- connector")
      (is (some #(str/includes? % "\\--") (:lines result)) "Should have \\-- connector for last child"))))

;; =============================================================================
;; Depth Limiting Tests
;; =============================================================================

(deftest tree-depth-limit-zero-test
  (testing "depth=0 shows only root"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "Child" :parent "1")
    (let [result (tree-mote "1" :depth 0)]
      (is (= 1 (:mote-count result)))
      (is (str/includes? (first (:lines result)) "Root"))
      (is (not (some #(str/includes? % "Child") (:lines result)))))))

(deftest tree-depth-limit-one-test
  (testing "depth=1 shows root and immediate children"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "Child" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Grandchild" :parent "1.1")
    (let [result (tree-mote "1" :depth 1)]
      (is (= 2 (:mote-count result)))
      (is (some #(str/includes? % "Root") (:lines result)))
      (is (some #(str/includes? % "Child") (:lines result)))
      (is (not (some #(str/includes? % "Grandchild") (:lines result)))))))

(deftest tree-depth-limit-two-test
  (testing "depth=2 shows three levels"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "Child" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Grandchild" :parent "1.1" :children ["1.1.1.1"])
    (create-test-mote :id "1.1.1.1" :claim "Great-grandchild" :parent "1.1.1")
    (let [result (tree-mote "1" :depth 2)]
      (is (= 3 (:mote-count result)))
      (is (some #(str/includes? % "Grandchild") (:lines result)))
      (is (not (some #(str/includes? % "Great-grandchild") (:lines result)))))))

(deftest tree-no-depth-limit-test
  (testing "no depth limit shows all levels"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "L1" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "L2" :parent "1.1" :children ["1.1.1.1"])
    (create-test-mote :id "1.1.1.1" :claim "L3" :parent "1.1.1")
    (let [result (tree-mote "1")]
      (is (= 4 (:mote-count result)))
      (is (some #(str/includes? % "L3") (:lines result))))))

;; =============================================================================
;; ASCII Art Connector Tests
;; =============================================================================

(deftest tree-connectors-structure-test
  (testing "tree uses correct ASCII connectors"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1" "1.2"])
    (create-test-mote :id "1.1" :claim "First" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Nested" :parent "1.1")
    (create-test-mote :id "1.2" :claim "Last" :parent "1")
    (let [result (tree-mote "1")
          lines (:lines result)]
      ;; Root has no prefix
      (is (not (str/starts-with? (first lines) "+--")))
      (is (not (str/starts-with? (first lines) "\\--")))
      ;; First child has +-- (not last)
      (is (some #(and (str/includes? % "1.1 ")
                      (str/includes? % "+--")) lines))
      ;; Last child has \--
      (is (some #(and (str/includes? % "1.2 ")
                      (str/includes? % "\\--")) lines)))))

(deftest tree-continuation-lines-test
  (testing "tree uses | for continuation in nested trees"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1" "1.2"])
    (create-test-mote :id "1.1" :claim "First" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Nested under first" :parent "1.1")
    (create-test-mote :id "1.2" :claim "Second" :parent "1")
    (let [result (tree-mote "1")
          lines (:lines result)]
      ;; The nested child under first should have | in its prefix
      ;; because 1.2 comes after
      (is (some #(and (str/includes? % "1.1.1")
                      (str/includes? % "|")) lines)))))

;; =============================================================================
;; Claim Truncation Tests
;; =============================================================================

(deftest tree-long-claim-truncation-test
  (testing "tree truncates long claims"
    (init-test-repo)
    (let [long-claim (apply str (repeat 100 "x"))]
      (create-test-mote :id "1" :claim long-claim)
      (let [result (tree-mote "1")
            line (first (:lines result))]
        (is (< (count line) 150) "Line should be truncated")
        (is (str/includes? line "...") "Truncated claim should end with ...")))))

(deftest tree-short-claim-no-truncation-test
  (testing "tree does not truncate short claims"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Short claim")
    (let [result (tree-mote "1")
          line (first (:lines result))]
      (is (str/includes? line "Short claim"))
      (is (not (str/includes? line "..."))))))

;; =============================================================================
;; Starting from Child Tests
;; =============================================================================

(deftest tree-from-child-test
  (testing "tree can start from a child mote"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "Child" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "Grandchild" :parent "1.1")
    (let [result (tree-mote "1.1")]
      (is (= 2 (:mote-count result)))
      (is (str/includes? (first (:lines result)) "1.1 "))
      (is (str/includes? (first (:lines result)) "Child"))
      (is (some #(str/includes? % "Grandchild") (:lines result)))
      ;; Should NOT include the root
      (is (not (some #(str/includes? % "Root") (:lines result)))))))

;; =============================================================================
;; Empty Children Tests
;; =============================================================================

(deftest tree-no-children-test
  (testing "tree handles mote with no children"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Leaf mote")
    (let [result (tree-mote "1")]
      (is (= 1 (:mote-count result)))
      (is (str/includes? (first (:lines result)) "Leaf mote")))))

(deftest tree-empty-children-vector-test
  (testing "tree handles mote with empty children vector"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Empty children" :children [])
    (let [result (tree-mote "1")]
      (is (= 1 (:mote-count result))))))

;; =============================================================================
;; Missing Children Tests
;; =============================================================================

(deftest tree-missing-child-test
  (testing "tree handles missing children gracefully"
    (init-test-repo)
    ;; Parent references a child that doesn't exist
    (create-test-mote :id "1" :claim "Parent" :children ["1.1" "1.2"])
    (create-test-mote :id "1.1" :claim "Existing child" :parent "1")
    ;; 1.2 does not exist
    (let [result (tree-mote "1")]
      ;; Should still render what exists
      (is (= 2 (:mote-count result)))
      (is (some #(str/includes? % "Existing child") (:lines result))))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest tree-not-found-test
  (testing "tree throws for non-existent mote"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (tree-mote "999")))))

;; =============================================================================
;; CLI Integration Tests
;; =============================================================================

(deftest tree-handler-registered-test
  (testing "tree handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "tree")))))

(deftest tree-handler-is-function-test
  (testing "tree handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "tree")]
      (is (fn? handler)))))

;; =============================================================================
;; Format Functions Unit Tests
;; =============================================================================

(deftest format-status-test
  (testing "format-status creates bracketed indicators"
    (is (= "[verified]" (#'cmd/format-status :verified)))
    (is (= "[proposed]" (#'cmd/format-status :proposed)))
    (is (= "[fixed]" (#'cmd/format-status :fixed)))))

(deftest format-taints-test
  (testing "format-taints creates parenthesized list"
    (is (nil? (#'cmd/format-taints #{})))
    (is (nil? (#'cmd/format-taints nil)))
    (let [result (#'cmd/format-taints #{:needs-verification})]
      (is (str/includes? result "needs-verification"))
      (is (str/starts-with? result " (")))
    (let [result (#'cmd/format-taints #{:needs-decomposition :needs-refs})]
      (is (str/includes? result "needs-decomposition"))
      (is (str/includes? result "needs-refs")))))

(deftest truncate-claim-test
  (testing "truncate-claim handles various lengths"
    (is (= "short" (#'cmd/truncate-claim "short" 60)))
    (is (= "abc..." (#'cmd/truncate-claim "abcdefghij" 6)))
    (is (= "exactly" (#'cmd/truncate-claim "exactly" 7)))))
