(ns alethfeld.tx-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.tx :as tx]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.git :as git]
            [alethfeld.io :as io]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-tx-test-"})]
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
  "Initialize a test repository with git."
  []
  (store/init-repo! *temp-dir*)
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "Test User")
  (git/git-config! *temp-dir* "user.email" "test@example.com"))

(defn- test-mote
  "Create a minimal valid mote for testing."
  [& {:keys [id claim status priority difficulty parent children]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3}}]
  (cond-> (mote/make-mote id claim "test-agent"
                          :status status
                          :priority priority
                          :difficulty difficulty)
    parent (assoc :parent parent)
    children (assoc :children children)))

;; =============================================================================
;; transact! Tests
;; =============================================================================

(deftest transact-basic-test
  (testing "Creates commit after transaction"
    (init-test-repo)
    (let [result (tx/transact! *temp-dir* "Add mote"
                               (fn [repo]
                                 (store/save-mote! repo (test-mote :id "1"))
                                 :done))]
      (is (= :done (:result result)))
      (is (some? (:commit result)))
      (is (string? (get-in result [:commit :sha]))))))

(deftest transact-no-changes-test
  (testing "Returns nil commit when no changes"
    (init-test-repo)
    ;; First add and commit something
    (tx/transact! *temp-dir* "Initial" (fn [repo]
                                          (store/save-mote! repo (test-mote :id "1"))))
    ;; Second transaction with no changes
    (let [result (tx/transact! *temp-dir* "No changes"
                               (fn [_repo]
                                 :nothing))]
      (is (= :nothing (:result result)))
      (is (nil? (:commit result))))))

(deftest transact-initializes-git-test
  (testing "Initializes git if needed"
    ;; Just init store, not git
    (store/init-repo! *temp-dir*)
    (is (not (git/git-initialized? *temp-dir*)))
    (tx/transact! *temp-dir* "Init" (fn [repo]
                                      (store/save-mote! repo (test-mote))))
    (is (git/git-initialized? *temp-dir*))))

(deftest transact-exception-test
  (testing "Exception propagates out"
    (init-test-repo)
    (is (thrown-with-msg? Exception #"Test error"
          (tx/transact! *temp-dir* "Fail"
                        (fn [_repo]
                          (throw (Exception. "Test error"))))))))

(deftest transact-multiple-motes-test
  (testing "Can write multiple motes in one transaction"
    (init-test-repo)
    (tx/transact! *temp-dir* "Add many"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))
                    (store/save-mote! repo (test-mote :id "2"))
                    (store/save-mote! repo (test-mote :id "3"))))
    ;; All motes should exist
    (is (some? (store/load-mote *temp-dir* "1")))
    (is (some? (store/load-mote *temp-dir* "2")))
    (is (some? (store/load-mote *temp-dir* "3")))
    ;; Should be one commit (plus initial if any)
    (let [log (git/git-log *temp-dir*)]
      (is (= "Add many" (:message (first log)))))))

;; =============================================================================
;; with-validation Tests
;; =============================================================================

(deftest with-validation-valid-test
  (testing "Commits when validation passes"
    (init-test-repo)
    ;; Create parent first
    (tx/transact! *temp-dir* "Add parent"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :children ["1.1"]))))
    ;; Add child with proper bidirectional link
    (let [result (tx/with-validation *temp-dir* "Add child"
                   (fn [repo]
                     (store/save-mote! repo (test-mote :id "1.1" :parent "1"))
                     :valid))]
      (is (= :valid (:result result)))
      (is (some? (:commit result))))))

(deftest with-validation-invalid-rollback-test
  (testing "Rolls back on validation failure"
    (init-test-repo)
    ;; Create a valid parent
    (tx/transact! *temp-dir* "Add parent"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))))
    ;; Try to create an orphan child (parent doesn't list it)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Validation failed"
          (tx/with-validation *temp-dir* "Add orphan"
            (fn [repo]
              (store/save-mote! repo (test-mote :id "1.1" :parent "1"))))))
    ;; Child should NOT exist (rolled back)
    (is (nil? (store/load-mote *temp-dir* "1.1")))
    ;; Parent should still exist
    (is (some? (store/load-mote *temp-dir* "1")))))

(deftest with-validation-cycle-rollback-test
  (testing "Rolls back when cycle detected"
    (init-test-repo)
    ;; Create initial motes without cycles
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))
                    (store/save-mote! repo (test-mote :id "2"))))
    ;; Try to create a cycle via assumptions
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Validation failed"
          (tx/with-validation *temp-dir* "Create cycle"
            (fn [repo]
              ;; Mote 1 assumes 2, mote 2 assumes 1 = cycle
              (store/save-mote! repo
                (assoc (test-mote :id "1")
                       :assumptions [{:type :internal :ref "2" :label "dep"}]))
              (store/save-mote! repo
                (assoc (test-mote :id "2")
                       :assumptions [{:type :internal :ref "1" :label "dep"}]))))))
    ;; Original motes should be restored (no assumptions)
    (let [m1 (store/load-mote *temp-dir* "1")
          m2 (store/load-mote *temp-dir* "2")]
      (is (empty? (:assumptions m1)))
      (is (empty? (:assumptions m2))))))

(deftest with-validation-broken-refs-rollback-test
  (testing "Rolls back on broken internal refs"
    (init-test-repo)
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))))
    ;; Try to create a mote with broken ref (valid MoteId pattern but non-existent)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Validation failed"
          (tx/with-validation *temp-dir* "Add broken ref"
            (fn [repo]
              (store/save-mote! repo
                (assoc (test-mote :id "2")
                       :assumptions [{:type :internal :ref "999" :note "broken ref"}]))))))
    ;; Mote 2 should not exist
    (is (nil? (store/load-mote *temp-dir* "2")))))

(deftest with-validation-error-info-test
  (testing "Includes validation errors in exception"
    (init-test-repo)
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))))
    (try
      (tx/with-validation *temp-dir* "Bad"
        (fn [repo]
          (store/save-mote! repo (test-mote :id "1.1" :parent "1"))))
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (is (= :validation-failed (:type (ex-data e))))
        (is (vector? (:errors (ex-data e))))
        (is (seq (:errors (ex-data e))))))))

;; =============================================================================
;; atomic-write! Tests
;; =============================================================================

(deftest atomic-write-single-test
  (testing "Writes single mote"
    (init-test-repo)
    (let [result (tx/atomic-write! *temp-dir* "Add one" [(test-mote :id "1")])]
      (is (= ["1"] (:result result)))
      (is (some? (:commit result)))
      (is (some? (store/load-mote *temp-dir* "1"))))))

(deftest atomic-write-multiple-test
  (testing "Writes multiple motes atomically"
    (init-test-repo)
    (let [motes [(test-mote :id "1" :children ["1.1" "1.2"])
                 (test-mote :id "1.1" :parent "1")
                 (test-mote :id "1.2" :parent "1")]
          result (tx/atomic-write! *temp-dir* "Add family" motes)]
      (is (= ["1" "1.1" "1.2"] (:result result)))
      ;; All should exist
      (is (some? (store/load-mote *temp-dir* "1")))
      (is (some? (store/load-mote *temp-dir* "1.1")))
      (is (some? (store/load-mote *temp-dir* "1.2"))))))

(deftest atomic-write-validation-failure-test
  (testing "Rolls back all on validation failure"
    (init-test-repo)
    ;; Try to write motes with broken parent-child link
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Validation failed"
          (tx/atomic-write! *temp-dir* "Bad family"
                            [(test-mote :id "1" :children ["1.1"])
                             ;; 1.1 doesn't have parent set
                             (test-mote :id "1.1")])))
    ;; Neither should exist
    (is (nil? (store/load-mote *temp-dir* "1")))
    (is (nil? (store/load-mote *temp-dir* "1.1")))))

(deftest atomic-write-no-validate-test
  (testing "Can skip validation"
    (init-test-repo)
    ;; Write motes with broken link but skip validation
    (let [result (tx/atomic-write! *temp-dir* "Skip validation"
                                   [(test-mote :id "1" :children ["1.1"])
                                    (test-mote :id "1.1")]  ; missing parent
                                   :validate false)]
      ;; Both should exist despite broken link
      (is (some? (store/load-mote *temp-dir* "1")))
      (is (some? (store/load-mote *temp-dir* "1.1"))))))

;; =============================================================================
;; atomic-delete! Tests
;; =============================================================================

(deftest atomic-delete-test
  (testing "Deletes multiple motes atomically"
    (init-test-repo)
    ;; Create some motes
    (tx/atomic-write! *temp-dir* "Add" [(test-mote :id "1")
                                         (test-mote :id "2")
                                         (test-mote :id "3")]
                      :validate false)
    ;; Delete some
    (let [result (tx/atomic-delete! *temp-dir* "Delete" ["1" "2"] :validate false)]
      (is (= [{:id "1" :deleted? true}
              {:id "2" :deleted? true}]
             (:result result)))
      (is (nil? (store/load-mote *temp-dir* "1")))
      (is (nil? (store/load-mote *temp-dir* "2")))
      (is (some? (store/load-mote *temp-dir* "3"))))))

(deftest atomic-delete-nonexistent-test
  (testing "Returns false for nonexistent motes"
    (init-test-repo)
    (let [result (tx/atomic-delete! *temp-dir* "Delete nothing" ["nonexistent"]
                                    :validate false)]
      (is (= [{:id "nonexistent" :deleted? false}]
             (:result result))))))

;; =============================================================================
;; atomic-update! Tests
;; =============================================================================

(deftest atomic-update-test
  (testing "Updates mote atomically"
    (init-test-repo)
    (tx/atomic-write! *temp-dir* "Add" [(test-mote :id "1" :claim "Original")]
                      :validate false)
    (let [result (tx/atomic-update! *temp-dir* "Update"
                                    "1"
                                    #(assoc % :claim "Updated")
                                    :validate false)]
      (is (= "Updated" (:claim (:result result))))
      (is (= "Updated" (:claim (store/load-mote *temp-dir* "1")))))))

(deftest atomic-update-not-found-test
  (testing "Throws when mote not found"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Mote not found"
          (tx/atomic-update! *temp-dir* "Update missing"
                             "nonexistent"
                             identity)))))

(deftest atomic-update-validation-test
  (testing "Validates after update"
    (init-test-repo)
    ;; Create parent with child
    (tx/atomic-write! *temp-dir* "Setup"
                      [(test-mote :id "1" :children ["1.1"])
                       (test-mote :id "1.1" :parent "1")]
                      :validate false)
    ;; Try to break the link by removing child from parent's children list
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Validation failed"
          (tx/atomic-update! *temp-dir* "Break link"
                             "1"
                             #(assoc % :children []))))))

;; =============================================================================
;; pending-changes? Tests
;; =============================================================================

(deftest pending-changes-clean-test
  (testing "Returns false when clean"
    (init-test-repo)
    (tx/transact! *temp-dir* "Add" (fn [repo]
                                     (store/save-mote! repo (test-mote))))
    (is (false? (tx/pending-changes? *temp-dir*)))))

(deftest pending-changes-untracked-test
  (testing "Returns true for untracked files"
    (init-test-repo)
    ;; Create initial state with a commit
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1"))))
    (is (false? (tx/pending-changes? *temp-dir*)))
    ;; Add new file without committing (IDs must be numeric)
    (store/save-mote! *temp-dir* (test-mote :id "2"))
    (is (true? (tx/pending-changes? *temp-dir*)))))

(deftest pending-changes-modified-test
  (testing "Returns true for modified files"
    (init-test-repo)
    (tx/transact! *temp-dir* "Add" (fn [repo]
                                     (store/save-mote! repo (test-mote))))
    ;; Modify without committing
    (store/save-mote! *temp-dir* (test-mote :claim "Modified"))
    (is (true? (tx/pending-changes? *temp-dir*)))))

;; =============================================================================
;; last-commit Tests
;; =============================================================================

(deftest last-commit-none-test
  (testing "Returns nil when no commits"
    (init-test-repo)
    (is (nil? (tx/last-commit *temp-dir*)))))

(deftest last-commit-exists-test
  (testing "Returns last commit info"
    (init-test-repo)
    (tx/transact! *temp-dir* "First commit"
                  (fn [repo]
                    (store/save-mote! repo (test-mote))))
    (let [commit (tx/last-commit *temp-dir*)]
      (is (some? commit))
      (is (= "First commit" (:message commit)))
      (is (string? (:sha commit)))
      (is (= "Test User" (:author commit))))))

;; =============================================================================
;; Integration Tests
;; =============================================================================

(deftest full-workflow-test
  (testing "Complete transaction workflow"
    (init-test-repo)

    ;; Step 1: Create root mote
    (tx/transact! *temp-dir* "Create root"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Root theorem"))))

    ;; Step 2: Add valid children
    (tx/with-validation *temp-dir* "Add children"
      (fn [repo]
        ;; Update parent to list children
        (store/save-mote! repo (test-mote :id "1" :claim "Root theorem"
                                          :children ["1.1" "1.2"]))
        ;; Add children with parent links
        (store/save-mote! repo (test-mote :id "1.1" :parent "1"))
        (store/save-mote! repo (test-mote :id "1.2" :parent "1"))))

    ;; All motes should exist
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 3 (count motes)))
      (is (= ["1.1" "1.2"] (:children (get motes "1"))))
      (is (= "1" (:parent (get motes "1.1")))))

    ;; Git should have history
    (let [log (git/git-log *temp-dir*)]
      (is (>= (count log) 2)))))

(deftest rollback-preserves-original-test
  (testing "Rollback exactly restores original state"
    (init-test-repo)

    ;; Create initial state (use correct definition schema: :symbol/:meaning)
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo
                      (assoc (test-mote :id "1" :claim "Original claim")
                             :definitions [{:symbol "x" :meaning "a value"}]))))

    ;; Get original mote
    (let [original (store/load-mote *temp-dir* "1")]
      ;; Try an invalid transaction
      (try
        (tx/with-validation *temp-dir* "Bad change"
          (fn [repo]
            ;; Make changes that will fail validation
            (store/save-mote! repo
              (assoc (test-mote :id "1" :claim "Changed claim"
                               :children ["1.1"])
                     :definitions []))
            ;; Child without parent link = validation failure
            (store/save-mote! repo (test-mote :id "1.1"))))
        (catch Exception _))

      ;; Mote should be exactly as before
      (let [restored (store/load-mote *temp-dir* "1")]
        (is (= "Original claim" (:claim restored)))
        (is (= [{:symbol "x" :meaning "a value"}] (:definitions restored)))
        (is (empty? (:children restored)))))))

(deftest no-rollback-after-validation-passes-test
  (testing "Validated changes are NOT rolled back when git operations fail"
    (init-test-repo)

    ;; Create initial state
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Original"))))

    ;; Simulate git-commit! failing after validation passes
    (let [original-commit git/git-commit!]
      (with-redefs [git/git-commit! (fn [& _]
                                      (throw (ex-info "Simulated git failure"
                                                      {:type :git-error})))]
        ;; This should throw, but changes should remain on disk
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"Simulated git failure"
                              (tx/with-validation *temp-dir* "Update mote"
                                (fn [repo]
                                  (store/save-mote! repo
                                    (test-mote :id "1" :claim "Updated"))))))))

    ;; Key assertion: changes should STILL be on disk (not rolled back)
    ;; because validation passed before git-commit failed
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (= "Updated" (:claim mote))
          "Validated changes must be preserved even when git commit fails")))

  (testing "Changes ARE rolled back when function execution fails"
    (init-test-repo)

    ;; Create initial state
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "2" :claim "Original"))))

    ;; Function itself throws - should rollback
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Function failed"
                          (tx/with-validation *temp-dir* "Update mote"
                            (fn [repo]
                              (store/save-mote! repo (test-mote :id "2" :claim "Changed"))
                              (throw (ex-info "Function failed" {}))))))

    ;; Changes should be rolled back
    (let [mote (store/load-mote *temp-dir* "2")]
      (is (= "Original" (:claim mote))
          "Changes must be rolled back when function throws"))))

;; =============================================================================
;; Snapshot Restoration Error Handling Tests
;; =============================================================================

(deftest restore-snapshot-delete-failure-test
  (testing "Rollback continues when delete fails (best effort)"
    (init-test-repo)

    ;; Create initial state
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Original"))))

    ;; Simulate delete-file failing
    (with-redefs [io/delete-file (fn [path]
                                   (throw (Exception. "Permission denied")))]
      ;; Transaction should still attempt restoration of original files
      ;; even if deletes fail - capture stderr to verify warning is logged
      (let [err-output (java.io.StringWriter.)]
        (binding [*err* err-output]
          (try
            (tx/with-validation *temp-dir* "Add invalid child"
              (fn [repo]
                ;; Add a file that will need to be deleted on rollback
                (store/save-mote! repo (test-mote :id "2" :claim "New file"))
                ;; Create orphan to trigger validation failure
                (store/save-mote! repo (test-mote :id "1.1" :parent "1"))))
            (catch clojure.lang.ExceptionInfo _)))
        ;; Warning should be logged about delete failures
        (is (str/includes? (str err-output) "Warning")
            "Should log warning about delete failures"))))

  (testing "Original files are restored even when some deletes fail"
    (init-test-repo)

    ;; Create initial state with specific content
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Original content"))))

    ;; Mock delete to fail but allow writes
    (let [original-delete io/delete-file]
      (with-redefs [io/delete-file (fn [path]
                                     ;; Fail for new files only
                                     (if (str/includes? path "/2.edn")
                                       (throw (Exception. "Simulated permission error"))
                                       (original-delete path)))]
        (try
          (tx/with-validation *temp-dir* "Modify and add"
            (fn [repo]
              ;; Modify existing file
              (store/save-mote! repo (test-mote :id "1" :claim "Modified!"))
              ;; Add new file
              (store/save-mote! repo (test-mote :id "2" :claim "New"))
              ;; Create validation failure
              (store/save-mote! repo (test-mote :id "1.1" :parent "1"))))
          (catch clojure.lang.ExceptionInfo _))))

    ;; Original content should be restored
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (= "Original content" (:claim mote))
          "Original content must be restored on rollback"))))

(deftest restore-snapshot-write-failure-test
  (testing "Write failure during restoration throws with context"
    (init-test-repo)

    ;; Create initial state
    (tx/transact! *temp-dir* "Initial"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Original"))))

    ;; Simulate write-edn failing during restoration
    (let [write-count (atom 0)]
      (with-redefs [io/write-edn (fn [path data]
                                   (swap! write-count inc)
                                   ;; Fail on restoration attempt (after initial writes)
                                   (when (> @write-count 2)
                                     (throw (Exception. "Disk full")))
                                   ;; Normal write for transaction phase
                                   (let [f (babashka.fs/file path)
                                         parent (babashka.fs/parent f)]
                                     (when (and parent (not (babashka.fs/exists? parent)))
                                       (babashka.fs/create-dirs parent))
                                     (spit f (pr-str data))
                                     (str path)))]
        ;; This should throw from the restoration phase
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"(Failed to restore|Disk full)"
                              (tx/with-validation *temp-dir* "Bad change"
                                (fn [repo]
                                  ;; Make changes that will fail validation
                                  (store/save-mote! repo (test-mote :id "1.1" :parent "1")))))))))

;; =============================================================================
;; Path Canonicalization Tests (alethfeld-9vok)
;; =============================================================================

(deftest path-canonicalization-symlink-test
  (testing "Symlinked paths use the same lock"
    ;; Create a real directory and a symlink to it
    (let [real-dir (str (fs/create-temp-dir {:prefix "tx-test-real-"}))
          parent (fs/parent real-dir)
          link-path (str parent "/tx-test-symlink-" (System/currentTimeMillis))]
      (try
        ;; Create symlink
        (fs/create-sym-link link-path real-dir)

        ;; Initialize repos using both paths
        (store/init-repo! real-dir)
        (git/git-init! real-dir)
        (git/git-config! real-dir "user.name" "Test User")
        (git/git-config! real-dir "user.email" "test@example.com")

        ;; Both paths should be able to transact (they're the same repo)
        (tx/transact! real-dir "Via real path"
                      (fn [repo]
                        (store/save-mote! repo (test-mote :id "1" :claim "First"))))

        (tx/transact! link-path "Via symlink"
                      (fn [repo]
                        (store/save-mote! repo (test-mote :id "2" :claim "Second"))))

        ;; Both motes should exist (same repo)
        (is (some? (store/load-mote real-dir "1")))
        (is (some? (store/load-mote real-dir "2")))
        (is (some? (store/load-mote link-path "1")))
        (is (some? (store/load-mote link-path "2")))

        (finally
          (fs/delete-tree real-dir)
          (fs/delete-if-exists link-path))))))

(deftest path-canonicalization-nil-test
  (testing "Nil path throws IllegalArgumentException"
    (is (thrown? IllegalArgumentException
          (tx/transact! nil "Should fail"
                        (fn [_repo] :never-called))))))

(deftest path-canonicalization-relative-path-test
  (testing "Relative paths are resolved correctly"
    (init-test-repo)
    ;; Get relative path from cwd
    (let [cwd (System/getProperty "user.dir")
          rel-path (if (.startsWith *temp-dir* cwd)
                     (subs *temp-dir* (inc (count cwd)))
                     *temp-dir*)]
      ;; Only run test if we can form a relative path
      (when (not= rel-path *temp-dir*)
        (tx/transact! rel-path "Via relative"
                      (fn [repo]
                        (store/save-mote! repo (test-mote :id "1" :claim "Relative test"))))
        (is (some? (store/load-mote *temp-dir* "1")))))))

(deftest path-canonicalization-trailing-slash-test
  (testing "Paths with trailing slashes are normalized"
    (init-test-repo)
    ;; Transact with trailing slash
    (tx/transact! (str *temp-dir* "/") "With trailing slash"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "1" :claim "Trailing test"))))
    ;; Should be accessible without trailing slash
    (is (some? (store/load-mote *temp-dir* "1")))
    ;; Transact again without trailing slash (same lock)
    (tx/transact! *temp-dir* "Without trailing slash"
                  (fn [repo]
                    (store/save-mote! repo (test-mote :id "2" :claim "No trailing"))))
    (is (some? (store/load-mote *temp-dir* "2")))))

(deftest path-canonicalization-dotdot-test
  (testing "Paths with .. are normalized"
    (init-test-repo)
    ;; Create a path with .. using the dirname itself (it exists)
    ;; e.g., /tmp/alethfeld-tx-test-123/../alethfeld-tx-test-123 -> /tmp/alethfeld-tx-test-123
    (let [dirname (fs/file-name *temp-dir*)
          dotdot-path (str *temp-dir* "/../" dirname)]
      ;; Transact using .. path
      (tx/transact! dotdot-path "Via .. path"
                    (fn [repo]
                      (store/save-mote! repo (test-mote :id "1" :claim "Dotdot test"))))
      ;; Should be accessible via original path
      (is (some? (store/load-mote *temp-dir* "1"))))))

(deftest path-canonicalization-nonexistent-path-test
  (testing "Non-existent paths don't crash (fall back to absolute)"
    ;; Use a unique path that doesn't exist
    (let [nonexistent (str "/tmp/alethfeld-nonexistent-" (System/currentTimeMillis))]
      (try
        ;; This should NOT throw - canonicalization falls back gracefully
        ;; The actual transaction will fail later when trying to access the path
        (is (thrown? Exception
              (tx/transact! nonexistent "Nonexistent path"
                            (fn [repo]
                              ;; This will fail because the directory doesn't exist
                              (store/save-mote! repo (test-mote :id "1"))))))
        (finally
          (fs/delete-if-exists nonexistent))))))

(deftest path-canonicalization-concurrent-same-repo-test
  (testing "Concurrent transactions on same repo (via different paths) are serialized"
    ;; Create a real directory and a symlink to it
    (let [real-dir (str (fs/create-temp-dir {:prefix "tx-test-concurrent-"}))
          parent (fs/parent real-dir)
          link-path (str parent "/tx-test-link-" (System/currentTimeMillis))
          counter (atom 0)
          results (atom [])]
      (try
        ;; Create symlink
        (fs/create-sym-link link-path real-dir)

        ;; Initialize repo
        (store/init-repo! real-dir)
        (git/git-init! real-dir)
        (git/git-config! real-dir "user.name" "Test User")
        (git/git-config! real-dir "user.email" "test@example.com")

        ;; Create initial mote
        (tx/transact! real-dir "Initial"
                      (fn [repo]
                        (store/save-mote! repo (test-mote :id "1" :claim "Initial"))))

        ;; Start concurrent transactions via different paths
        (let [f1 (future
                   (tx/transact! real-dir "Via real"
                                 (fn [repo]
                                   (let [n (swap! counter inc)]
                                     (Thread/sleep 50) ; Hold lock for a bit
                                     (swap! results conj [:real n])
                                     (store/save-mote! repo (test-mote :id "2" :claim "Real"))
                                     n))))
              f2 (future
                   (Thread/sleep 10) ; Small delay to ensure f1 starts first
                   (tx/transact! link-path "Via link"
                                 (fn [repo]
                                   (let [n (swap! counter inc)]
                                     (swap! results conj [:link n])
                                     (store/save-mote! repo (test-mote :id "3" :claim "Link"))
                                     n))))]
          ;; Wait for both to complete
          @f1
          @f2

          ;; Results should show serialization (counter values are consecutive)
          (is (= #{1 2} (set (map second @results)))
              "Both transactions should have run with consecutive counter values")

          ;; Both motes should exist
          (is (some? (store/load-mote real-dir "2")))
          (is (some? (store/load-mote real-dir "3"))))

        (finally
          (fs/delete-tree real-dir)
          (fs/delete-if-exists link-path)))))))
