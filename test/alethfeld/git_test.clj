(ns alethfeld.git-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [clojure.string :as str]
            [alethfeld.git :as git]
            [alethfeld.io :as io]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-git-test-"})]
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
  "Initialize a test git repository with user config."
  []
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "Test User")
  (git/git-config! *temp-dir* "user.email" "test@example.com"))

(defn- create-file
  "Create a file with content in the temp repo."
  [rel-path content]
  (let [full-path (str *temp-dir* "/" rel-path)]
    (io/write-edn full-path content)
    full-path))

(defn- create-alethfeld-file
  "Create a file in .alethfeld/ directory."
  [rel-path content]
  (create-file (str ".alethfeld/" rel-path) content))

;; =============================================================================
;; git-initialized? Tests
;; =============================================================================

(deftest git-initialized-false-test
  (testing "Returns false for non-git directory"
    (is (false? (git/git-initialized? *temp-dir*)))))

(deftest git-initialized-true-test
  (testing "Returns true after git init"
    (git/git-init! *temp-dir*)
    (is (true? (git/git-initialized? *temp-dir*)))))

;; =============================================================================
;; git-init! Tests
;; =============================================================================

(deftest git-init-creates-git-dir-test
  (testing "Creates .git directory"
    (git/git-init! *temp-dir*)
    (is (fs/directory? (str *temp-dir* "/.git")))))

(deftest git-init-idempotent-test
  (testing "Calling init twice is safe"
    (git/git-init! *temp-dir*)
    (git/git-init! *temp-dir*)
    (is (fs/directory? (str *temp-dir* "/.git")))))

(deftest git-init-returns-path-test
  (testing "Returns the repo path"
    (is (= *temp-dir* (git/git-init! *temp-dir*)))))

(deftest git-init-custom-branch-test
  (testing "Creates repo with custom initial branch"
    (git/git-init! *temp-dir* :initial-branch "trunk")
    (git/git-config! *temp-dir* "user.name" "Test")
    (git/git-config! *temp-dir* "user.email" "test@example.com")
    ;; Need a commit to verify branch name
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial commit")
    ;; Check we're on trunk branch
    (let [_config (git/git-config *temp-dir* "init.defaultBranch")]
      ;; The branch name should be trunk (visible in git branch output)
      (is (fs/exists? (str *temp-dir* "/.git/refs/heads/trunk"))))))

;; =============================================================================
;; git-config Tests
;; =============================================================================

(deftest git-config-set-get-test
  (testing "Can set and get config values"
    (init-test-repo)
    (git/git-config! *temp-dir* "user.name" "Alice")
    (is (= "Alice" (git/git-config *temp-dir* "user.name")))))

(deftest git-config-get-missing-test
  (testing "Returns nil for missing config"
    (init-test-repo)
    (is (nil? (git/git-config *temp-dir* "nonexistent.key")))))

;; =============================================================================
;; git-status Tests
;; =============================================================================

(deftest git-status-clean-test
  (testing "Clean repo shows clean status"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    (let [status (git/git-status *temp-dir*)]
      (is (:clean? status))
      (is (empty? (:staged status)))
      (is (empty? (:unstaged status)))
      (is (empty? (:untracked status))))))

(deftest git-status-untracked-test
  (testing "Shows untracked files"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    ;; Create new untracked file
    (create-file "new.txt" {:data "new"})
    (let [status (git/git-status *temp-dir*)]
      (is (not (:clean? status)))
      (is (some #(= "new.txt" %) (:untracked status))))))

(deftest git-status-staged-test
  (testing "Shows staged files"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (let [status (git/git-status *temp-dir*)]
      (is (not (:clean? status)))
      (is (some #(= "test.txt" %) (:staged status))))))

(deftest git-status-modified-test
  (testing "Shows modified files"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    ;; Modify the file
    (create-file "test.txt" {:data "modified"})
    (let [status (git/git-status *temp-dir*)]
      (is (not (:clean? status)))
      (is (some #(= "test.txt" %) (:unstaged status))))))

(deftest git-status-empty-repo-test
  (testing "Works on empty repo (no commits)"
    (init-test-repo)
    (let [status (git/git-status *temp-dir*)]
      (is (:clean? status)))))

;; =============================================================================
;; git-add! Tests
;; =============================================================================

(deftest git-add-single-file-test
  (testing "Stages a single file"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (let [status (git/git-status *temp-dir*)]
      (is (some #(= "test.txt" %) (:staged status))))))

(deftest git-add-multiple-files-test
  (testing "Stages multiple files"
    (init-test-repo)
    (create-file "a.txt" {:data "a"})
    (create-file "b.txt" {:data "b"})
    (git/git-add! *temp-dir* ["a.txt" "b.txt"])
    (let [status (git/git-status *temp-dir*)]
      (is (= 2 (count (:staged status))))
      (is (some #(= "a.txt" %) (:staged status)))
      (is (some #(= "b.txt" %) (:staged status))))))

(deftest git-add-returns-path-test
  (testing "Returns repo path"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (is (= *temp-dir* (git/git-add! *temp-dir* "test.txt")))))

;; =============================================================================
;; git-add-all! Tests
;; =============================================================================

(deftest git-add-all-alethfeld-test
  (testing "Stages all .alethfeld/ changes"
    (init-test-repo)
    (create-alethfeld-file "config.edn" {:project "Test"})
    (create-alethfeld-file "motes/1.edn" {:id "1"})
    (git/git-add-all! *temp-dir*)
    (let [status (git/git-status *temp-dir*)]
      (is (= 2 (count (:staged status))))
      (is (every? #(str/starts-with? % ".alethfeld/") (:staged status))))))

(deftest git-add-all-ignores-other-files-test
  (testing "Only stages .alethfeld/ files"
    (init-test-repo)
    (create-file "readme.txt" {:data "readme"})
    (create-alethfeld-file "config.edn" {:project "Test"})
    (git/git-add-all! *temp-dir*)
    (let [status (git/git-status *temp-dir*)]
      ;; config.edn should be staged
      (is (some #(str/includes? % "config.edn") (:staged status)))
      ;; readme.txt should be untracked
      (is (some #(= "readme.txt" %) (:untracked status))))))

;; =============================================================================
;; git-commit! Tests
;; =============================================================================

(deftest git-commit-creates-commit-test
  (testing "Creates a commit"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (let [result (git/git-commit! *temp-dir* "Test commit")]
      (is (string? (:sha result)))
      (is (= 7 (count (:sha result))))
      (is (= "Test commit" (:message result))))))

(deftest git-commit-appears-in-log-test
  (testing "Commit appears in log"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "My test commit")
    (let [log (git/git-log *temp-dir*)]
      (is (= 1 (count log)))
      (is (= "My test commit" (:message (first log)))))))

(deftest git-commit-no-changes-fails-test
  (testing "Commit with no changes throws"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "First")
    ;; Try to commit again with no changes
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-commit! *temp-dir* "Second")))))

(deftest git-commit-allow-empty-test
  (testing "Allow empty commits"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "First")
    ;; Empty commit should work with :allow-empty
    (let [result (git/git-commit! *temp-dir* "Empty" :allow-empty true)]
      (is (string? (:sha result))))))

(deftest git-commit-with-author-test
  (testing "Commit with custom author"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Test" :author "Bob <bob@example.com>")
    (let [log (git/git-log *temp-dir* :format :short)]
      (is (= "Bob" (:author (first log)))))))

;; =============================================================================
;; git-has-commits? Tests
;; =============================================================================

(deftest git-has-commits-false-test
  (testing "Returns false for empty repo"
    (init-test-repo)
    (is (false? (git/git-has-commits? *temp-dir*)))))

(deftest git-has-commits-true-test
  (testing "Returns true after commit"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    (is (true? (git/git-has-commits? *temp-dir*)))))

;; =============================================================================
;; git-log Tests
;; =============================================================================

(deftest git-log-empty-repo-test
  (testing "Returns nil for empty repo"
    (init-test-repo)
    (is (nil? (git/git-log *temp-dir*)))))

(deftest git-log-single-commit-test
  (testing "Returns single commit"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "First commit")
    (let [log (git/git-log *temp-dir*)]
      (is (= 1 (count log)))
      (is (= "First commit" (:message (first log)))))))

(deftest git-log-multiple-commits-test
  (testing "Returns multiple commits in order"
    (init-test-repo)
    (create-file "a.txt" {:data "a"})
    (git/git-add! *temp-dir* "a.txt")
    (git/git-commit! *temp-dir* "Commit A")
    (create-file "b.txt" {:data "b"})
    (git/git-add! *temp-dir* "b.txt")
    (git/git-commit! *temp-dir* "Commit B")
    (create-file "c.txt" {:data "c"})
    (git/git-add! *temp-dir* "c.txt")
    (git/git-commit! *temp-dir* "Commit C")
    (let [log (git/git-log *temp-dir*)]
      (is (= 3 (count log)))
      ;; Most recent first
      (is (= "Commit C" (:message (first log))))
      (is (= "Commit A" (:message (last log)))))))

(deftest git-log-max-count-test
  (testing "Respects max-count"
    (init-test-repo)
    (dotimes [i 5]
      (create-file (str i ".txt") {:n i})
      (git/git-add! *temp-dir* (str i ".txt"))
      (git/git-commit! *temp-dir* (str "Commit " i)))
    (let [log (git/git-log *temp-dir* :max-count 3)]
      (is (= 3 (count log))))))

(deftest git-log-path-filter-test
  (testing "Filters by path"
    (init-test-repo)
    (create-file "a.txt" {:data "a"})
    (git/git-add! *temp-dir* "a.txt")
    (git/git-commit! *temp-dir* "Add a.txt")
    (create-file "b.txt" {:data "b"})
    (git/git-add! *temp-dir* "b.txt")
    (git/git-commit! *temp-dir* "Add b.txt")
    (create-file "a.txt" {:data "modified"})
    (git/git-add! *temp-dir* "a.txt")
    (git/git-commit! *temp-dir* "Modify a.txt")
    (let [log (git/git-log *temp-dir* :path "a.txt")]
      (is (= 2 (count log)))
      (is (= "Modify a.txt" (:message (first log))))
      (is (= "Add a.txt" (:message (second log)))))))

(deftest git-log-short-format-test
  (testing "Short format includes author"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Test")
    (let [log (git/git-log *temp-dir* :format :short)]
      (is (= "Test User" (:author (first log)))))))

(deftest git-log-full-format-test
  (testing "Full format includes date"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Test")
    (let [log (git/git-log *temp-dir* :format :full)]
      (is (string? (:date (first log))))
      (is (string? (:author (first log)))))))

;; =============================================================================
;; git-has-remote? Tests
;; =============================================================================

(deftest git-has-remote-false-test
  (testing "Returns false when no remote"
    (init-test-repo)
    (is (false? (git/git-has-remote? *temp-dir*)))))

;; =============================================================================
;; git-pull! Tests
;; =============================================================================

(deftest git-pull-no-remote-throws-test
  (testing "Throws when no remote configured"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"No remote configured"
                          (git/git-pull! *temp-dir*)))))

;; =============================================================================
;; git-push! Tests
;; =============================================================================

(deftest git-push-no-remote-throws-test
  (testing "Throws when no remote configured"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"No remote configured"
                          (git/git-push! *temp-dir*)))))

;; =============================================================================
;; Integration Tests
;; =============================================================================

(deftest full-workflow-test
  (testing "Complete workflow: init, add, commit, log"
    (git/git-init! *temp-dir*)
    (git/git-config! *temp-dir* "user.name" "Integration Test")
    (git/git-config! *temp-dir* "user.email" "int@test.com")

    ;; Create .alethfeld structure
    (create-alethfeld-file "config.edn" {:project "Test Project"})
    (create-alethfeld-file "motes/1.edn" {:id "1" :claim "Root"})

    ;; Stage and commit
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* "Initialize proof repository")

    ;; Verify clean
    (is (:clean? (git/git-status *temp-dir*)))

    ;; Add more motes
    (create-alethfeld-file "motes/1/1.1.edn" {:id "1.1" :claim "Child"})
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* "Add child mote")

    ;; Check log
    (let [log (git/git-log *temp-dir*)]
      (is (= 2 (count log)))
      (is (= "Add child mote" (:message (first log)))))))

(deftest alethfeld-directory-workflow-test
  (testing "Staging only .alethfeld changes"
    (init-test-repo)

    ;; Create files inside and outside .alethfeld
    (create-file "readme.md" {:content "readme"})
    (create-alethfeld-file "config.edn" {:project "Test"})
    (create-alethfeld-file "motes/1.edn" {:id "1"})

    ;; Only stage .alethfeld
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* "Init alethfeld")

    (let [status (git/git-status *temp-dir*)]
      ;; readme.md should still be untracked
      (is (some #(= "readme.md" %) (:untracked status)))
      ;; .alethfeld files should be committed
      (is (not (some #(str/includes? % ".alethfeld") (:staged status)))))))

;; =============================================================================
;; Error/Failure Scenario Tests
;; =============================================================================

;; -----------------------------------------------------------------------------
;; Non-Git Directory Failures
;; -----------------------------------------------------------------------------

(deftest git-status-non-git-dir-throws-test
  (testing "git-status on non-git directory throws"
    ;; *temp-dir* is NOT initialized as a git repo
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-status *temp-dir*)))
    ;; Verify the exception info contains useful data
    (try
      (git/git-status *temp-dir*)
      (catch clojure.lang.ExceptionInfo e
        (let [data (ex-data e)]
          (is (= :git-error (:type data)))
          (is (string? (:stderr data)))
          (is (not= 0 (:exit data))))))))

(deftest git-add-non-git-dir-throws-test
  (testing "git-add! on non-git directory throws"
    ;; Create a file but don't init git
    (create-file "test.txt" {:data "test"})
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-add! *temp-dir* "test.txt")))))

(deftest git-add-all-non-git-dir-throws-test
  (testing "git-add-all! on non-git directory throws"
    ;; Create .alethfeld directory but don't init git
    (create-alethfeld-file "config.edn" {:project "Test"})
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-add-all! *temp-dir*)))))

(deftest git-commit-non-git-dir-throws-test
  (testing "git-commit! on non-git directory throws"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-commit! *temp-dir* "Test commit")))))

(deftest git-log-non-git-dir-returns-nil-test
  (testing "git-log on non-git directory returns nil (not throws)"
    ;; Note: git-log calls git-has-commits? first with :check false
    ;; So on a non-git directory, git-has-commits? returns false
    ;; and git-log returns nil without calling git log
    ;; Documenting the actual behavior
    (is (nil? (git/git-log *temp-dir*)))))

(deftest git-has-commits-non-git-dir-returns-false-test
  (testing "git-has-commits? on non-git directory returns false"
    ;; Note: This uses :check false internally, so it returns false instead of throwing
    ;; Documenting the actual behavior
    (is (false? (git/git-has-commits? *temp-dir*)))))

(deftest git-config-set-non-git-dir-throws-test
  (testing "git-config! on non-git directory throws"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-config! *temp-dir* "user.name" "Test")))))

(deftest git-config-get-non-git-dir-returns-global-test
  (testing "git-config (get) on non-git directory returns global config or nil"
    ;; Note: Uses :check false, so it doesn't throw
    ;; Git will return global config values if they exist
    ;; The behavior depends on whether global git config is set
    ;; We just verify it doesn't throw and returns something (or nil)
    (let [result (git/git-config *temp-dir* "user.name")]
      (is (or (nil? result) (string? result))))))

;; -----------------------------------------------------------------------------
;; git-commit! Edge Cases
;; -----------------------------------------------------------------------------

(deftest git-commit-no-staged-changes-throws-test
  (testing "git-commit! with unstaged changes but nothing staged throws"
    (init-test-repo)
    ;; Create initial commit
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    ;; Create changes but don't stage them
    (create-file "new.txt" {:data "new"})
    ;; Verify unstaged changes exist
    (let [status (git/git-status *temp-dir*)]
      (is (seq (:untracked status))))
    ;; Commit should fail - nothing staged
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-commit! *temp-dir* "Should fail")))))

(deftest git-commit-allow-empty-on-fresh-repo-test
  (testing "git-commit! with :allow-empty on fresh repo (no prior commits)"
    (init-test-repo)
    ;; Empty commit on repo with no commits should work
    (let [result (git/git-commit! *temp-dir* "Empty initial" :allow-empty true)]
      (is (string? (:sha result)))
      (is (= "Empty initial" (:message result)))
      ;; Verify commit exists
      (is (true? (git/git-has-commits? *temp-dir*))))))

(deftest git-commit-allow-empty-multiple-times-test
  (testing "Multiple :allow-empty commits in sequence"
    (init-test-repo)
    (git/git-commit! *temp-dir* "Empty 1" :allow-empty true)
    (git/git-commit! *temp-dir* "Empty 2" :allow-empty true)
    (git/git-commit! *temp-dir* "Empty 3" :allow-empty true)
    (let [log (git/git-log *temp-dir*)]
      (is (= 3 (count log)))
      (is (= "Empty 3" (:message (first log))))
      (is (= "Empty 1" (:message (last log)))))))

(deftest git-commit-empty-message-throws-test
  (testing "git-commit! with empty message string throws"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    ;; Git rejects empty commit messages
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-commit! *temp-dir* "")))))

;; -----------------------------------------------------------------------------
;; git-init! Edge Cases
;; -----------------------------------------------------------------------------

(deftest git-init-double-init-preserves-state-test
  (testing "Double git-init! preserves existing commits and config"
    (git/git-init! *temp-dir*)
    (git/git-config! *temp-dir* "user.name" "First User")
    (git/git-config! *temp-dir* "user.email" "first@example.com")
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "First commit")
    ;; Call init again - should be no-op
    (git/git-init! *temp-dir*)
    ;; Verify state preserved
    (is (= "First User" (git/git-config *temp-dir* "user.name")))
    (is (true? (git/git-has-commits? *temp-dir*)))
    (let [log (git/git-log *temp-dir*)]
      (is (= 1 (count log)))
      (is (= "First commit" (:message (first log)))))))

(deftest git-init-on-nested-non-existent-path-test
  (testing "git-init! creates parent directories if needed"
    (let [nested-path (str *temp-dir* "/deep/nested/repo")]
      (git/git-init! nested-path)
      (is (fs/directory? (str nested-path "/.git"))))))

(deftest git-init-different-branch-names-test
  (testing "git-init! with various branch names"
    (doseq [branch-name ["main" "master" "trunk" "develop" "my-branch"]]
      (let [repo-path (str (fs/create-temp-dir {:prefix "git-init-branch-"}))]
        (try
          (git/git-init! repo-path :initial-branch branch-name)
          (git/git-config! repo-path "user.name" "Test")
          (git/git-config! repo-path "user.email" "test@example.com")
          ;; Write file directly using spit (not our create-file helper which uses a different path)
          (spit (str repo-path "/test.txt") "{:data \"test\"}")
          ;; Use relative path for git add
          (git/git-add! repo-path "test.txt")
          (git/git-commit! repo-path "Initial")
          ;; Verify branch was created
          (is (fs/exists? (str repo-path "/.git/refs/heads/" branch-name))
              (str "Branch " branch-name " should exist"))
          (finally
            (fs/delete-tree repo-path)))))))

;; -----------------------------------------------------------------------------
;; git-log Edge Cases
;; -----------------------------------------------------------------------------

(deftest git-log-on-repo-with-no-commits-returns-nil-test
  (testing "git-log returns nil on initialized repo with no commits"
    (init-test-repo)
    ;; Repo is initialized but has no commits
    (is (nil? (git/git-log *temp-dir*)))
    ;; Also verify git-has-commits? returns false
    (is (false? (git/git-has-commits? *temp-dir*)))))

(deftest git-log-path-filter-nonexistent-file-test
  (testing "git-log with path filter for non-existent file returns empty"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    ;; Filter by path that was never committed
    (let [log (git/git-log *temp-dir* :path "nonexistent.txt")]
      (is (empty? log)))))

(deftest git-log-max-count-zero-test
  (testing "git-log with max-count 0 returns empty"
    (init-test-repo)
    (create-file "test.txt" {:data "test"})
    (git/git-add! *temp-dir* "test.txt")
    (git/git-commit! *temp-dir* "Initial")
    (let [log (git/git-log *temp-dir* :max-count 0)]
      (is (empty? log)))))

;; -----------------------------------------------------------------------------
;; git-add! Edge Cases
;; -----------------------------------------------------------------------------

(deftest git-add-empty-paths-vector-test
  (testing "git-add! with empty paths vector is no-op"
    (init-test-repo)
    ;; Should not throw
    (is (= *temp-dir* (git/git-add! *temp-dir* [])))))

(deftest git-add-nonexistent-file-throws-test
  (testing "git-add! with non-existent file throws"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-add! *temp-dir* "does-not-exist.txt")))))

(deftest git-add-all-empty-alethfeld-dir-test
  (testing "git-add-all! with empty .alethfeld directory"
    (init-test-repo)
    ;; Create empty .alethfeld directory
    (fs/create-dirs (str *temp-dir* "/.alethfeld"))
    ;; Should not throw, but there's nothing to add
    (is (= *temp-dir* (git/git-add-all! *temp-dir*)))))

(deftest git-add-all-no-alethfeld-dir-throws-test
  (testing "git-add-all! with no .alethfeld directory throws"
    (init-test-repo)
    ;; No .alethfeld directory exists
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Git command failed"
                          (git/git-add-all! *temp-dir*)))))

;; -----------------------------------------------------------------------------
;; Exception Data Verification
;; -----------------------------------------------------------------------------

(deftest git-error-exception-data-test
  (testing "Git errors include useful exception data"
    (init-test-repo)
    (try
      ;; Try to add a non-existent file
      (git/git-add! *temp-dir* "nonexistent.txt")
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (let [data (ex-data e)]
          (is (= :git-error (:type data)))
          (is (string? (:command data)))
          (is (str/includes? (:command data) "git add"))
          (is (integer? (:exit data)))
          (is (not= 0 (:exit data)))
          (is (string? (:stderr data)))
          (is (string? (:stdout data))))))))
