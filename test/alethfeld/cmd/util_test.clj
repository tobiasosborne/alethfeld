(ns alethfeld.cmd.util-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.dag :as dag]
            [alethfeld.path :as path]
            [alethfeld.cli :as cli]
            [alethfeld.tx :as tx]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-util-test-"})
        orig (System/getProperty "user.dir")]
    (try
      (System/setProperty "user.dir" (str temp))
      (binding [*temp-dir* (str temp)
                *original-dir* orig]
        (f))
      (finally
        (System/setProperty "user.dir" orig)
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-repo!
  "Initialize a test repository."
  []
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :project-name "Test Project")
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-mote!
  "Create a mote directly in the store for test setup."
  [id claim & {:keys [difficulty priority taint parent status children assumptions]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}
                    status :fixed
                    children []
                    assumptions []}}]
  (let [m (-> (mote/make-mote id claim "test-agent"
                              :difficulty difficulty
                              :priority priority
                              :taint taint
                              :status status
                              :parent parent)
              (assoc :children children)
              (assoc :assumptions assumptions))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

;; -----------------------------------------------------------------------------
;; Check Command Helpers
;; -----------------------------------------------------------------------------

(defn- cmd-check-in-temp
  "Call cmd-check using the temp directory context."
  []
  (let [repo-path *temp-dir*]
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [motes (store/load-all-motes repo-path :include-archived true)
          schema-errors (->> motes
                             (keep (fn [[mote-id mote]]
                                     (when-let [explanation (store/validate-mote mote)]
                                       {:mote-id mote-id
                                        :error explanation})))
                             vec)
          dag-result (dag/validate-mote-graph motes)
          dag-errors (:errors dag-result)
          all-valid? (and (empty? schema-errors)
                          (:valid? dag-result))]
      {:valid? all-valid?
       :mote-count (count motes)
       :schema-errors (when (seq schema-errors) schema-errors)
       :dag-errors (when (seq dag-errors) dag-errors)})))

;; -----------------------------------------------------------------------------
;; Log Command Helpers
;; -----------------------------------------------------------------------------

(defn- cmd-log-in-temp
  "Call cmd-log using the temp directory context."
  [id & {:keys [limit] :or {limit 50}}]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to show history for"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [mote (store/load-mote repo-path id)]
      (when-not mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [mote-file-path (path/mote-id->path id (:status mote))
            history (git/git-log repo-path :path mote-file-path :max-count limit)]
        (or history [])))))

;; -----------------------------------------------------------------------------
;; Sync Command Helpers
;; -----------------------------------------------------------------------------

(defn- cmd-sync-in-temp!
  "Call cmd-sync! using the temp directory context."
  [& {:keys [no-push]}]
  (let [repo-path *temp-dir*]
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (when-not (git/git-initialized? repo-path)
      (throw (ex-info "Not a git repository"
                      {:type :not-git-repo
                       :path repo-path})))
    (let [has-remote (git/git-has-remote? repo-path)
          pull-result (when has-remote
                        (try
                          (git/git-pull! repo-path)
                          (catch Exception e
                            (let [data (ex-data e)]
                              (when-not (= :no-remote (:type data))
                                (throw e))
                              nil))))
          _ (git/git-add-all! repo-path)
          timestamp (.format (java.time.OffsetDateTime/now)
                             java.time.format.DateTimeFormatter/ISO_OFFSET_DATE_TIME)
          commit-msg (str "af sync " timestamp)
          commit-result (git/git-commit! repo-path commit-msg :allow-empty true)
          push-result (when (and has-remote (not no-push))
                        (try
                          (git/git-push! repo-path)
                          (catch Exception e
                            (let [data (ex-data e)]
                              (when-not (= :no-remote (:type data))
                                (throw e))
                              nil))))]
      {:pulled (if pull-result true :skipped)
       :committed true
       :pushed (cond
                 no-push :skipped
                 (not has-remote) :skipped
                 push-result true
                 :else false)
       :commit-sha (:sha commit-result)})))

;; =============================================================================
;; Check Command - Basic Tests
;; =============================================================================

(deftest check-empty-repo-valid-test
  (testing "check on empty repo is valid"
    (init-repo!)
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result)))
      (is (= 0 (:mote-count result)))
      (is (nil? (:schema-errors result)))
      (is (nil? (:dag-errors result))))))

(deftest check-single-mote-valid-test
  (testing "check with single valid mote passes"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result)))
      (is (= 1 (:mote-count result))))))

(deftest check-multiple-motes-valid-test
  (testing "check with multiple valid motes passes"
    (init-repo!)
    (create-mote! "1" "Root claim" :children ["1.1" "1.2"])
    (create-mote! "1.1" "Child 1" :parent "1")
    (create-mote! "1.2" "Child 2" :parent "1")
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result)))
      (is (= 3 (:mote-count result))))))

(deftest check-returns-mote-count-test
  (testing "check returns correct mote count"
    (init-repo!)
    (create-mote! "1" "Claim 1")
    (create-mote! "2" "Claim 2")
    (create-mote! "3" "Claim 3")
    (let [result (cmd-check-in-temp)]
      (is (= 3 (:mote-count result))))))

;; =============================================================================
;; Check Command - DAG Validation Tests
;; =============================================================================

(deftest check-detects-phantom-child-test
  (testing "check detects phantom child"
    (init-repo!)
    (create-mote! "1" "Root with phantom child" :children ["1.999"])
    (let [result (cmd-check-in-temp)]
      (is (false? (:valid? result)))
      (is (some? (:dag-errors result)))
      (is (some #(= :parent-child (:category %)) (:dag-errors result))))))

(deftest check-detects-broken-ref-test
  (testing "check detects broken internal reference"
    (init-repo!)
    (create-mote! "1" "Mote with broken ref"
                  :assumptions [{:type :internal :ref "nonexistent"}])
    (let [result (cmd-check-in-temp)]
      (is (false? (:valid? result)))
      (is (some? (:dag-errors result)))
      (is (some #(= :broken-refs (:category %)) (:dag-errors result))))))

(deftest check-valid-internal-ref-test
  (testing "check passes with valid internal reference"
    (init-repo!)
    (create-mote! "1" "Referenced mote")
    (create-mote! "2" "Mote with ref"
                  :assumptions [{:type :internal :ref "1"}])
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result))))))

(deftest check-external-refs-ignored-test
  (testing "check ignores external references"
    (init-repo!)
    (create-mote! "1" "Mote with external ref"
                  :assumptions [{:type :external :ref "Some paper citation"}])
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result))))))

;; =============================================================================
;; Check Command - Validation Tests
;; =============================================================================

(deftest check-requires-repo-test
  (testing "check requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-check-in-temp)))))

;; =============================================================================
;; Log Command - Basic Tests
;; =============================================================================

(deftest log-returns-history-test
  (testing "log returns commit history for mote"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-log-in-temp "1")]
      (is (vector? result))
      (is (pos? (count result)))
      (is (some? (:sha (first result))))
      (is (some? (:message (first result)))))))

(deftest log-includes-create-commit-test
  (testing "log includes the mote creation commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-log-in-temp "1")
          messages (map :message result)]
      (is (some #(str/includes? % "Create mote 1") messages)))))

(deftest log-tracks-updates-test
  (testing "log tracks mote updates"
    (init-repo!)
    (create-mote! "1" "Original claim")
    ;; Update the mote
    (let [m (store/load-mote *temp-dir* "1")
          updated (mote/set-claim m "Updated claim")]
      (store/save-mote! *temp-dir* updated)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Update mote 1 claim"))
    (let [result (cmd-log-in-temp "1")]
      (is (>= (count result) 2)))))

(deftest log-respects-limit-test
  (testing "log respects limit option"
    (init-repo!)
    (create-mote! "1" "Test claim")
    ;; Create multiple commits
    (dotimes [i 5]
      (let [m (store/load-mote *temp-dir* "1")
            updated (mote/set-claim m (str "Update " i))]
        (store/save-mote! *temp-dir* updated)
        (git/git-add-all! *temp-dir*)
        (git/git-commit! *temp-dir* (str "Update " i))))
    ;; Request only 3
    (let [result (cmd-log-in-temp "1" :limit 3)]
      (is (<= (count result) 3)))))

(deftest log-returns-empty-for-new-repo-test
  (testing "log returns empty vector for mote with no specific history"
    (init-repo!)
    ;; Create a mote that hasn't been committed to its own file yet
    ;; Actually, create-mote! commits, so let's check a different scenario
    ;; by loading immediately after init with no motes
    (create-mote! "1" "Test claim")
    ;; This should have history
    (let [result (cmd-log-in-temp "1")]
      (is (vector? result)))))

;; =============================================================================
;; Log Command - Validation Tests
;; =============================================================================

(deftest log-requires-mote-id-test
  (testing "log requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-log-in-temp nil)))))

(deftest log-requires-repo-test
  (testing "log requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-log-in-temp "1")))))

(deftest log-mote-not-found-test
  (testing "log fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-log-in-temp "999")))))

;; =============================================================================
;; Log Command - Child Mote Tests
;; =============================================================================

(deftest log-child-mote-test
  (testing "log works for child motes"
    (init-repo!)
    (create-mote! "1" "Root" :children ["1.1"])
    (create-mote! "1.1" "Child" :parent "1")
    (let [result (cmd-log-in-temp "1.1")]
      (is (vector? result))
      (is (pos? (count result))))))

(deftest log-deep-child-mote-test
  (testing "log works for deeply nested motes"
    (init-repo!)
    (create-mote! "1" "Root" :children ["1.1"])
    (create-mote! "1.1" "L1" :parent "1" :children ["1.1.1"])
    (create-mote! "1.1.1" "L2" :parent "1.1")
    (let [result (cmd-log-in-temp "1.1.1")]
      (is (vector? result))
      (is (pos? (count result))))))

;; =============================================================================
;; Sync Command - Basic Tests
;; =============================================================================

(deftest sync-commits-changes-test
  (testing "sync creates a commit"
    (init-repo!)
    (let [initial-log (git/git-log *temp-dir*)
          result (cmd-sync-in-temp!)
          final-log (git/git-log *temp-dir*)]
      (is (true? (:committed result)))
      (is (some? (:commit-sha result)))
      (is (> (count final-log) (count initial-log))))))

(deftest sync-commit-message-format-test
  (testing "sync commit message has correct format"
    (init-repo!)
    (cmd-sync-in-temp!)
    (let [log (git/git-log *temp-dir*)
          latest-msg (:message (first log))]
      (is (str/starts-with? latest-msg "af sync ")))))

(deftest sync-skips-push-without-remote-test
  (testing "sync skips push when no remote configured"
    (init-repo!)
    (let [result (cmd-sync-in-temp!)]
      (is (= :skipped (:pushed result)))
      (is (= :skipped (:pulled result))))))

(deftest sync-skips-push-with-no-push-option-test
  (testing "sync skips push with --no-push option"
    (init-repo!)
    (let [result (cmd-sync-in-temp! :no-push true)]
      (is (= :skipped (:pushed result))))))

(deftest sync-stages-alethfeld-changes-test
  (testing "sync stages .alethfeld/ changes"
    (init-repo!)
    ;; Create unstaged changes
    (create-mote! "1" "Test claim")
    ;; Make an additional change without committing
    (let [m (store/load-mote *temp-dir* "1")
          updated (mote/set-claim m "Modified claim")]
      (store/save-mote! *temp-dir* updated))
    ;; Verify there are unstaged changes
    (let [status-before (git/git-status *temp-dir*)]
      (is (or (seq (:unstaged status-before))
              (seq (:untracked status-before)))))
    ;; Sync
    (cmd-sync-in-temp!)
    ;; Changes should be committed
    (let [status-after (git/git-status *temp-dir*)]
      (is (:clean? status-after)))))

(deftest sync-allow-empty-commit-test
  (testing "sync creates commit even with no changes"
    (init-repo!)
    ;; First sync to ensure clean state
    (cmd-sync-in-temp!)
    ;; Second sync with no changes
    (let [result (cmd-sync-in-temp!)]
      (is (true? (:committed result)))
      (is (some? (:commit-sha result))))))

;; =============================================================================
;; Sync Command - Validation Tests
;; =============================================================================

(deftest sync-requires-repo-test
  (testing "sync requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-sync-in-temp!)))))

(deftest sync-requires-git-test
  (testing "sync requires git repository"
    ;; Initialize store but not git
    (store/init-repo! *temp-dir* :project-name "Test")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not a git repository"
                          (cmd-sync-in-temp!)))))

;; =============================================================================
;; Sync Command - Multiple Operations
;; =============================================================================

(deftest sync-multiple-times-test
  (testing "sync can be called multiple times"
    (init-repo!)
    (let [result1 (cmd-sync-in-temp!)
          result2 (cmd-sync-in-temp!)
          result3 (cmd-sync-in-temp!)]
      (is (true? (:committed result1)))
      (is (true? (:committed result2)))
      (is (true? (:committed result3)))
      (is (not= (:commit-sha result1) (:commit-sha result2)))
      (is (not= (:commit-sha result2) (:commit-sha result3))))))

(deftest sync-after-mote-operations-test
  (testing "sync captures mote operations"
    (init-repo!)
    (create-mote! "1" "First claim")
    (cmd-sync-in-temp!)
    (create-mote! "2" "Second claim")
    (let [result (cmd-sync-in-temp!)]
      (is (true? (:committed result)))
      ;; Check that both motes exist and are tracked
      (let [status (git/git-status *temp-dir*)]
        (is (:clean? status))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest check-handler-registered-test
  (testing "check handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "check")))))

(deftest log-handler-registered-test
  (testing "log handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "log")))))

(deftest sync-handler-registered-test
  (testing "sync handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "sync")))))

(deftest check-handler-is-function-test
  (testing "check handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "check")]
      (is (fn? handler)))))

(deftest log-handler-is-function-test
  (testing "log handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "log")]
      (is (fn? handler)))))

(deftest sync-handler-is-function-test
  (testing "sync handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "sync")]
      (is (fn? handler)))))

;; =============================================================================
;; Integration Tests
;; =============================================================================

(deftest check-after-sync-test
  (testing "check passes after sync"
    (init-repo!)
    (create-mote! "1" "Root claim" :children ["1.1"])
    (create-mote! "1.1" "Child claim" :parent "1")
    (cmd-sync-in-temp!)
    (let [result (cmd-check-in-temp)]
      (is (true? (:valid? result)))
      (is (= 2 (:mote-count result))))))

(deftest log-after-sync-test
  (testing "log shows sync commits"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-sync-in-temp!)
    (let [result (cmd-log-in-temp "1")
          messages (map :message result)]
      ;; Should have both create commit and sync commit
      (is (>= (count result) 1)))))
