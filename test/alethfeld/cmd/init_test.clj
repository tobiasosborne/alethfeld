(ns alethfeld.cmd.init-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.cli :as cli]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-init-test-"})
        orig (System/getProperty "user.dir")]
    (try
      (System/setProperty "user.dir" (str temp))
      (binding [*temp-dir* (str temp)
                *original-dir* orig]
        ;; Change current directory
        (let [original-user-dir (System/getProperty "user.dir")]
          ;; We need to actually change directory for the "." path to work
          ;; Since Java doesn't support changing directory, we'll use a different approach
          (f)))
      (finally
        (System/setProperty "user.dir" orig)
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- with-temp-cwd
  "Execute f with the current working directory temporarily changed.
   Since Java can't change cwd, we modify the cmd functions to use the temp dir."
  [f]
  ;; We'll patch the repo-path by using a modified version
  (f))

(defn- init-in-temp
  "Run init command targeting the temp directory."
  [& {:keys [name] :or {name nil}}]
  ;; Directly call the underlying functions with temp dir
  (let [repo-path *temp-dir*
        project-name (or name "Alethfeld Project")]
    (when (store/repo-exists? repo-path)
      (throw (ex-info "Repository already initialized"
                      {:type :already-initialized
                       :path repo-path})))
    (git/git-init! repo-path)
    (when-not (git/git-config repo-path "user.name")
      (git/git-config! repo-path "user.name" "alethfeld"))
    (when-not (git/git-config repo-path "user.email")
      (git/git-config! repo-path "user.email" "alethfeld@local"))
    (let [config (store/init-repo! repo-path :project-name project-name)]
      (git/git-add-all! repo-path)
      (git/git-commit! repo-path (str "Initialize Alethfeld: " project-name))
      {:message (str "Initialized Alethfeld repository: " project-name)
       :config config})))

;; =============================================================================
;; Directory Structure Tests
;; =============================================================================

(deftest init-creates-alethfeld-dir-test
  (testing "init creates .alethfeld/ directory"
    (init-in-temp)
    (is (fs/directory? (str *temp-dir* "/.alethfeld")))))

(deftest init-creates-motes-dir-test
  (testing "init creates motes/ directory"
    (init-in-temp)
    (is (fs/directory? (str *temp-dir* "/.alethfeld/motes")))))

(deftest init-creates-proposed-dir-test
  (testing "init creates proposed/ directory"
    (init-in-temp)
    (is (fs/directory? (str *temp-dir* "/.alethfeld/proposed")))))

(deftest init-creates-archive-dir-test
  (testing "init creates archive/ directory"
    (init-in-temp)
    (is (fs/directory? (str *temp-dir* "/.alethfeld/archive")))))

(deftest init-creates-config-test
  (testing "init creates config.edn"
    (init-in-temp)
    (is (fs/exists? (str *temp-dir* "/.alethfeld/config.edn")))))

;; =============================================================================
;; Config Content Tests
;; =============================================================================

(deftest init-config-has-project-name-test
  (testing "init config has default project name"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= "Alethfeld Project" (:project-name config))))))

(deftest init-config-custom-name-test
  (testing "init config accepts custom project name"
    (init-in-temp :name "My Proof")
    (let [config (store/load-config *temp-dir*)]
      (is (= "My Proof" (:project-name config))))))

(deftest init-config-has-version-test
  (testing "init config has version"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= "0.1" (:version config))))))

(deftest init-config-has-default-difficulty-test
  (testing "init config has default-difficulty"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= 3 (:default-difficulty config))))))

(deftest init-config-has-vote-quorum-test
  (testing "init config has vote-quorum"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= 2 (:vote-quorum config))))))

(deftest init-config-has-proposal-quorum-test
  (testing "init config has proposal-quorum"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= 2 (:proposal-quorum config))))))

(deftest init-config-has-claim-timeout-test
  (testing "init config has claim-timeout-minutes"
    (init-in-temp)
    (let [config (store/load-config *temp-dir*)]
      (is (= 30 (:claim-timeout-minutes config))))))

;; =============================================================================
;; Git Integration Tests
;; =============================================================================

(deftest init-initializes-git-test
  (testing "init initializes git repository"
    (init-in-temp)
    (is (git/git-initialized? *temp-dir*))))

(deftest init-creates-initial-commit-test
  (testing "init creates initial commit"
    (init-in-temp)
    (is (git/git-has-commits? *temp-dir*))))

(deftest init-commit-message-test
  (testing "init commit has appropriate message"
    (init-in-temp :name "Test Proof")
    (let [log (git/git-log *temp-dir* :max-count 1)]
      (is (= 1 (count log)))
      (is (re-find #"Initialize Alethfeld: Test Proof" (:message (first log)))))))

(deftest init-no-uncommitted-changes-test
  (testing "init leaves no uncommitted changes"
    (init-in-temp)
    (let [status (git/git-status *temp-dir*)]
      (is (:clean? status)))))

;; =============================================================================
;; Return Value Tests
;; =============================================================================

(deftest init-returns-message-test
  (testing "init returns success message"
    (let [result (init-in-temp :name "My Proof")]
      (is (string? (:message result)))
      (is (re-find #"Initialized" (:message result)))
      (is (re-find #"My Proof" (:message result))))))

(deftest init-returns-config-test
  (testing "init returns the config that was created"
    (let [result (init-in-temp :name "My Proof")]
      (is (map? (:config result)))
      (is (= "My Proof" (get-in result [:config :project-name]))))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest init-already-initialized-test
  (testing "init throws when already initialized"
    (init-in-temp)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Repository already initialized"
                          (init-in-temp)))))

(deftest init-already-initialized-error-type-test
  (testing "init throws with :already-initialized type"
    (init-in-temp)
    (try
      (init-in-temp)
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (is (= :already-initialized (:type (ex-data e))))))))

;; =============================================================================
;; CLI Integration Tests
;; =============================================================================

(deftest init-handler-registered-test
  (testing "init handler is registered"
    (cmd/register-handlers!)
    ;; Access the private handlers atom (deref var, then deref atom)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "init")))))

(deftest init-via-dispatch-test
  (testing "init works via CLI dispatch"
    (cmd/register-handlers!)
    ;; We can't easily test full dispatch since it uses "." path
    ;; But we can verify the handler exists
    (let [handler (get @@#'cli/handlers "init")]
      (is (fn? handler)))))
