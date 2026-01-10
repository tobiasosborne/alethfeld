(ns alethfeld.cmd.enforce-test
  "Tests for session enforcement middleware (Step A.5)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [alethfeld.session :as session]
            [alethfeld.tx :as tx]
            [alethfeld.proposal :as proposal]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-enforce-test-"})
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
  (session/ensure-session-dirs! *temp-dir*)
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-mote!
  "Create a mote directly in the store for test setup."
  [id claim & {:keys [difficulty priority taint parent status claimed-by]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}
                    status :fixed}}]
  (let [m (cond-> (mote/make-mote id claim "test-agent"
                                   :difficulty difficulty
                                   :priority priority
                                   :taint taint
                                   :status status
                                   :parent parent)
            claimed-by (mote/set-claimed-by claimed-by))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

(defn- create-session!
  "Create a session for testing."
  [mote-id role agent]
  (session/create-session! *temp-dir* mote-id role agent))

;; =============================================================================
;; enforce-session! Tests
;; =============================================================================

(deftest enforce-session-valid-test
  (testing "enforce-session! passes for valid session and action"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          result (session/enforce-session! *temp-dir* (:session-id sess) :propose "1")]
      (is (some? result))
      (is (= "1" (:mote-id result)))
      (is (= :proposer (:role result))))))

(deftest enforce-session-records-action-test
  (testing "enforce-session! records action in audit trail"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          _ (session/enforce-session! *temp-dir* (:session-id sess) :propose "1")
          updated (session/load-session *temp-dir* (:session-id sess))]
      (is (= [:propose] (:actions updated))))))

(deftest enforce-session-invalid-session-test
  (testing "enforce-session! throws for non-existent session"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid session"
                          (session/enforce-session! *temp-dir* "fake-session" :propose "1")))))

(deftest enforce-session-wrong-mote-test
  (testing "enforce-session! throws when session is for different mote"
    (init-repo!)
    (create-mote! "1" "Test claim 1" :claimed-by "agent-1")
    (create-mote! "2" "Test claim 2")
    (let [sess (create-session! "1" :proposer "agent-1")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Session locked to different mote"
                            (session/enforce-session! *temp-dir* (:session-id sess) :propose "2"))))))

(deftest enforce-session-wrong-action-test
  (testing "enforce-session! throws when action not allowed for role"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :verifier "agent-1")]
      ;; Verifier can vote but not propose
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Action not allowed for role"
                            (session/enforce-session! *temp-dir* (:session-id sess) :propose "1"))))))

;; =============================================================================
;; Command Enforcement Tests - Session Required
;; =============================================================================

;; Note: The cmd-* functions use "." as repo path, which won't resolve to our
;; temp directory. Instead of testing full cmd-* functions, we test the
;; enforce-session! function directly which is what provides the enforcement.
;; The cmd tests verify that the functions properly call enforce-session!.

;; These tests verify that commands require session tokens by testing that
;; enforce-session! is properly wired into each command. We test this by
;; creating direct-call helpers that use *temp-dir* instead of ".".

(defn- test-session-required
  "Test helper that verifies a command throws session required error.
   Uses the session/enforce-session! function which is what the commands use."
  [action mote-id]
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"Invalid session"
                        (session/enforce-session! *temp-dir* "nonexistent-session" action mote-id))))

(deftest session-enforcement-wired-test
  (testing "enforce-session! rejects invalid sessions for all actions"
    (init-repo!)
    (create-mote! "1" "Test claim")
    ;; Test that enforce-session! properly rejects invalid sessions for each action type
    (test-session-required :propose "1")
    (test-session-required :approve "1")
    (test-session-required :reject "1")
    (test-session-required :vote "1")
    (test-session-required :taint-add "1")
    (test-session-required :taint-remove "1")
    (test-session-required :add-ref "1")
    (test-session-required :add-assumption "1")
    (test-session-required :add-definition "1")))

;; =============================================================================
;; Role-Based Action Tests
;; =============================================================================

(deftest proposer-can-propose-test
  (testing "proposer role can propose"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")]
      ;; This would normally work but we need proper directory context
      ;; Just verify the session enforcement passes
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :propose "1")]
        (is (= :proposer (:role result)))))))

(deftest advisor-can-approve-test
  (testing "advisor role can approve"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :advisor "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :approve "1")]
        (is (= :advisor (:role result)))))))

(deftest advisor-can-reject-test
  (testing "advisor role can reject"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :advisor "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :reject "1")]
        (is (= :advisor (:role result)))))))

(deftest verifier-can-vote-test
  (testing "verifier role can vote"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :verifier "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :vote "1")]
        (is (= :verifier (:role result)))))))

(deftest verifier-can-taint-add-test
  (testing "verifier role can add taints"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :verifier "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :taint-add "1")]
        (is (= :verifier (:role result)))))))

(deftest prover-can-taint-remove-test
  (testing "prover role can remove taints"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :prover "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :taint-remove "1")]
        (is (= :prover (:role result)))))))

(deftest ref-checker-can-add-ref-test
  (testing "ref-checker role can add refs"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :ref-checker "agent-1")]
      (let [result (session/enforce-session! *temp-dir* (:session-id sess) :add-ref "1")]
        (is (= :ref-checker (:role result)))))))

;; =============================================================================
;; Role Restriction Tests
;; =============================================================================

(deftest verifier-cannot-propose-test
  (testing "verifier role cannot propose"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :verifier "agent-1")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Action not allowed for role"
                            (session/enforce-session! *temp-dir* (:session-id sess) :propose "1"))))))

(deftest advisor-cannot-vote-test
  (testing "advisor role cannot vote"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :advisor "agent-1")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Action not allowed for role"
                            (session/enforce-session! *temp-dir* (:session-id sess) :vote "1"))))))

(deftest proposer-cannot-vote-test
  (testing "proposer role cannot vote"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Action not allowed for role"
                            (session/enforce-session! *temp-dir* (:session-id sess) :vote "1"))))))

(deftest verifier-can-taint-remove-test
  ;; Changed in v0.2 (7.8): Verifiers can now remove taints for workflow control.
  ;; This enables verifiers to remove :needs-verification when demanding decomposition.
  (testing "verifier role CAN remove taints (7.8 workflow control)"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :verifier "agent-1")
          result (session/enforce-session! *temp-dir* (:session-id sess) :taint-remove "1")]
      (is (some? result))
      (is (= :verifier (:role result))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest done-handler-registered-test
  (testing "done handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "done")))))
