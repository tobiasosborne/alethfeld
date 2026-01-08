(ns alethfeld.cmd.done-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [alethfeld.session :as session]
            [alethfeld.tx :as tx]
            [alethfeld.io :as io]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-done-test-"})
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

(defn- cmd-done-in-temp!
  "Call cmd-done! using the temp directory context."
  [session-id]
  (let [repo-path *temp-dir*]
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with the session token"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [sess (session/load-active-session repo-path session-id)]
      (when-not sess
        (throw (ex-info "Session not found or already ended"
                        {:type :session-not-found
                         :session-id session-id})))
      (when (session/session-expired? sess)
        (throw (ex-info "Session has expired"
                        {:type :session-expired
                         :session-id session-id
                         :expires-at (:expires-at sess)})))
      (let [mote-id (:mote-id sess)
            mote (store/load-mote repo-path mote-id)]
        (when-not mote
          (throw (ex-info "Mote not found for session"
                          {:type :integrity-error
                           :session-id session-id
                           :mote-id mote-id})))
        (let [ended-session (session/end-session! repo-path session-id :record-stats true)
              updated-mote (mote/clear-claim mote)]
          (tx/atomic-write! repo-path
                            (str "Done: end session for " mote-id)
                            [updated-mote])
          {:session-id session-id
           :mote-id mote-id
           :action-count (:action-count ended-session)})))))

;; =============================================================================
;; Done Command - Basic Tests
;; =============================================================================

(deftest done-ends-session-test
  (testing "done ends the session"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      ;; Session should be active
      (is (session/session-active? *temp-dir* session-id))
      ;; Call done
      (cmd-done-in-temp! session-id)
      ;; Session should no longer be active
      (is (not (session/session-active? *temp-dir* session-id))))))

(deftest done-clears-mote-claim-test
  (testing "done clears the mote claim"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      (cmd-done-in-temp! session-id)
      (let [mote (store/load-mote *temp-dir* "1")]
        (is (nil? (:claimed-by mote)))
        (is (nil? (:claimed-at mote)))))))

(deftest done-returns-session-info-test
  (testing "done returns session info"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)
          result (cmd-done-in-temp! session-id)]
      (is (= session-id (:session-id result)))
      (is (= "1" (:mote-id result)))
      (is (number? (:action-count result))))))

(deftest done-records-stats-test
  (testing "done records completion stats in session"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      ;; Record some actions
      (session/record-action! *temp-dir* session-id :propose)
      (session/record-action! *temp-dir* session-id :add-definition)
      ;; Call done
      (let [result (cmd-done-in-temp! session-id)]
        (is (= 2 (:action-count result)))))))

(deftest done-moves-session-to-completed-test
  (testing "done moves session to completed directory"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      (cmd-done-in-temp! session-id)
      ;; Session should be loadable from completed (via load-session)
      (let [completed (session/load-session *temp-dir* session-id)]
        (is (some? completed))
        (is (= session-id (:session-id completed)))
        ;; Should have completion stats
        (is (some? (:completed-at completed)))
        (is (number? (:action-count completed)))))))

(deftest done-creates-git-commit-test
  (testing "done creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)
          initial-count (count (git/git-log *temp-dir*))]
      (cmd-done-in-temp! session-id)
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest done-allows-mote-reclaim-test
  (testing "done allows mote to be claimed again"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      ;; End session
      (cmd-done-in-temp! session-id)
      ;; Create new session for different agent
      (let [new-sess (create-session! "1" :verifier "agent-2")]
        (is (some? new-sess))
        (is (= "1" (:mote-id new-sess)))
        (is (= :verifier (:role new-sess)))
        (is (= "agent-2" (:agent new-sess)))))))

;; =============================================================================
;; Done Command - Validation Tests
;; =============================================================================

(deftest done-requires-session-test
  (testing "done requires session token"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Session token is required"
                          (cmd-done-in-temp! nil)))))

(deftest done-requires-repo-test
  (testing "done requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-done-in-temp! "fake-session-id")))))

(deftest done-session-not-found-test
  (testing "done fails when session not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Session not found"
                          (cmd-done-in-temp! "nonexistent-session-id")))))

(deftest done-already-ended-test
  (testing "done fails when session already ended"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      ;; End session first time
      (cmd-done-in-temp! session-id)
      ;; Try to end again
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Session not found"
                            (cmd-done-in-temp! session-id))))))

;; =============================================================================
;; Done Command - Edge Cases
;; =============================================================================

(deftest done-preserves-mote-fields-test
  (testing "done preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p1 :difficulty 4
                  :taint #{:needs-verification} :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)]
      (cmd-done-in-temp! session-id)
      (let [mote (store/load-mote *temp-dir* "1")]
        (is (= "Test claim" (:claim mote)))
        (is (= :p1 (:priority mote)))
        (is (= 4 (:difficulty mote)))
        (is (contains? (:taint mote) :needs-verification))
        ;; But claim should be cleared
        (is (nil? (:claimed-by mote)))))))

(deftest done-with-zero-actions-test
  (testing "done works with zero actions"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [sess (create-session! "1" :proposer "agent-1")
          session-id (:session-id sess)
          result (cmd-done-in-temp! session-id)]
      (is (= 0 (:action-count result))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest done-handler-registered-test
  (testing "done handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "done")))))

(deftest done-handler-is-function-test
  (testing "done handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "done")]
      (is (fn? handler)))))
