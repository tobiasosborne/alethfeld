(ns alethfeld.cmd.stale-cleanup-test
  "Tests for stale session cleanup integration in cmd-ready."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.session :as session]
            [alethfeld.io :as io]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-stale-cleanup-test-"})
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
  "Initialize a test repository with session directories."
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
  [id claim & {:keys [difficulty priority taint status claimed-by]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}
                    status :fixed}}]
  (let [m (cond-> (mote/make-mote id claim "test-agent"
                                  :difficulty difficulty
                                  :priority priority
                                  :taint taint
                                  :status status)
            claimed-by (mote/set-claimed-by claimed-by))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

(defn- create-stale-session!
  "Create a stale session (expired) for testing."
  [mote-id session-id]
  (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 10000))
        stale-session {:session-id session-id
                      :mote-id mote-id
                      :role :proposer
                      :agent "stale-agent"
                      :started-at past
                      :expires-at past
                      :actions []}
        active-path (str *temp-dir* "/.alethfeld/sessions/active/" session-id ".edn")]
    (io/write-edn active-path stale-session)
    stale-session))

(defn- create-crashed-session!
  "Create a session with a dead PID for testing."
  [mote-id session-id]
  (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
        crashed-session {:session-id session-id
                        :mote-id mote-id
                        :role :verifier
                        :agent "crashed-agent"
                        :started-at (java.util.Date.)
                        :expires-at future-time
                        :actions []
                        :pid 999999999}  ; Non-existent PID
        active-path (str *temp-dir* "/.alethfeld/sessions/active/" session-id ".edn")]
    (io/write-edn active-path crashed-session)
    crashed-session))

;; =============================================================================
;; Cleanup Function Tests
;; =============================================================================

(deftest cleanup-stale-sessions-clears-mote-claim-test
  (testing "Stale session cleanup clears mote claim on expired session"
    (init-repo!)
    ;; Create a mote that is claimed
    (create-mote! "1" "Test claim" :claimed-by "stale-agent")
    ;; Create a stale session for this mote
    (let [session-id "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee"]
      (create-stale-session! "1" session-id)

      ;; Verify mote is claimed before cleanup
      (let [mote-before (store/load-mote *temp-dir* "1")]
        (is (= "stale-agent" (:claimed-by mote-before))))

      ;; Run cleanup
      (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
        (is (= 1 (count cleaned)))
        (is (= "1" (:mote-id (first cleaned))))

        ;; Verify mote claim is cleared
        (let [mote-after (store/load-mote *temp-dir* "1")]
          (is (nil? (:claimed-by mote-after))))

        ;; Verify session is archived
        (is (nil? (session/load-active-session *temp-dir* session-id)))))))

(deftest cleanup-stale-sessions-clears-mote-claim-on-crashed-test
  (testing "Stale session cleanup clears mote claim on crashed agent"
    (init-repo!)
    ;; Create a mote that is claimed
    (create-mote! "2" "Test claim" :claimed-by "crashed-agent")
    ;; Create a crashed session (dead PID)
    (let [session-id "11111111-2222-3333-4444-555555555555-11111111-2222-3333-4444-555555555555"]
      (create-crashed-session! "2" session-id)

      ;; Verify mote is claimed before cleanup
      (let [mote-before (store/load-mote *temp-dir* "2")]
        (is (= "crashed-agent" (:claimed-by mote-before))))

      ;; Run cleanup
      (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
        (is (= 1 (count cleaned)))
        (is (= :crashed (:reason (first cleaned))))

        ;; Verify mote claim is cleared
        (let [mote-after (store/load-mote *temp-dir* "2")]
          (is (nil? (:claimed-by mote-after))))))))

(deftest cleanup-stale-sessions-handles-multiple-test
  (testing "Cleanup handles multiple stale sessions"
    (init-repo!)
    ;; Create multiple claimed motes
    (create-mote! "1" "First claim" :claimed-by "agent-1")
    (create-mote! "2" "Second claim" :claimed-by "agent-2")

    ;; Create stale sessions
    (create-stale-session! "1" "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa-aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa")
    (create-crashed-session! "2" "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb-bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb")

    ;; Run cleanup
    (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
      (is (= 2 (count cleaned)))

      ;; Both motes should have claims cleared
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "1"))))
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "2")))))))

(deftest cleanup-stale-sessions-does-not-clear-unclaimed-motes-test
  (testing "Cleanup doesn't try to clear motes that aren't claimed"
    (init-repo!)
    ;; Create an unclaimed mote
    (create-mote! "1" "Unclaimed")

    ;; Create a stale session (orphaned session, mote not claimed)
    (create-stale-session! "1" "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee")

    ;; Run cleanup - should succeed without error
    (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
      (is (= 1 (count cleaned)))

      ;; Mote is still unclaimed (no error thrown)
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "1")))))))

(deftest cleanup-stale-sessions-returns-empty-when-no-stale-test
  (testing "Cleanup returns empty when no stale sessions"
    (init-repo!)
    (create-mote! "1" "Active mote")

    ;; Create a valid active session
    (session/create-session! *temp-dir* "1" :proposer "active-agent")

    ;; Run cleanup
    (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
      (is (empty? cleaned)))))

(deftest cleanup-stale-sessions-handles-missing-mote-test
  (testing "Cleanup handles session for non-existent mote gracefully"
    (init-repo!)

    ;; Create a stale session for a mote that doesn't exist (but has valid ID format)
    (create-stale-session! "99.99.99" "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee")

    ;; Run cleanup - should succeed without error
    (let [cleaned (@#'cmd/cleanup-stale-sessions-and-claims! *temp-dir*)]
      (is (= 1 (count cleaned)))
      ;; Session is still archived even though mote doesn't exist
      (is (nil? (session/load-active-session *temp-dir*
                  "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee"))))))
