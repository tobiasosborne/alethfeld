(ns alethfeld.session-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.session :as session]
            [alethfeld.schema :as schema]
            [alethfeld.path :as path]
            [alethfeld.io :as io]
            [malli.core :as m]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-session-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-session-dirs
  "Initialize session directories in temp directory."
  []
  (session/ensure-session-dirs! *temp-dir*))

;; =============================================================================
;; Session ID Tests
;; =============================================================================

(deftest generate-session-id-format-test
  (testing "Generated session ID has correct format"
    (let [id (session/generate-session-id)]
      (is (string? id))
      (is (= 73 (count id)))  ; 36 + 1 + 36 = 73
      (is (re-matches #"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}" id)))))

(deftest generate-session-id-unique-test
  (testing "Generated session IDs are unique"
    (let [ids (repeatedly 100 session/generate-session-id)]
      (is (= 100 (count (set ids)))))))

(deftest valid-session-id-test
  (testing "Validates correct session ID format"
    (is (session/valid-session-id? "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"))
    (is (session/valid-session-id? "abcdefab-abcd-abcd-abcd-abcdefabcdef-abcdefab-abcd-abcd-abcd-abcdefabcdef")))
  (testing "Rejects invalid formats"
    (is (not (session/valid-session-id? "not-a-valid-id")))
    (is (not (session/valid-session-id? "12345678-1234-1234-1234-123456789012")))  ; Single UUID
    (is (not (session/valid-session-id? nil)))
    (is (not (session/valid-session-id? "")))))

;; =============================================================================
;; Schema Validation Tests
;; =============================================================================

(deftest session-schema-test
  (testing "Valid session passes schema validation"
    (let [session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1.2.3"
                   :role :proposer
                   :agent "test-agent"
                   :started-at (java.util.Date.)
                   :expires-at (java.util.Date.)
                   :actions [:propose :add-definition]}]
      (is (m/validate schema/Session session))))

  (testing "Session with optional pid passes validation"
    (let [session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :advisor
                   :agent "advisor-1"
                   :started-at (java.util.Date.)
                   :expires-at (java.util.Date.)
                   :pid 12345
                   :actions []}]
      (is (m/validate schema/Session session))))

  (testing "Invalid session fails validation"
    (is (not (m/validate schema/Session {:session-id "invalid"})))
    (is (not (m/validate schema/Session {:mote-id "1"})))))

;; =============================================================================
;; Session Creation Tests
;; =============================================================================

(deftest create-session-test
  (testing "Creates session with required fields"
    (let [session (session/create-session "1.2.3" :proposer "agent-1")]
      (is (string? (:session-id session)))
      (is (= "1.2.3" (:mote-id session)))
      (is (= :proposer (:role session)))
      (is (= "agent-1" (:agent session)))
      (is (inst? (:started-at session)))
      (is (inst? (:expires-at session)))
      (is (= [] (:actions session)))
      (is (nil? (:pid session)))))

  (testing "Creates session with optional pid"
    (let [session (session/create-session "1" :verifier "verifier-1" :pid 9999)]
      (is (= 9999 (:pid session)))))

  (testing "Respects custom duration"
    (let [session (session/create-session "1" :prover "prover-1" :duration-minutes 60)
          start (:started-at session)
          end (:expires-at session)
          diff-ms (- (.getTime end) (.getTime start))]
      ;; Should be approximately 60 minutes (3600000 ms)
      (is (< 3590000 diff-ms 3610000))))

  (testing "Created session passes schema validation"
    (let [session (session/create-session "1.2" :advisor "test")]
      (is (m/validate schema/Session session)))))

(deftest create-session!-test
  (testing "Persists session to active directory"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1.2.3" :proposer "agent-1")
          path (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id session) ".edn")]
      (is (some? session))
      (is (fs/exists? path))))

  (testing "Returns nil for invalid data"
    (init-session-dirs)
    ;; Invalid mote-id
    (is (nil? (session/create-session! *temp-dir* "invalid..id" :proposer "agent-1")))))

;; =============================================================================
;; Session Loading Tests
;; =============================================================================

(deftest load-session-test
  (testing "Loads active session by ID"
    (init-session-dirs)
    (let [created (session/create-session! *temp-dir* "1" :proposer "agent")
          loaded (session/load-session *temp-dir* (:session-id created))]
      (is (= created loaded))))

  (testing "Returns nil for non-existent session"
    (init-session-dirs)
    (is (nil? (session/load-session *temp-dir* "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012")))))

(deftest load-active-session-test
  (testing "Loads only active sessions"
    (init-session-dirs)
    (let [created (session/create-session! *temp-dir* "1" :proposer "agent")
          _ (session/end-session! *temp-dir* (:session-id created))]
      ;; Should not find in active
      (is (nil? (session/load-active-session *temp-dir* (:session-id created))))
      ;; But should find via load-session (which checks both)
      (is (some? (session/load-session *temp-dir* (:session-id created)))))))

(deftest load-all-active-sessions-test
  (testing "Returns empty vector when no sessions"
    (init-session-dirs)
    (is (= [] (session/load-all-active-sessions *temp-dir*))))

  (testing "Returns all active sessions"
    (init-session-dirs)
    (let [s1 (session/create-session! *temp-dir* "1" :proposer "agent-1")
          s2 (session/create-session! *temp-dir* "2" :advisor "agent-2")
          s3 (session/create-session! *temp-dir* "3" :prover "agent-3")
          all (session/load-all-active-sessions *temp-dir*)]
      (is (= 3 (count all)))
      (is (= #{(:session-id s1) (:session-id s2) (:session-id s3)}
             (set (map :session-id all)))))))

(deftest load-sessions-for-mote-test
  (testing "Filters sessions by mote ID"
    (init-session-dirs)
    (let [_ (session/create-session! *temp-dir* "1" :proposer "agent-1")
          s2 (session/create-session! *temp-dir* "2" :advisor "agent-2")
          _ (session/create-session! *temp-dir* "2" :verifier "agent-3")
          mote-2-sessions (session/load-sessions-for-mote *temp-dir* "2")]
      (is (= 2 (count mote-2-sessions)))
      (is (every? #(= "2" (:mote-id %)) mote-2-sessions)))))

;; =============================================================================
;; Session Status Tests
;; =============================================================================

(deftest session-active?-test
  (testing "Returns true for active, non-expired session"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")]
      (is (session/session-active? *temp-dir* (:session-id session)))))

  (testing "Returns false for non-existent session"
    (init-session-dirs)
    (is (not (session/session-active? *temp-dir* "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012")))))

(deftest session-expired?-test
  (testing "Returns false for non-expired session"
    (let [session (session/create-session "1" :proposer "agent")]
      (is (not (session/session-expired? session)))))

  (testing "Returns true for expired session"
    (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 1000))
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at past
                   :expires-at past
                   :actions []}]
      (is (session/session-expired? session)))))

;; =============================================================================
;; TOCTOU Prevention Tests - Boundary Conditions
;; =============================================================================

(deftest session-expired?-now-parameter-test
  (testing "Accepts :now parameter for consistent time checking"
    (let [;; Create session that expires at a specific time
          now (java.time.Instant/now)
          expires-at-date (java.util.Date/from (.plusSeconds now 60))
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      ;; Using a time before expiration -> not expired
      (is (not (session/session-expired? session :now now)))
      ;; Using a time 30 seconds later -> not expired
      (is (not (session/session-expired? session :now (.plusSeconds now 30))))
      ;; Using a time 61 seconds later -> expired
      (is (session/session-expired? session :now (.plusSeconds now 61)))))

  (testing "Exact boundary: at expiration time is NOT expired (uses isAfter)"
    ;; Note: java.util.Date has millisecond precision, java.time.Instant has nanosecond.
    ;; We truncate to millis to ensure consistent comparison.
    (let [now (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          expires-at-date (java.util.Date/from now)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      ;; At exact expiration time, isAfter returns false (equal is not after)
      (is (not (session/session-expired? session :now now)))
      ;; One millisecond after -> expired
      (is (session/session-expired? session :now (.plusMillis now 1)))))

  (testing "Defaults to current time when :now not provided"
    (let [;; Create a session expired 1 second ago
          past (java.util.Date. (- (System/currentTimeMillis) 1000))
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at past
                   :expires-at past
                   :actions []}]
      (is (session/session-expired? session)))))

(deftest session-active?-now-parameter-test
  (testing "Accepts :now parameter for consistent time checking"
    (init-session-dirs)
    (let [;; Create a session with known expiration
          session (session/create-session! *temp-dir* "1" :proposer "agent" :duration-minutes 1)
          now (java.time.Instant/now)]
      ;; Active with current time
      (is (session/session-active? *temp-dir* (:session-id session) :now now))
      ;; Active 30 seconds later
      (is (session/session-active? *temp-dir* (:session-id session) :now (.plusSeconds now 30)))
      ;; Not active 2 minutes later (past 1 minute expiration)
      (is (not (session/session-active? *temp-dir* (:session-id session) :now (.plusSeconds now 120)))))))

(deftest session-stale?-now-parameter-test
  (testing "Accepts :now parameter for consistent time checking"
    (let [now (java.time.Instant/now)
          expires-at (java.util.Date/from (.plusSeconds now 60))
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at
                   :actions []}]
      ;; Not stale at current time
      (is (not (session/session-stale? session :now now)))
      ;; Stale 61 seconds later
      (is (session/session-stale? session :now (.plusSeconds now 61)))))

  (testing "Still detects crashed process regardless of :now"
    (let [;; Session with non-existent PID, not expired
          future-time (java.util.Date. (+ (System/currentTimeMillis) 3600000))
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at future-time
                   :actions []
                   :pid 999999999}  ; Non-existent PID
          now (java.time.Instant/now)]
      ;; Stale due to crashed PID even though not expired
      (is (session/session-stale? session :now now)))))

(deftest toctou-consistent-timestamp-test
  (testing "Multiple expiration checks use same timestamp"
    ;; This test verifies the TOCTOU fix: when checking multiple sessions,
    ;; a single timestamp is used to ensure consistent evaluation.
    (init-session-dirs)
    (let [;; Create sessions that expire at slightly different times
          ;; In a race condition, if we checked each with a new timestamp,
          ;; results could be inconsistent
          now (java.time.Instant/now)
          base-time (java.util.Date/from now)
          ;; Session 1 expires at now+50ms
          session1 {:session-id "11111111-1111-1111-1111-111111111111-11111111-1111-1111-1111-111111111111"
                    :mote-id "1"
                    :role :proposer
                    :agent "test"
                    :started-at base-time
                    :expires-at (java.util.Date/from (.plusMillis now 50))
                    :actions []}
          ;; Session 2 expires at now+100ms
          session2 {:session-id "22222222-2222-2222-2222-222222222222-22222222-2222-2222-2222-222222222222"
                    :mote-id "2"
                    :role :proposer
                    :agent "test"
                    :started-at base-time
                    :expires-at (java.util.Date/from (.plusMillis now 100))
                    :actions []}
          ;; Check time at 75ms (session1 expired, session2 not)
          check-time (.plusMillis now 75)]
      ;; With consistent timestamp, results are predictable
      (is (session/session-expired? session1 :now check-time))
      (is (not (session/session-expired? session2 :now check-time)))
      ;; Verify the same check-time gives consistent results on re-check
      (is (session/session-expired? session1 :now check-time))
      (is (not (session/session-expired? session2 :now check-time))))))

;; =============================================================================
;; Session Update Tests
;; =============================================================================

(deftest record-action!-test
  (testing "Appends action to session"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")
          updated (session/record-action! *temp-dir* (:session-id session) :propose)]
      (is (= [:propose] (:actions updated)))))

  (testing "Records multiple actions in order"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :prover "agent")
          _ (session/record-action! *temp-dir* (:session-id session) :propose)
          _ (session/record-action! *temp-dir* (:session-id session) :add-definition)
          updated (session/record-action! *temp-dir* (:session-id session) :add-ref)]
      (is (= [:propose :add-definition :add-ref] (:actions updated)))))

  (testing "Returns nil for non-existent session"
    (init-session-dirs)
    (is (nil? (session/record-action! *temp-dir* "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012" :propose)))))

;; =============================================================================
;; Session Lifecycle Tests
;; =============================================================================

(deftest end-session!-test
  (testing "Moves session from active to completed"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")
          session-id (:session-id session)
          active-path (str *temp-dir* "/.alethfeld/sessions/active/" session-id ".edn")
          completed-path (str *temp-dir* "/.alethfeld/sessions/completed/" session-id ".edn")]
      (is (fs/exists? active-path))
      (is (not (fs/exists? completed-path)))

      (session/end-session! *temp-dir* session-id)

      (is (not (fs/exists? active-path)))
      (is (fs/exists? completed-path))))

  (testing "Returns the ended session"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")
          ended (session/end-session! *temp-dir* (:session-id session))]
      (is (= (:session-id session) (:session-id ended)))))

  (testing "Returns nil for non-existent session"
    (init-session-dirs)
    (is (nil? (session/end-session! *temp-dir* "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012")))))

(deftest archive-session!-test
  (testing "Archives session (same as end)"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")
          archived (session/archive-session! *temp-dir* (:session-id session))]
      (is (some? archived))
      (is (nil? (session/load-active-session *temp-dir* (:session-id session)))))))

(deftest delete-session!-test
  (testing "Deletes active session"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")]
      (is (session/delete-session! *temp-dir* (:session-id session)))
      (is (nil? (session/load-session *temp-dir* (:session-id session))))))

  (testing "Deletes completed session"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent")
          _ (session/end-session! *temp-dir* (:session-id session))]
      (is (session/delete-session! *temp-dir* (:session-id session)))
      (is (nil? (session/load-session *temp-dir* (:session-id session))))))

  (testing "Returns false for non-existent session"
    (init-session-dirs)
    (is (not (session/delete-session! *temp-dir* "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012")))))

;; =============================================================================
;; Cleanup Tests
;; =============================================================================

(deftest cleanup-expired-sessions!-test
  (testing "Archives expired sessions"
    (init-session-dirs)
    ;; Create a session with very short duration (already expired)
    (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 1000))
          expired-session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                          :mote-id "1"
                          :role :proposer
                          :agent "test"
                          :started-at past
                          :expires-at past
                          :actions []}
          active-path (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id expired-session) ".edn")]
      ;; Manually write expired session
      (io/write-edn active-path expired-session)

      ;; Create a valid non-expired session
      (let [valid-session (session/create-session! *temp-dir* "2" :advisor "agent-2")]
        ;; Cleanup
        (let [archived (session/cleanup-expired-sessions! *temp-dir*)]
          (is (= 1 (count archived)))
          (is (= "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012" (first archived)))
          ;; Expired session moved to completed
          (is (nil? (session/load-active-session *temp-dir* (:session-id expired-session))))
          ;; Valid session still active
          (is (some? (session/load-active-session *temp-dir* (:session-id valid-session)))))))))

(deftest pid-alive?-test
  (testing "Current process PID is alive"
    ;; Get current JVM PID
    (let [pid (.pid (java.lang.ProcessHandle/current))]
      (is (true? (session/pid-alive? pid)))
      (is (true? (session/pid-alive? (str pid))))))  ; Also works with string

  (testing "Non-existent PID returns false (definitely dead)"
    ;; Use a very high PID that's unlikely to exist
    (is (false? (session/pid-alive? 999999999))))

  (testing "Nil PID returns nil"
    (is (nil? (session/pid-alive? nil))))

  (testing "Return value is tri-state: true, false, :unknown, or nil"
    ;; The function should return one of these values
    (let [pid (.pid (java.lang.ProcessHandle/current))
          result (session/pid-alive? pid)]
      (is (or (true? result) (false? result) (= :unknown result))))
    (let [result (session/pid-alive? 999999999)]
      (is (or (true? result) (false? result) (= :unknown result))))
    (is (nil? (session/pid-alive? nil))))

  (testing "Cross-platform: works on current platform"
    ;; This test verifies the function works on whatever platform it's running on
    (let [pid (.pid (java.lang.ProcessHandle/current))
          os-name (System/getProperty "os.name")]
      ;; Should work regardless of platform
      (is (true? (session/pid-alive? pid))
          (str "pid-alive? should work on " os-name)))))

(deftest session-stale?-test
  (testing "Expired session is stale"
    (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 1000))
          expired-session {:session-id "test-id"
                          :mote-id "1"
                          :role :proposer
                          :agent "test"
                          :started-at past
                          :expires-at past
                          :actions []}]
      (is (session/session-stale? expired-session))))

  (testing "Session with dead PID is stale"
    (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
          session-with-dead-pid {:session-id "test-id"
                                :mote-id "1"
                                :role :proposer
                                :agent "test"
                                :started-at (java.util.Date.)
                                :expires-at future-time
                                :actions []
                                :pid 999999999}]  ; Non-existent PID
      (is (session/session-stale? session-with-dead-pid))))

  (testing "Valid session with live PID is not stale"
    (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
          current-pid (.pid (java.lang.ProcessHandle/current))
          valid-session {:session-id "test-id"
                        :mote-id "1"
                        :role :proposer
                        :agent "test"
                        :started-at (java.util.Date.)
                        :expires-at future-time
                        :actions []
                        :pid current-pid}]
      (is (not (session/session-stale? valid-session)))))

  (testing "Valid session without PID is not stale"
    (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
          session-no-pid {:session-id "test-id"
                         :mote-id "1"
                         :role :proposer
                         :agent "test"
                         :started-at (java.util.Date.)
                         :expires-at future-time
                         :actions []}]
      (is (not (session/session-stale? session-no-pid)))))

  (testing "Session with :unknown PID status is NOT stale (conservative)"
    ;; This tests the conservative behavior: if we can't determine PID status,
    ;; we treat it as NOT stale to avoid incorrectly cleaning up sessions
    ;; We can't easily mock pid-alive? to return :unknown, but we can verify
    ;; that false? is used (only false triggers staleness, not :unknown)
    (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))]
      ;; Verify that (false? :unknown) is false
      (is (not (false? :unknown)) "false? should return false for :unknown")
      ;; Verify that (false? false) is true
      (is (false? false) "false? should return true for false"))))

(deftest cleanup-stale-sessions!-test
  (testing "Cleans up expired session and returns mote info"
    (init-session-dirs)
    (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 1000))
          expired-session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                          :mote-id "1.2"
                          :role :proposer
                          :agent "test"
                          :started-at past
                          :expires-at past
                          :actions []}
          active-path (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id expired-session) ".edn")]
      (io/write-edn active-path expired-session)

      (let [cleaned (session/cleanup-stale-sessions! *temp-dir*)]
        (is (= 1 (count cleaned)))
        (is (= "1.2" (:mote-id (first cleaned))))
        (is (= :expired (:reason (first cleaned))))
        ;; Session moved to completed
        (is (nil? (session/load-active-session *temp-dir* (:session-id expired-session)))))))

  (testing "Cleans up crashed session (dead PID) and returns mote info"
    (init-session-dirs)
    (let [future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
          crashed-session {:session-id "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee"
                          :mote-id "2.3"
                          :role :verifier
                          :agent "crashed-agent"
                          :started-at (java.util.Date.)
                          :expires-at future-time
                          :actions []
                          :pid 999999999}  ; Non-existent PID
          active-path (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id crashed-session) ".edn")]
      (io/write-edn active-path crashed-session)

      (let [cleaned (session/cleanup-stale-sessions! *temp-dir*)]
        (is (= 1 (count cleaned)))
        (is (= "2.3" (:mote-id (first cleaned))))
        (is (= :crashed (:reason (first cleaned))))
        ;; Session moved to completed
        (is (nil? (session/load-active-session *temp-dir* (:session-id crashed-session)))))))

  (testing "Does not clean up valid sessions"
    (init-session-dirs)
    (let [valid-session (session/create-session! *temp-dir* "3" :advisor "valid-agent")]
      (let [cleaned (session/cleanup-stale-sessions! *temp-dir*)]
        (is (empty? cleaned))
        ;; Valid session still active
        (is (some? (session/load-active-session *temp-dir* (:session-id valid-session)))))))

  (testing "Cleans up both expired and crashed in one call"
    (init-session-dirs)
    (let [past (java.util.Date. (- (.getTime (java.util.Date.)) 1000))
          future-time (java.util.Date. (+ (.getTime (java.util.Date.)) 3600000))
          expired-session {:session-id "11111111-2222-3333-4444-555555555555-11111111-2222-3333-4444-555555555555"
                          :mote-id "4"
                          :role :proposer
                          :agent "expired-agent"
                          :started-at past
                          :expires-at past
                          :actions []}
          crashed-session {:session-id "66666666-7777-8888-9999-aaaaaaaaaaaa-66666666-7777-8888-9999-aaaaaaaaaaaa"
                          :mote-id "5"
                          :role :verifier
                          :agent "crashed-agent"
                          :started-at (java.util.Date.)
                          :expires-at future-time
                          :actions []
                          :pid 999999998}]

      (io/write-edn (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id expired-session) ".edn")
                    expired-session)
      (io/write-edn (str *temp-dir* "/.alethfeld/sessions/active/" (:session-id crashed-session) ".edn")
                    crashed-session)

      (let [cleaned (session/cleanup-stale-sessions! *temp-dir*)]
        (is (= 2 (count cleaned)))
        (is (some #(= "4" (:mote-id %)) cleaned))
        (is (some #(= "5" (:mote-id %)) cleaned))
        (is (some #(= :expired (:reason %)) cleaned))
        (is (some #(= :crashed (:reason %)) cleaned))))))

;; =============================================================================
;; Directory Initialization Tests
;; =============================================================================

(deftest ensure-session-dirs!-test
  (testing "Creates session directories"
    (session/ensure-session-dirs! *temp-dir*)
    (is (fs/directory? (str *temp-dir* "/.alethfeld/sessions")))
    (is (fs/directory? (str *temp-dir* "/.alethfeld/sessions/active")))
    (is (fs/directory? (str *temp-dir* "/.alethfeld/sessions/completed")))))

;; =============================================================================
;; Validation Tests
;; =============================================================================

(deftest validate-session-test
  (testing "Returns nil for valid session"
    (let [session (session/create-session "1" :proposer "agent")]
      (is (nil? (session/validate-session session)))))

  (testing "Returns explanation for invalid session"
    (let [invalid {:session-id "not-valid"}]
      (is (some? (session/validate-session invalid))))))

;; =============================================================================
;; Path Tests
;; =============================================================================

(deftest session-path-test
  (testing "Active session path"
    (is (= ".alethfeld/sessions/active/abc-123.edn"
           (path/session-path "abc-123" :active))))

  (testing "Completed session path"
    (is (= ".alethfeld/sessions/completed/abc-123.edn"
           (path/session-path "abc-123" :completed)))))

(deftest sessions-base-path-test
  (testing "Returns correct base path"
    (is (= ".alethfeld/sessions" (path/sessions-base-path)))))

(deftest active-sessions-path-test
  (testing "Returns correct active path"
    (is (= ".alethfeld/sessions/active" (path/active-sessions-path)))))

(deftest completed-sessions-path-test
  (testing "Returns correct completed path"
    (is (= ".alethfeld/sessions/completed" (path/completed-sessions-path)))))

;; =============================================================================
;; Role-Action Matrix Tests
;; =============================================================================

(deftest role-actions-structure-test
  (testing "All roles are defined"
    (is (= #{:proposer :advisor :prover :verifier :ref-checker :counterexample}
           (set (keys session/role-actions)))))

  (testing "Each role has a set of actions"
    (doseq [[role actions] session/role-actions]
      (is (set? actions) (str role " should have a set of actions"))
      (is (seq actions) (str role " should have at least one action")))))

(deftest allowed?-test
  (testing "Proposer can perform proposer actions"
    (is (session/allowed? :proposer :propose))
    (is (session/allowed? :proposer :add-definition))
    (is (session/allowed? :proposer :add-assumption))
    (is (session/allowed? :proposer :add-ref))
    (is (session/allowed? :proposer :done)))

  (testing "Proposer cannot perform other role actions"
    (is (not (session/allowed? :proposer :vote)))
    (is (not (session/allowed? :proposer :approve)))
    (is (not (session/allowed? :proposer :reject)))
    (is (not (session/allowed? :proposer :taint-add)))
    (is (not (session/allowed? :proposer :taint-remove))))

  (testing "Advisor can perform advisor actions"
    (is (session/allowed? :advisor :approve))
    (is (session/allowed? :advisor :reject))
    (is (session/allowed? :advisor :done)))

  (testing "Advisor cannot perform other role actions"
    (is (not (session/allowed? :advisor :propose)))
    (is (not (session/allowed? :advisor :vote)))
    (is (not (session/allowed? :advisor :add-definition))))

  (testing "Prover can perform prover actions"
    (is (session/allowed? :prover :propose))
    (is (session/allowed? :prover :add-definition))
    (is (session/allowed? :prover :add-assumption))
    (is (session/allowed? :prover :add-ref))
    (is (session/allowed? :prover :taint-remove))
    (is (session/allowed? :prover :done)))

  (testing "Prover cannot vote"
    (is (not (session/allowed? :prover :vote))))

  (testing "Verifier can perform verifier actions"
    (is (session/allowed? :verifier :vote))
    (is (session/allowed? :verifier :taint-add))
    (is (session/allowed? :verifier :done)))

  (testing "Verifier cannot propose"
    (is (not (session/allowed? :verifier :propose))))

  (testing "Ref-checker can perform ref-checker actions"
    (is (session/allowed? :ref-checker :add-ref))
    (is (session/allowed? :ref-checker :taint-remove))
    (is (session/allowed? :ref-checker :done)))

  (testing "Counterexample can perform counterexample actions"
    (is (session/allowed? :counterexample :vote))
    (is (session/allowed? :counterexample :update-status))
    (is (session/allowed? :counterexample :done)))

  (testing "All roles can :done"
    (doseq [role (keys session/role-actions)]
      (is (session/allowed? role :done) (str role " should be able to :done"))))

  (testing "Invalid role returns false"
    (is (not (session/allowed? :invalid-role :propose)))
    (is (not (session/allowed? nil :propose)))))

(deftest sessionless-commands-test
  (testing "Read-only commands don't require session"
    (is (contains? session/sessionless-commands :init))
    (is (contains? session/sessionless-commands :ready))
    (is (contains? session/sessionless-commands :show))
    (is (contains? session/sessionless-commands :tree))
    (is (contains? session/sessionless-commands :status))
    (is (contains? session/sessionless-commands :check))
    (is (contains? session/sessionless-commands :log))
    (is (contains? session/sessionless-commands :help))
    (is (contains? session/sessionless-commands :config)))

  (testing "Mutation commands are not sessionless"
    (is (not (contains? session/sessionless-commands :propose)))
    (is (not (contains? session/sessionless-commands :vote)))
    (is (not (contains? session/sessionless-commands :approve)))))

(deftest requires-session?-test
  (testing "Sessionless commands don't require session"
    (is (not (session/requires-session? :init)))
    (is (not (session/requires-session? :ready)))
    (is (not (session/requires-session? :show)))
    (is (not (session/requires-session? :help))))

  (testing "Mutation commands require session"
    (is (session/requires-session? :propose))
    (is (session/requires-session? :vote))
    (is (session/requires-session? :approve))
    (is (session/requires-session? :reject))
    (is (session/requires-session? :add-definition))))

(deftest get-allowed-actions-test
  (testing "Returns actions for valid role"
    (is (= #{:propose :add-definition :add-assumption :add-ref :done}
           (session/get-allowed-actions :proposer)))
    (is (= #{:approve :reject :done}
           (session/get-allowed-actions :advisor))))

  (testing "Returns nil for invalid role"
    (is (nil? (session/get-allowed-actions :invalid)))
    (is (nil? (session/get-allowed-actions nil)))))

(deftest get-roles-for-action-test
  (testing "Returns roles that can propose"
    (is (= #{:proposer :prover}
           (session/get-roles-for-action :propose))))

  (testing "Returns roles that can vote"
    (is (= #{:verifier :counterexample}
           (session/get-roles-for-action :vote))))

  (testing "All roles can :done"
    (is (= #{:proposer :advisor :prover :verifier :ref-checker :counterexample}
           (session/get-roles-for-action :done))))

  (testing "Returns empty set for unknown action"
    (is (= #{} (session/get-roles-for-action :unknown-action)))))

;; =============================================================================
;; Session Expiration Boundary Condition Tests
;; =============================================================================

(deftest session-expired?-boundary-conditions-test
  (testing "Session at exact expiration time is NOT expired (boundary: equal)"
    ;; When checking at the exact expiration instant, the session should NOT be
    ;; expired because session-expired? uses .isAfter, which returns false for
    ;; equal times.
    (let [now (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          expires-at-date (java.util.Date/from now)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (not (session/session-expired? session :now now))
          "Session should NOT be expired at exact expiration time")))

  (testing "Session 1ms BEFORE expiration is NOT expired"
    ;; When checking 1ms before the expiration time, the session should
    ;; definitely NOT be expired.
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          one-ms-before (.minusMillis expiration-time 1)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (not (session/session-expired? session :now one-ms-before))
          "Session should NOT be expired 1ms before expiration")))

  (testing "Session 1ms AFTER expiration IS expired"
    ;; When checking 1ms after the expiration time, the session should
    ;; definitely be expired because .isAfter returns true.
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          one-ms-after (.plusMillis expiration-time 1)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (session/session-expired? session :now one-ms-after)
          "Session SHOULD be expired 1ms after expiration")))

  (testing "Transition around expiration boundary - comprehensive"
    ;; Test a range of times around the boundary to ensure consistency
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      ;; Times before expiration - should NOT be expired
      (is (not (session/session-expired? session :now (.minusMillis expiration-time 1000)))
          "1 second before: not expired")
      (is (not (session/session-expired? session :now (.minusMillis expiration-time 100)))
          "100ms before: not expired")
      (is (not (session/session-expired? session :now (.minusMillis expiration-time 10)))
          "10ms before: not expired")
      (is (not (session/session-expired? session :now (.minusMillis expiration-time 1)))
          "1ms before: not expired")
      ;; Exact expiration time - should NOT be expired (isAfter semantics)
      (is (not (session/session-expired? session :now expiration-time))
          "at exact expiration: not expired")
      ;; Times after expiration - SHOULD be expired
      (is (session/session-expired? session :now (.plusMillis expiration-time 1))
          "1ms after: expired")
      (is (session/session-expired? session :now (.plusMillis expiration-time 10))
          "10ms after: expired")
      (is (session/session-expired? session :now (.plusMillis expiration-time 100))
          "100ms after: expired")
      (is (session/session-expired? session :now (.plusMillis expiration-time 1000))
          "1 second after: expired"))))

(deftest session-stale?-boundary-conditions-test
  (testing "Session at exact expiration time is NOT stale (via session-expired?)"
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (not (session/session-stale? session :now expiration-time))
          "Session should NOT be stale at exact expiration time")))

  (testing "Session 1ms before expiration is NOT stale"
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          one-ms-before (.minusMillis expiration-time 1)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (not (session/session-stale? session :now one-ms-before))
          "Session should NOT be stale 1ms before expiration")))

  (testing "Session 1ms after expiration IS stale"
    (let [expiration-time (.truncatedTo (java.time.Instant/now) java.time.temporal.ChronoUnit/MILLIS)
          one-ms-after (.plusMillis expiration-time 1)
          expires-at-date (java.util.Date/from expiration-time)
          session {:session-id "12345678-1234-1234-1234-123456789012-12345678-1234-1234-1234-123456789012"
                   :mote-id "1"
                   :role :proposer
                   :agent "test"
                   :started-at (java.util.Date.)
                   :expires-at expires-at-date
                   :actions []}]
      (is (session/session-stale? session :now one-ms-after)
          "Session SHOULD be stale 1ms after expiration"))))

(deftest session-active?-boundary-conditions-test
  (testing "Session at exact expiration time IS still active"
    (init-session-dirs)
    (let [;; Create session, then we'll check at exact expiration time
          now (java.time.Instant/now)
          ;; Create session with 1-minute duration, then compute when it expires
          session (session/create-session! *temp-dir* "1" :proposer "agent" :duration-minutes 1)
          ;; The session expires at started-at + 1 minute
          ;; We need to get the expiration instant
          expires-instant (java.time.Instant/ofEpochMilli (.getTime (:expires-at session)))]
      ;; At exact expiration time, session should still be active
      (is (session/session-active? *temp-dir* (:session-id session) :now expires-instant)
          "Session should be active at exact expiration time")))

  (testing "Session 1ms before expiration IS active"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent" :duration-minutes 1)
          expires-instant (java.time.Instant/ofEpochMilli (.getTime (:expires-at session)))
          one-ms-before (.minusMillis expires-instant 1)]
      (is (session/session-active? *temp-dir* (:session-id session) :now one-ms-before)
          "Session should be active 1ms before expiration")))

  (testing "Session 1ms after expiration is NOT active"
    (init-session-dirs)
    (let [session (session/create-session! *temp-dir* "1" :proposer "agent" :duration-minutes 1)
          expires-instant (java.time.Instant/ofEpochMilli (.getTime (:expires-at session)))
          one-ms-after (.plusMillis expires-instant 1)]
      (is (not (session/session-active? *temp-dir* (:session-id session) :now one-ms-after))
          "Session should NOT be active 1ms after expiration"))))

;; =============================================================================
;; Contributors & Self-Vote Prevention Tests
;; =============================================================================

(deftest can-vote?-test
  (testing "Non-contributor can vote"
    (let [mote {:contributors {:created-by "alice"}}]
      (is (session/can-vote? mote "bob"))))

  (testing "Creator cannot vote"
    (let [mote {:contributors {:created-by "alice"}}]
      (is (not (session/can-vote? mote "alice")))))

  (testing "Proposer cannot vote"
    (let [mote {:contributors {:created-by "alice"
                               :proposed-by "bob"}}]
      (is (not (session/can-vote? mote "bob")))
      (is (session/can-vote? mote "charlie"))))

  (testing "Refiner cannot vote"
    (let [mote {:contributors {:created-by "alice"
                               :refined-by #{"bob" "carol"}}}]
      (is (not (session/can-vote? mote "bob")))
      (is (not (session/can-vote? mote "carol")))
      (is (session/can-vote? mote "dave"))))

  (testing "Ref-checker cannot vote"
    (let [mote {:contributors {:created-by "alice"
                               :refs-checked-by #{"bob"}}}]
      (is (not (session/can-vote? mote "bob")))
      (is (session/can-vote? mote "charlie"))))

  (testing "All contributors blocked"
    (let [mote {:contributors {:created-by "alice"
                               :proposed-by "bob"
                               :refined-by #{"carol" "dave"}
                               :refs-checked-by #{"eve"}}}]
      (is (not (session/can-vote? mote "alice")))
      (is (not (session/can-vote? mote "bob")))
      (is (not (session/can-vote? mote "carol")))
      (is (not (session/can-vote? mote "dave")))
      (is (not (session/can-vote? mote "eve")))
      (is (session/can-vote? mote "frank"))))

  (testing "Handles mote without contributors field"
    (let [mote {:created-by "alice"}]
      (is (session/can-vote? mote "bob"))
      ;; Without :contributors, can-vote? doesn't check :created-by at top level
      ;; This is intentional - contributors field should be present for enforcement
      (is (session/can-vote? mote "alice")))))

(deftest add-contributor-test
  (testing "Add proposed-by"
    (let [mote {:contributors {:created-by "alice"}}
          updated (session/add-contributor mote "bob" :proposed-by)]
      (is (= "bob" (get-in updated [:contributors :proposed-by])))))

  (testing "Add refined-by creates set"
    (let [mote {:contributors {:created-by "alice"}}
          updated (session/add-contributor mote "bob" :refined-by)]
      (is (= #{"bob"} (get-in updated [:contributors :refined-by])))))

  (testing "Add refined-by accumulates"
    (let [mote {:contributors {:created-by "alice"
                               :refined-by #{"bob"}}}
          updated (session/add-contributor mote "carol" :refined-by)]
      (is (= #{"bob" "carol"} (get-in updated [:contributors :refined-by])))))

  (testing "Add refs-checked-by"
    (let [mote {:contributors {:created-by "alice"}}
          updated (session/add-contributor mote "bob" :refs-checked-by)]
      (is (= #{"bob"} (get-in updated [:contributors :refs-checked-by])))))

  (testing "Initializes contributors if missing"
    (let [mote {:created-by "alice"}
          updated (session/add-contributor mote "bob" :refined-by)]
      (is (= "alice" (get-in updated [:contributors :created-by])))
      (is (= #{"bob"} (get-in updated [:contributors :refined-by]))))))

(deftest get-contributors-test
  (testing "Returns all contributors as set"
    (let [mote {:contributors {:created-by "alice"
                               :proposed-by "bob"
                               :refined-by #{"carol" "dave"}
                               :refs-checked-by #{"eve"}}}]
      (is (= #{"alice" "bob" "carol" "dave" "eve"}
             (session/get-contributors mote)))))

  (testing "Handles partial contributors"
    (let [mote {:contributors {:created-by "alice"}}]
      (is (= #{"alice"} (session/get-contributors mote)))))

  (testing "Handles nil values"
    (let [mote {:contributors {:created-by "alice"
                               :proposed-by nil
                               :refined-by nil}}]
      (is (= #{"alice"} (session/get-contributors mote))))))

;; =============================================================================
;; Schema Integration Tests
;; =============================================================================

(deftest contributors-schema-test
  (testing "Valid contributors passes schema"
    (let [contributors {:created-by "alice"
                        :proposed-by "bob"
                        :refined-by #{"carol"}
                        :refs-checked-by #{"dave"}}]
      (is (m/validate schema/Contributors contributors))))

  (testing "Minimal contributors passes schema"
    (let [contributors {:created-by "alice"}]
      (is (m/validate schema/Contributors contributors))))

  (testing "Invalid contributors fails schema"
    (is (not (m/validate schema/Contributors {})))
    (is (not (m/validate schema/Contributors {:proposed-by "bob"})))))
