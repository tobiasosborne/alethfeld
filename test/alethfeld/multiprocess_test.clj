(ns alethfeld.multiprocess-test
  "Multi-process safety tests for Alethfeld.

   Tests the race condition prevention mechanisms that enable safe
   multi-agent deployments:

   1. FileLock-based repository locking (cross-process mutex)
   2. Atomic reservation creation (CREATE_NEW semantics)
   3. Atomic claim flow with retry-on-conflict

   NOTE: These tests simulate multi-process behavior using concurrent
   threads within a single JVM. FileLock provides cross-thread safety
   within the same JVM, so this accurately tests the locking behavior.
   True multi-process tests would require spawning actual `af` CLI
   processes, which is environment-dependent and less reliable in CI."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.tx :as tx]
            [alethfeld.io :as io]
            [alethfeld.session :as session]
            [alethfeld.job :as job])
  (:import [java.util.concurrent CountDownLatch TimeUnit]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-multiprocess-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn- init-repo!
  "Initialize a test repository with git configured."
  []
  (let [repo-path *temp-dir*]
    (git/git-init! repo-path)
    (git/git-config! repo-path "user.name" "test")
    (git/git-config! repo-path "user.email" "test@test.com")
    (store/init-repo! repo-path :project-name "Multiprocess Test")
    (git/git-add-all! repo-path)
    (git/git-commit! repo-path "Initialize")))

(defn- create-workable-mote!
  "Create a mote that can be claimed."
  [id]
  (let [repo-path *temp-dir*
        m (-> (mote/make-root-mote id "Test claim" "test-agent"
                                   :difficulty 3
                                   :priority :p2)
              (assoc :taint #{:needs-verification}))]
    (store/save-mote! repo-path m)
    (git/git-add-all! repo-path)
    (git/git-commit! repo-path (str "Create mote " id))
    m))

;; =============================================================================
;; FileLock Tests
;; =============================================================================

(deftest filelock-prevents-concurrent-access-test
  (testing "FileLock serializes concurrent operations"
    (init-repo!)
    (create-workable-mote! "1")

    (let [execution-order (atom [])
          temp-dir *temp-dir*
          latch (CountDownLatch. 2)
          start-latch (CountDownLatch. 1)]

      ;; Start two threads that try to acquire the lock simultaneously
      (let [t1 (future
                 (.await start-latch)
                 (tx/with-validation temp-dir "Thread 1 operation"
                   (fn [_]
                     (swap! execution-order conj :t1-start)
                     (Thread/sleep 50) ; Hold lock briefly
                     (swap! execution-order conj :t1-end)
                     nil))
                 (.countDown latch))
            t2 (future
                 (.await start-latch)
                 (tx/with-validation temp-dir "Thread 2 operation"
                   (fn [_]
                     (swap! execution-order conj :t2-start)
                     (Thread/sleep 50)
                     (swap! execution-order conj :t2-end)
                     nil))
                 (.countDown latch))]

        ;; Release both threads simultaneously
        (.countDown start-latch)

        ;; Wait for both to complete
        (.await latch 5 TimeUnit/SECONDS)
        @t1
        @t2)

      ;; Verify execution was serialized (one fully completes before other starts)
      (let [order @execution-order]
        (is (= 4 (count order)) "All operations should complete")
        ;; Either t1 fully completes before t2, or t2 fully completes before t1
        (is (or (= order [:t1-start :t1-end :t2-start :t2-end])
                (= order [:t2-start :t2-end :t1-start :t1-end]))
            (str "Operations should be serialized, got: " order))))))

(deftest filelock-many-concurrent-threads-test
  (testing "FileLock handles many concurrent threads"
    (init-repo!)
    (create-workable-mote! "1")

    (let [thread-count 10
          counter (atom 0)
          temp-dir *temp-dir*
          latch (CountDownLatch. thread-count)
          start-latch (CountDownLatch. 1)]

      ;; Start many threads that increment a counter inside the lock
      (doseq [i (range thread-count)]
        (future
          (.await start-latch)
          (tx/with-validation temp-dir (str "Thread " i " increment")
            (fn [_]
              ;; Non-atomic read-modify-write that would race without lock
              (let [current @counter]
                (Thread/sleep 5) ; Small delay to expose races
                (reset! counter (inc current)))
              nil))
          (.countDown latch)))

      ;; Release all threads
      (.countDown start-latch)

      ;; Wait for completion
      (.await latch 10 TimeUnit/SECONDS)

      ;; Counter should be exactly thread-count (no lost increments)
      (is (= thread-count @counter)
          "All increments should be counted (no race conditions)"))))

;; =============================================================================
;; Atomic Reservation Tests
;; =============================================================================

(deftest atomic-reservation-prevents-duplicate-test
  (testing "Only one thread succeeds when reserving same mote"
    (init-repo!)
    (session/ensure-session-dirs! *temp-dir*)

    (let [results (atom [])
          temp-dir *temp-dir*
          latch (CountDownLatch. 5)
          start-latch (CountDownLatch. 1)]

      ;; 5 threads try to reserve the same mote simultaneously
      (doseq [i (range 5)]
        (future
          (.await start-latch)
          (let [result (session/create-reservation-atomic! temp-dir "1" :verifier)]
            (swap! results conj {:thread i :success (:success result)}))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 5 TimeUnit/SECONDS)

      ;; Exactly one should succeed
      (let [successes (filter :success @results)]
        (is (= 1 (count successes))
            (str "Exactly one reservation should succeed, got: " (count successes)))))))

(deftest atomic-reservation-different-motes-test
  (testing "Different motes can be reserved concurrently"
    (init-repo!)
    (session/ensure-session-dirs! *temp-dir*)

    (let [results (atom [])
          temp-dir *temp-dir*
          latch (CountDownLatch. 3)
          start-latch (CountDownLatch. 1)]

      ;; 3 threads reserve different motes
      (doseq [i (range 3)]
        (future
          (.await start-latch)
          (let [result (session/create-reservation-atomic! temp-dir (str i) :verifier)]
            (swap! results conj {:mote (str i) :success (:success result)}))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 5 TimeUnit/SECONDS)

      ;; All should succeed
      (is (= 3 (count (filter :success @results)))
          "All reservations for different motes should succeed"))))

(deftest atomic-reservation-expiration-test
  (testing "Expired reservation allows new reservation"
    (init-repo!)
    (session/ensure-session-dirs! *temp-dir*)

    ;; Create a reservation with very short TTL
    (let [result1 (session/create-reservation-atomic! *temp-dir* "1" :verifier
                                                       :duration-seconds 1)]
      (is (:success result1) "First reservation should succeed")

      ;; Wait for expiration
      (Thread/sleep 1100)

      ;; New reservation should succeed
      (let [result2 (session/create-reservation-atomic! *temp-dir* "1" :verifier)]
        (is (:success result2) "Reservation after expiration should succeed")))))

;; =============================================================================
;; Atomic Claim Flow Tests
;; =============================================================================

(deftest atomic-claim-prevents-duplicate-claims-test
  (testing "Only one agent can claim a mote"
    (init-repo!)
    (create-workable-mote! "1")

    (let [results (atom [])
          temp-dir *temp-dir*
          latch (CountDownLatch. 5)
          start-latch (CountDownLatch. 1)]

      ;; 5 threads try to claim the same mote using atomic-update!
      (doseq [i (range 5)]
        (future
          (.await start-latch)
          (try
            (tx/atomic-update! temp-dir
                               (str "Agent " i " claims mote 1")
                               "1"
                               (fn [m]
                                 (when (:claimed-by m)
                                   (throw (ex-info "Already claimed"
                                                   {:type :already-claimed
                                                    :claimed-by (:claimed-by m)})))
                                 (mote/set-claimed-by m (str "agent-" i)))
                               :validate false)
            (swap! results conj {:agent i :success true})
            (catch Exception e
              (swap! results conj {:agent i :success false
                                   :error (:type (ex-data e))})))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 5 TimeUnit/SECONDS)

      ;; Exactly one should succeed
      (let [successes (filter :success @results)
            failures (remove :success @results)]
        (is (= 1 (count successes))
            "Exactly one claim should succeed")
        (is (= 4 (count failures))
            "Four claims should fail")
        (is (every? #(= :already-claimed (:error %)) failures)
            "Failures should be :already-claimed")))))

(deftest atomic-claim-stress-test
  (testing "High contention claim stress test"
    (init-repo!)

    ;; Create 5 motes
    (doseq [i (range 5)]
      (create-workable-mote! (str i)))

    (let [claim-results (atom [])
          temp-dir *temp-dir*
          thread-count 20
          latch (CountDownLatch. thread-count)
          start-latch (CountDownLatch. 1)]

      ;; 20 threads each try to claim one of the 5 motes
      (doseq [i (range thread-count)]
        (future
          (.await start-latch)
          ;; Each thread picks a random mote
          (let [mote-id (str (mod i 5))]
            (try
              (tx/atomic-update! temp-dir
                                 (str "Agent " i " claims mote " mote-id)
                                 mote-id
                                 (fn [m]
                                   (when (:claimed-by m)
                                     (throw (ex-info "Already claimed"
                                                     {:type :already-claimed})))
                                   (mote/set-claimed-by m (str "agent-" i)))
                                 :validate false)
              (swap! claim-results conj {:agent i :mote mote-id :success true})
              (catch Exception _
                (swap! claim-results conj {:agent i :mote mote-id :success false}))))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 10 TimeUnit/SECONDS)

      ;; Exactly 5 claims should succeed (one per mote)
      (let [successes (filter :success @claim-results)]
        (is (= 5 (count successes))
            "Exactly 5 claims should succeed (one per mote)")
        ;; Each mote should have exactly one successful claim
        (is (= 5 (count (set (map :mote successes))))
            "Each mote should be claimed exactly once")))))

;; =============================================================================
;; Reservation + Claim Integration Tests
;; =============================================================================

(deftest reservation-excludes-from-job-selection-test
  (testing "Reserved motes are excluded from job selection"
    (init-repo!)
    (session/ensure-session-dirs! *temp-dir*)

    ;; Create 3 motes
    (doseq [i (range 3)]
      (create-workable-mote! (str i)))

    ;; Reserve mote "1"
    (let [result (session/create-reservation-atomic! *temp-dir* "1" :verifier)]
      (is (:success result)))

    ;; Get active reservations
    (let [reservations (session/list-active-reservations *temp-dir*)
          active-ids (set (map :mote-id reservations))]

      (is (= #{"1"} active-ids) "Mote 1 should be reserved")

      ;; Job selection should exclude reserved motes
      (let [motes (store/load-all-motes *temp-dir*)
            jobs (job/select-jobs motes
                                  :active-reservations active-ids
                                  :max 10)]
        (is (= 2 (count jobs)) "Should find 2 available jobs")
        (is (not (some #(= "1" (:mote-id %)) jobs))
            "Reserved mote should not be in job list")))))

(deftest full-concurrent-claim-flow-test
  (testing "Full concurrent claim flow with reservation + claim"
    (init-repo!)
    (session/ensure-session-dirs! *temp-dir*)

    ;; Create a single mote
    (create-workable-mote! "1")

    (let [results (atom [])
          temp-dir *temp-dir*
          latch (CountDownLatch. 3)
          start-latch (CountDownLatch. 1)]

      ;; 3 threads simulate the full claim flow:
      ;; 1. Try to reserve
      ;; 2. If reserved, try to claim
      (doseq [i (range 3)]
        (future
          (.await start-latch)
          (let [res-result (session/create-reservation-atomic! temp-dir "1" :verifier)]
            (if (:success res-result)
              ;; Got reservation, now claim
              (try
                (tx/atomic-update! temp-dir
                                   (str "Agent " i " claims mote 1")
                                   "1"
                                   (fn [m]
                                     (when (:claimed-by m)
                                       (throw (ex-info "Already claimed"
                                                       {:type :already-claimed})))
                                     (mote/set-claimed-by m (str "agent-" i)))
                                   :validate false)
                (swap! results conj {:agent i :phase :claim :success true})
                (catch Exception _
                  (swap! results conj {:agent i :phase :claim :success false})))
              ;; Failed to reserve
              (swap! results conj {:agent i :phase :reserve :success false})))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 5 TimeUnit/SECONDS)

      ;; Exactly one should succeed at claiming
      (let [claim-successes (filter #(and (= :claim (:phase %)) (:success %)) @results)]
        (is (= 1 (count claim-successes))
            "Exactly one agent should successfully claim")))))

;; =============================================================================
;; create-file-exclusive! Tests
;; =============================================================================

(deftest create-file-exclusive-atomicity-test
  (testing "create-file-exclusive! is atomic - only one succeeds"
    (let [test-file (str *temp-dir* "/exclusive-test.edn")
          results (atom [])
          latch (CountDownLatch. 10)
          start-latch (CountDownLatch. 1)]

      ;; 10 threads try to create the same file
      (doseq [i (range 10)]
        (future
          (.await start-latch)
          (let [success (io/create-file-exclusive! test-file {:creator i})]
            (swap! results conj {:thread i :success success}))
          (.countDown latch)))

      (.countDown start-latch)
      (.await latch 5 TimeUnit/SECONDS)

      ;; Exactly one should succeed
      (let [successes (filter :success @results)]
        (is (= 1 (count successes))
            "Exactly one file creation should succeed")))))

;; =============================================================================
;; Lock Contention Feedback Test
;; =============================================================================

(deftest lock-contention-does-not-deadlock-test
  (testing "Lock contention resolves without deadlock"
    (init-repo!)
    (create-workable-mote! "1")

    (let [completed (atom 0)
          temp-dir *temp-dir*
          thread-count 20
          latch (CountDownLatch. thread-count)
          start-latch (CountDownLatch. 1)]

      (doseq [_ (range thread-count)]
        (future
          (.await start-latch)
          (tx/with-validation temp-dir "Contention test"
            (fn [_]
              (swap! completed inc)
              nil))
          (.countDown latch)))

      (.countDown start-latch)

      ;; Should complete within reasonable time (no deadlock)
      (let [finished (.await latch 30 TimeUnit/SECONDS)]
        (is finished "All threads should complete (no deadlock)")
        (is (= thread-count @completed)
            "All operations should complete")))))
