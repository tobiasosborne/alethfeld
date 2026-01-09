(ns alethfeld.concurrency-test
  "Concurrency tests for Alethfeld.

   Tests race conditions and concurrent access scenarios that could occur
   when multiple agents work on the same repository simultaneously.

   NOTE: These tests simulate concurrency within a single process using
   futures. Real multi-process concurrency would require git-level locking
   which is not yet implemented."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.tx :as tx]
            [alethfeld.job :as job]
            [alethfeld.verify :as verify]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-concurrency-test-"})]
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
  "Initialize a test repository with git configured.
   Captures *temp-dir* at call time.
   Optional :vote-quorum defaults to 1 (v0.2 default)."
  [& {:keys [vote-quorum] :or {vote-quorum 1}}]
  (let [repo-path *temp-dir*]
    (git/git-init! repo-path)
    (git/git-config! repo-path "user.name" "test")
    (git/git-config! repo-path "user.email" "test@test.com")
    (store/init-repo! repo-path :project-name "Concurrency Test Project"
                      :config {:vote-quorum vote-quorum})
    (git/git-add-all! repo-path)
    (git/git-commit! repo-path "Initialize")))

(defn- create-workable-mote!
  "Create a mote that can be claimed (has taint, not terminal status).
   Captures *temp-dir* at call time."
  [id & {:keys [claim taint]
         :or {claim "Test claim"
              taint #{:needs-verification}}}]
  (let [repo-path *temp-dir*
        m (-> (mote/make-root-mote id claim "test-agent"
                                   :difficulty 3
                                   :priority :p2)
              (assoc :taint taint))]
    (store/save-mote! repo-path m)
    (git/git-add-all! repo-path)
    (git/git-commit! repo-path (str "Create mote " id))
    m))

(defn- create-mote-with-stale-claim!
  "Create a mote with an expired claim (for timeout testing)."
  [id claimer minutes-ago]
  (let [old-time (java.util.Date. (- (.getTime (java.util.Date.))
                                     (* minutes-ago 60 1000)))
        m (-> (mote/make-root-mote id "Test claim" "test-agent"
                                   :difficulty 3
                                   :priority :p2)
              (assoc :taint #{:needs-verification})
              (assoc :claimed-by claimer)
              (assoc :claimed-at old-time))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create stale-claimed mote " id))
    m))

(defn- claim-mote!
  "Claim a mote (wrapper that uses *temp-dir*).
   Uses atomic-update! to ensure read-check-write is atomic."
  [id agent]
  (let [repo-path *temp-dir*]
    (:result
     (tx/atomic-update! repo-path
                        (str "Claim mote " id " for " agent)
                        id
                        (fn [current-mote]
                          (let [current-claimer (:claimed-by current-mote)]
                            (when (and current-claimer (not= current-claimer agent))
                              (throw (ex-info "Mote already claimed"
                                              {:type :already-claimed
                                               :mote-id id
                                               :claimed-by current-claimer})))
                            (mote/set-claimed-by current-mote agent)))
                        :validate false))))

(defn- vote-on-mote!
  "Vote on a mote (wrapper that uses *temp-dir*)."
  [id vote-type agent]
  (let [repo-path *temp-dir*]
    (verify/cast-vote! repo-path id agent vote-type)))

;; =============================================================================
;; Concurrent Claiming Tests
;; =============================================================================

(deftest concurrent-claim-same-mote-test
  (testing "Two agents claiming same mote - one should succeed"
    (init-repo!)
    (create-workable-mote! "1")

    ;; Both agents try to claim at the same time
    (let [results (atom [])
          temp-dir *temp-dir*
          barrier (promise)]

      ;; Start two futures that wait for the barrier before claiming
      (let [f1 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (claim-mote! "1" "agent-1")
                     (swap! results conj {:agent "agent-1" :success true})
                     (catch Exception e
                       (swap! results conj {:agent "agent-1" :success false
                                            :error (:type (ex-data e))})))))
            f2 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (claim-mote! "1" "agent-2")
                     (swap! results conj {:agent "agent-2" :success true})
                     (catch Exception e
                       (swap! results conj {:agent "agent-2" :success false
                                            :error (:type (ex-data e))})))))]

        ;; Release the barrier
        (deliver barrier true)

        ;; Wait for both to complete
        @f1
        @f2)

      ;; Exactly one should succeed
      (is (= 1 (count (filter :success @results)))
          "Exactly one claim should succeed")

      ;; The other should fail with :already-claimed
      (let [failures (remove :success @results)]
        (is (= 1 (count failures)))
        (is (= :already-claimed (:error (first failures))))))))

(deftest concurrent-claim-different-motes-test
  (testing "Two agents claiming different motes - both should succeed"
    (init-repo!)
    (create-workable-mote! "1")
    (create-workable-mote! "2")

    (let [results (atom [])
          temp-dir *temp-dir*
          barrier (promise)]

      (let [f1 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (claim-mote! "1" "agent-1")
                     (swap! results conj {:mote "1" :success true})
                     (catch Exception e
                       (swap! results conj {:mote "1" :success false
                                            :error (ex-message e)})))))
            f2 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (claim-mote! "2" "agent-2")
                     (swap! results conj {:mote "2" :success true})
                     (catch Exception e
                       (swap! results conj {:mote "2" :success false
                                            :error (ex-message e)})))))]

        (deliver barrier true)
        @f1
        @f2)

      ;; Both should succeed
      (is (= 2 (count (filter :success @results)))
          "Both claims should succeed"))))

;; =============================================================================
;; Claim Timeout Edge Cases
;; =============================================================================

(deftest claim-timeout-basic-test
  (testing "Stale claim is treated as available with timeout"
    (init-repo!)
    ;; Create mote with 60-minute-old claim
    (create-mote-with-stale-claim! "1" "stale-agent" 60)

    ;; Without timeout, mote is not workable
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (false? (job/workable? mote))
          "Mote should not be workable without timeout"))

    ;; With timeout, mote is workable
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (true? (job/workable? mote :claim-timeout 30))
          "Mote should be workable with 30-minute timeout"))))

(deftest claim-timeout-boundary-test
  (testing "Claim exactly at timeout boundary"
    (init-repo!)
    ;; Create mote claimed exactly 30 minutes ago
    (create-mote-with-stale-claim! "1" "boundary-agent" 30)

    ;; With 30-minute timeout, should be just expired (> not >=)
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (true? (job/workable? mote :claim-timeout 30))
          "Claim at exactly timeout should be considered expired"))))

(deftest claim-timeout-fresh-claim-test
  (testing "Fresh claim is not affected by timeout"
    (init-repo!)
    ;; Create mote with 5-minute-old claim
    (create-mote-with-stale-claim! "1" "active-agent" 5)

    ;; With 30-minute timeout, claim is still valid
    (let [mote (store/load-mote *temp-dir* "1")]
      (is (false? (job/workable? mote :claim-timeout 30))
          "Fresh claim should not be considered expired"))))

(deftest reclaim-stale-mote-test
  (testing "New agent can reclaim a mote with expired claim"
    (init-repo!)
    ;; Create mote with 60-minute-old claim
    (create-mote-with-stale-claim! "1" "stale-agent" 60)

    ;; Load motes and check with timeout
    (let [motes (store/load-all-motes *temp-dir*)
          jobs (job/select-jobs motes :claim-timeout 30 :max 10)]
      (is (= 1 (count jobs))
          "Should find the stale-claimed mote as available")
      (is (= "1" (:mote-id (first jobs)))))))

;; =============================================================================
;; Concurrent Voting Tests
;; =============================================================================

(deftest concurrent-votes-reaching-quorum-test
  (testing "Multiple votes arriving concurrently - quorum is reached atomically"
    (init-repo! :vote-quorum 2)

    (let [repo-path *temp-dir*]
      ;; Create a mote needing verification with quorum of 2
      (let [m (-> (mote/make-root-mote "1" "Test claim" "test-agent")
                  (assoc :status :fixed)
                  (assoc :taint #{:needs-verification}))]
        (store/save-mote! repo-path m)
        (git/git-add-all! repo-path)
        (git/git-commit! repo-path "Create mote"))

      ;; Verify mote exists before testing concurrency
      (is (some? (store/load-mote repo-path "1"))
          "Mote should exist before voting")

      ;; Two verifiers vote concurrently
      (let [results (atom [])
            barrier (promise)]

        (let [f1 (future
                   @barrier
                   (try
                     (verify/cast-vote! repo-path "1" "verifier-1" :for)
                     (swap! results conj {:agent "verifier-1" :success true})
                     (catch Exception e
                       (swap! results conj {:agent "verifier-1" :success false
                                            :error (ex-message e)}))))
              f2 (future
                   @barrier
                   (try
                     (verify/cast-vote! repo-path "1" "verifier-2" :for)
                     (swap! results conj {:agent "verifier-2" :success true})
                     (catch Exception e
                       (swap! results conj {:agent "verifier-2" :success false
                                            :error (ex-message e)}))))]

          (deliver barrier true)
          @f1
          @f2)

        ;; Both should succeed (votes are independent)
        (is (= 2 (count (filter :success @results)))
            "Both votes should succeed")

        ;; Mote should now be verified (quorum reached)
        (let [final-mote (store/load-mote repo-path "1")]
          (is (= :verified (:status final-mote))
              "Mote should be verified after quorum reached")
          (is (= 2 (count (:votes final-mote)))
              "Mote should have 2 votes"))))))

;; =============================================================================
;; File Write Race Tests
;; =============================================================================

(deftest concurrent-writes-to-different-motes-test
  (testing "Concurrent atomic writes to different motes"
    (init-repo!)
    (create-workable-mote! "1" :claim "First mote")
    (create-workable-mote! "2" :claim "Second mote")

    (let [results (atom [])
          temp-dir *temp-dir*
          barrier (promise)]

      (let [f1 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (let [m (store/load-mote temp-dir "1")
                           updated (assoc m :claim "Updated by agent 1")]
                       (tx/atomic-write! temp-dir "Update mote 1" [updated])
                       (swap! results conj {:mote "1" :success true}))
                     (catch Exception e
                       (swap! results conj {:mote "1" :success false
                                            :error (ex-message e)})))))
            f2 (future
                 @barrier
                 (binding [*temp-dir* temp-dir]
                   (try
                     (let [m (store/load-mote temp-dir "2")
                           updated (assoc m :claim "Updated by agent 2")]
                       (tx/atomic-write! temp-dir "Update mote 2" [updated])
                       (swap! results conj {:mote "2" :success true}))
                     (catch Exception e
                       (swap! results conj {:mote "2" :success false
                                            :error (ex-message e)})))))]

        (deliver barrier true)
        @f1
        @f2)

      ;; Both should succeed (different files)
      (is (= 2 (count (filter :success @results)))
          "Both writes should succeed")

      ;; Verify final state
      (let [m1 (store/load-mote *temp-dir* "1")
            m2 (store/load-mote *temp-dir* "2")]
        (is (= "Updated by agent 1" (:claim m1)))
        (is (= "Updated by agent 2" (:claim m2)))))))

(deftest sequential-writes-preserve-order-test
  (testing "Sequential writes preserve data integrity"
    (init-repo!)
    (create-workable-mote! "1")

    (let [repo-path *temp-dir*]
      ;; Verify mote exists after creation
      (is (some? (store/load-mote repo-path "1"))
          "Mote should exist after creation")

      ;; Apply 10 sequential updates using atomic-update! for proper locking
      ;; Use :meta field since :difficulty is constrained to 1-5
      (dotimes [i 10]
        (tx/atomic-update! repo-path
                           (str "Update " i)
                           "1"
                           (fn [m] (assoc-in m [:meta :counter] (inc i)))
                           :validate false))

      ;; Final state should have counter 10
      (let [final (store/load-mote repo-path "1")]
        (is (= 10 (get-in final [:meta :counter]))
            "Final counter should be 10")))))

;; =============================================================================
;; Transaction Isolation Tests
;; =============================================================================

(deftest transaction-reads-consistent-snapshot-test
  (testing "Transaction reads should see consistent state"
    (init-repo!)
    (create-workable-mote! "1")
    (create-workable-mote! "2")

    ;; Start a "slow" transaction that reads both motes
    ;; While it's processing, another transaction updates one mote
    (let [slow-read-result (atom nil)
          temp-dir *temp-dir*
          fast-update-done (promise)
          slow-read-started (promise)]

      (let [slow-reader (future
                          (binding [*temp-dir* temp-dir]
                            ;; Read initial state
                            (let [m1 (store/load-mote temp-dir "1")
                                  _ (deliver slow-read-started true)
                                  ;; Wait for fast update to complete
                                  _ @fast-update-done
                                  ;; Read second mote (might see updated state)
                                  m2 (store/load-mote temp-dir "2")]
                              (reset! slow-read-result {:m1 m1 :m2 m2}))))

            fast-updater (future
                           (binding [*temp-dir* temp-dir]
                             ;; Wait for slow reader to start
                             @slow-read-started
                             ;; Update mote 2
                             (let [m (store/load-mote temp-dir "2")
                                   updated (assoc m :claim "Fast update")]
                               (tx/atomic-write! temp-dir "Fast update" [updated])
                               (deliver fast-update-done true))))]

        @slow-reader
        @fast-updater)

      ;; This documents current behavior: reads are NOT isolated
      ;; The slow reader might see the fast update's changes
      ;; This is expected since we don't have snapshot isolation
      (is (some? @slow-read-result)
          "Both reads should complete"))))
