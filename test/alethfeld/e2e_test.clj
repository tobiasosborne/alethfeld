(ns alethfeld.e2e-test
  "End-to-end integration tests for complete workflows.

   Tests exercise real workflows through the domain layer:
   - Complete verification workflow
   - Complete proposal workflow
   - Multi-agent collaboration
   - Session lifecycle
   - Error handling paths

   Note: These tests use domain functions directly (session, proposal, verify)
   rather than cmd-* functions, since cmd-* functions use hardcoded \".\" paths
   designed for CLI execution context."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.tx :as tx]
            [alethfeld.dag :as dag]
            [alethfeld.session :as session]
            [alethfeld.proposal :as proposal]
            [alethfeld.verify :as verify]
            [alethfeld.job :as job]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-e2e-test-"})
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

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn- init-repo!
  "Initialize a test repository with git configured.
   Optional :vote-quorum and :proposal-quorum default to 1."
  [& {:keys [vote-quorum proposal-quorum session-timeout-minutes]
      :or {vote-quorum 1 proposal-quorum 1 session-timeout-minutes 30}}]
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :project-name "E2E Test Project"
                    :config {:vote-quorum vote-quorum
                             :proposal-quorum proposal-quorum
                             :session-timeout-minutes session-timeout-minutes})
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-root-mote!
  "Create a root mote directly in the store.
   Note: Default taint is empty (#{}) to avoid motes showing up in job queries
   unless explicitly given taints via add-*-taint! helpers."
  [id claim & {:keys [difficulty priority taint]
               :or {difficulty 3 priority :p2
                    taint #{}}}]
  (let [m (mote/make-root-mote id claim "test-agent"
                               :difficulty difficulty
                               :priority priority
                               :taint taint)]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create root mote " id))
    m))

(defn- create-child-mote!
  "Create a child mote and update parent.
   Note: Default taint is empty (#{}) to avoid motes showing up in job queries
   unless explicitly given taints via add-*-taint! helpers."
  [id claim parent-id & {:keys [difficulty priority status taint]
                         :or {difficulty 3 priority :p2 status :fixed taint #{}}}]
  (let [parent (store/load-mote *temp-dir* parent-id)
        child (mote/make-child-mote id claim "test-agent" parent
                                    :difficulty difficulty
                                    :priority priority
                                    :taint taint)
        child (assoc child :status status)
        updated-parent (mote/add-child parent id)]
    (store/save-mote! *temp-dir* child)
    (store/save-mote! *temp-dir* updated-parent)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create child mote " id))
    child))

(defn- load-mote
  "Load a mote from the store."
  [id]
  (store/load-mote *temp-dir* id))

(defn- load-all-motes
  "Load all motes from the store."
  []
  (store/load-all-motes *temp-dir*))

(defn- add-verification-taint!
  "Add :needs-verification taint to a mote."
  [mote-id]
  (let [m (load-mote mote-id)
        updated (mote/add-taint m :needs-verification)]
    (store/save-mote! *temp-dir* updated)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Add verification taint to " mote-id))
    updated))

(defn- add-decomposition-taint!
  "Add :needs-decomposition taint to a mote."
  [mote-id]
  (let [m (load-mote mote-id)
        updated (mote/add-taint m :needs-decomposition)]
    (store/save-mote! *temp-dir* updated)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Add decomposition taint to " mote-id))
    updated))

(defn- claim-mote!
  "Claim a mote for an agent and create a session."
  [mote-id agent-name role]
  (session/ensure-session-dirs! *temp-dir*)
  (let [mote (load-mote mote-id)
        sess (session/create-session! *temp-dir* mote-id role agent-name)
        updated-mote (mote/set-claimed-by mote agent-name)]
    (tx/atomic-write! *temp-dir*
                      (str "Claim mote " mote-id " for " agent-name)
                      [updated-mote])
    sess))

(defn- end-session!
  "End a session and release the mote claim."
  [session-id]
  (let [sess (session/load-active-session *temp-dir* session-id)
        mote-id (:mote-id sess)
        mote (load-mote mote-id)
        updated-mote (mote/clear-claim mote)]
    (session/end-session! *temp-dir* session-id :record-stats true)
    (tx/atomic-write! *temp-dir*
                      (str "End session for " mote-id)
                      [updated-mote])))

;; =============================================================================
;; 1. Complete Verification Workflow Tests
;; =============================================================================

(deftest complete-verification-workflow-test
  (testing "Full verification workflow: init -> create -> session -> vote -> verify"
    (init-repo! :vote-quorum 2)

    (testing "Step 1: Create root mote"
      (let [root (create-root-mote! "1" "Prove that P implies Q")]
        (is (= "1" (:id root)))
        (is (= :fixed (:status root)))))

    (testing "Step 2: Create child mote that needs verification"
      (create-child-mote! "1.1" "Show P is true" "1")
      (add-verification-taint! "1.1")
      (is (contains? (:taint (load-mote "1.1")) :needs-verification)))

    (testing "Step 3: Start session as verifier"
      (let [sess (claim-mote! "1.1" "verifier-agent-1" :verifier)]
        (is (some? (:session-id sess)))
        (is (= "verifier-agent-1" (:claimed-by (load-mote "1.1"))))

        (testing "Step 4: Cast first verification vote"
          (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-agent-1" :for
                                          :reason "Verified by first verifier")]
            (is (= :pending (:quorum-status (:result result)))
                "First vote should leave status pending")))

        (testing "Step 5: End first verifier session"
          (end-session! (:session-id sess)))))

    (testing "Step 6: Second verifier claims and votes"
      (let [sess (claim-mote! "1.1" "verifier-agent-2" :verifier)]
        (is (some? (:session-id sess)))

        (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-agent-2" :for
                                        :reason "Confirmed by second verifier")]
          (is (= :verified (:quorum-status (:result result)))
              "Second vote should reach quorum and verify"))

        (end-session! (:session-id sess))))

    (testing "Step 7: Check final status shows verified"
      (let [final-mote (load-mote "1.1")]
        (is (= :verified (:status final-mote)))
        (is (= 2 (count (:votes final-mote))))))))

(deftest single-vote-quorum-verification-test
  (testing "Verification with quorum of 1"
    (init-repo! :vote-quorum 1)
    (create-root-mote! "1" "Simple theorem")
    (create-child-mote! "1.1" "Simple lemma" "1")
    (add-verification-taint! "1.1")

    (let [sess (claim-mote! "1.1" "solo-verifier" :verifier)]
      ;; Single vote should verify immediately
      (let [result (verify/cast-vote! *temp-dir* "1.1" "solo-verifier" :for
                                      :reason "Solo verification")]
        (is (= :verified (:quorum-status (:result result)))))

      (end-session! (:session-id sess))
      (is (= :verified (:status (load-mote "1.1")))))))

;; =============================================================================
;; 2. Complete Proposal Workflow Tests
;; =============================================================================

(deftest complete-proposal-workflow-test
  (testing "Full proposal workflow: init -> propose -> approve -> adopt"
    (init-repo! :proposal-quorum 2)

    (testing "Step 1: Create mote needing decomposition"
      (create-root-mote! "1" "Complex theorem to decompose")
      (add-decomposition-taint! "1")
      (is (contains? (:taint (load-mote "1")) :needs-decomposition)))

    (testing "Step 2: Start session as proposer"
      (let [sess (claim-mote! "1" "proposer-agent" :proposer)]
        (is (some? (:session-id sess)))

        (testing "Step 3: Create proposal with children"
          (let [result (proposal/create-proposal! *temp-dir* "1"
                                                  [{:claim "First substep"}
                                                   {:claim "Second substep"}]
                                                  "proposer-agent")]
            (is (some? (:result result)))
            (is (= 2 (count (:children (:result result)))))
            ;; Verify proposed children exist
            (is (= :proposed (:status (load-mote "1.1"))))
            (is (= :proposed (:status (load-mote "1.2"))))))

        ;; End proposer session
        (end-session! (:session-id sess))))

    (testing "Step 4: First advisor approves"
      (let [sess (claim-mote! "1" "advisor-1" :advisor)]
        (let [result (proposal/approve-proposal! *temp-dir* "1" "advisor-1"
                                                 :reason "Looks good")]
          (is (= :pending (:quorum-status (:result result)))
              "First approval should leave status pending"))
        (end-session! (:session-id sess))))

    (testing "Step 5: Second advisor approves - quorum reached"
      (let [sess (claim-mote! "1" "advisor-2" :advisor)]
        (let [result (proposal/approve-proposal! *temp-dir* "1" "advisor-2"
                                                 :reason "Approved")]
          (is (= :approved (:quorum-status (:result result))))
          (is (= #{"1.1" "1.2"} (set (:promoted-children (:result result))))))
        (end-session! (:session-id sess))))

    (testing "Step 6: Check proposal is adopted"
      (let [parent (load-mote "1")
            child-1 (load-mote "1.1")
            child-2 (load-mote "1.2")]
        ;; Parent should have children and no active proposal
        (is (= #{"1.1" "1.2"} (set (:children parent))))
        (is (nil? (:proposal parent)))
        ;; Children should be fixed status
        (is (= :fixed (:status child-1)))
        (is (= :fixed (:status child-2)))))))

(deftest proposal-rejection-workflow-test
  (testing "Proposal rejection workflow"
    (init-repo! :proposal-quorum 2)
    (create-root-mote! "1" "Theorem to decompose")
    (add-decomposition-taint! "1")

    ;; Proposer creates proposal
    (let [proposer-session (claim-mote! "1" "proposer" :proposer)]
      (proposal/create-proposal! *temp-dir* "1"
                                 [{:claim "Bad approach 1"}
                                  {:claim "Bad approach 2"}]
                                 "proposer")
      (end-session! (:session-id proposer-session)))

    ;; First advisor rejects
    (let [advisor1-session (claim-mote! "1" "advisor-1" :advisor)]
      (let [result (proposal/reject-proposal! *temp-dir* "1" "advisor-1"
                                              :reason "Needs rework")]
        (is (= :pending (:quorum-status (:result result)))))
      (end-session! (:session-id advisor1-session)))

    ;; Second advisor rejects - quorum reached
    (let [advisor2-session (claim-mote! "1" "advisor-2" :advisor)]
      (let [result (proposal/reject-proposal! *temp-dir* "1" "advisor-2"
                                              :reason "Agree, needs rework")]
        (is (= :rejected (:quorum-status (:result result)))))
      (end-session! (:session-id advisor2-session)))

    ;; Verify rejection effects
    (let [parent (load-mote "1")]
      (is (empty? (:children parent)))
      (is (nil? (:proposal parent)))
      ;; Parent should have needs-decomposition taint restored
      (is (contains? (:taint parent) :needs-decomposition)))))

;; =============================================================================
;; 3. Multi-Agent Collaboration Tests
;; =============================================================================

(deftest multi-agent-role-handoff-test
  (testing "Handoff between proposer -> advisor -> verifier"
    (init-repo! :proposal-quorum 1 :vote-quorum 1)
    (create-root-mote! "1" "Multi-agent theorem")
    (add-decomposition-taint! "1")

    (testing "Phase 1: Proposer creates decomposition"
      (let [sess (claim-mote! "1" "proposer-agent" :proposer)]
        (proposal/create-proposal! *temp-dir* "1"
                                   [{:claim "Lemma to verify"}]
                                   "proposer-agent")
        (end-session! (:session-id sess))
        (is (= :proposed (:status (load-mote "1.1"))))))

    (testing "Phase 2: Advisor approves proposal"
      (let [sess (claim-mote! "1" "advisor-agent" :advisor)]
        (let [result (proposal/approve-proposal! *temp-dir* "1" "advisor-agent"
                                                 :reason "Approved")]
          (is (= :approved (:quorum-status (:result result)))))
        (end-session! (:session-id sess))
        (is (= :fixed (:status (load-mote "1.1"))))))

    (testing "Phase 3: Verifier verifies the child"
      ;; Add verification taint
      (add-verification-taint! "1.1")

      (let [sess (claim-mote! "1.1" "verifier-agent" :verifier)]
        (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-agent" :for
                                        :reason "Verified")]
          (is (= :verified (:quorum-status (:result result)))))
        (end-session! (:session-id sess))
        (is (= :verified (:status (load-mote "1.1"))))))

    (testing "Final DAG is valid"
      (let [motes (load-all-motes)
            validation (dag/validate-mote-graph motes)]
        (is (:valid? validation))))))

(deftest multi-agent-parallel-work-test
  (testing "Multiple agents working on different motes simultaneously"
    (init-repo! :vote-quorum 1)
    (create-root-mote! "1" "Theorem A")
    (create-root-mote! "2" "Theorem B")
    (create-child-mote! "1.1" "Lemma A1" "1")
    (create-child-mote! "2.1" "Lemma B1" "2")
    (add-verification-taint! "1.1")
    (add-verification-taint! "2.1")

    ;; Agent A claims mote 1.1
    (let [agent-a-session (claim-mote! "1.1" "agent-a" :verifier)
          agent-a-sid (:session-id agent-a-session)]

      ;; Agent B claims mote 2.1 while A is still working
      (let [agent-b-session (claim-mote! "2.1" "agent-b" :verifier)
            agent-b-sid (:session-id agent-b-session)]

        ;; Both vote in parallel (simulated)
        (verify/cast-vote! *temp-dir* "1.1" "agent-a" :for :reason "A verified")
        (verify/cast-vote! *temp-dir* "2.1" "agent-b" :for :reason "B verified")

        ;; Both end sessions
        (end-session! agent-a-sid)
        (end-session! agent-b-sid)))

    ;; Both should be verified
    (is (= :verified (:status (load-mote "1.1"))))
    (is (= :verified (:status (load-mote "2.1"))))))

;; =============================================================================
;; 4. Session Lifecycle Tests
;; =============================================================================

(deftest session-create-action-end-test
  (testing "Complete session lifecycle: create -> action -> done"
    (init-repo! :vote-quorum 1)
    (create-root-mote! "1" "Session test theorem")
    (create-child-mote! "1.1" "Session test lemma" "1")
    (add-verification-taint! "1.1")

    (testing "Create session via claim"
      (let [sess (claim-mote! "1.1" "session-test-agent" :verifier)
            session-id (:session-id sess)]
        (is (some? session-id))

        ;; Session should be active
        (is (session/session-active? *temp-dir* session-id))

        (testing "Perform action within session"
          (let [result (verify/cast-vote! *temp-dir* "1.1" "session-test-agent" :for
                                          :reason "Test vote")]
            (is (= :verified (:quorum-status (:result result))))))

        (testing "End session with done"
          (end-session! session-id))

        (testing "Session is no longer active after done"
          ;; Session should be moved to completed
          (is (not (session/session-active? *temp-dir* session-id))))))))

(deftest session-mote-claim-released-after-done-test
  (testing "Mote claim is released when session ends"
    (init-repo!)
    (create-root-mote! "1" "Claim release test")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    ;; First agent claims
    (let [sess (claim-mote! "1.1" "first-agent" :verifier)
          session-id (:session-id sess)]

      ;; Mote should be claimed
      (is (= "first-agent" (:claimed-by (load-mote "1.1"))))

      ;; End session
      (end-session! session-id)

      ;; Mote claim should be cleared
      (is (nil? (:claimed-by (load-mote "1.1"))))

      ;; Second agent can now claim
      (let [second-sess (claim-mote! "1.1" "second-agent" :verifier)]
        (is (some? (:session-id second-sess)))
        (is (= "second-agent" (:claimed-by (load-mote "1.1"))))
        (end-session! (:session-id second-sess))))))

(deftest session-role-enforcement-test
  (testing "Session role enforces allowed actions"
    (init-repo!)
    (create-root-mote! "1" "Role test theorem")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    (let [sess (claim-mote! "1.1" "advisor-agent" :advisor)
          session-id (:session-id sess)]
      ;; Advisor role can approve/reject but NOT vote
      (is (session/allowed? :advisor :approve))
      (is (session/allowed? :advisor :reject))
      (is (not (session/allowed? :advisor :vote)))

      ;; Try to enforce vote action - should fail
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"[Nn]ot allowed|[Rr]ole"
           (session/enforce-session! *temp-dir* session-id :vote "1.1")))

      (end-session! session-id))))

;; =============================================================================
;; 5. Error Handling Tests
;; =============================================================================

(deftest expired-session-rejection-test
  (testing "Expired session is rejected"
    (init-repo!)
    (create-root-mote! "1" "Expiry test theorem")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    (session/ensure-session-dirs! *temp-dir*)

    ;; Create session with 0 duration (expires immediately)
    (let [sess (session/create-session! *temp-dir* "1.1" :verifier "test-agent"
                                        :duration-minutes 0)]
      ;; Wait briefly to ensure expiration
      (Thread/sleep 10)

      ;; Session should be expired
      (is (session/session-expired? sess))

      ;; Try to enforce action on expired session
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"[Ee]xpired"
           (session/enforce-session! *temp-dir* (:session-id sess) :vote "1.1"))))))

(deftest wrong-role-rejection-test
  (testing "Wrong role for action is rejected"
    (init-repo!)
    (create-root-mote! "1" "Role test theorem")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    (let [sess (claim-mote! "1.1" "advisor-agent" :advisor)
          session-id (:session-id sess)]

      ;; Try to enforce vote with advisor role - should fail
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"[Nn]ot allowed|[Rr]ole"
           (session/enforce-session! *temp-dir* session-id :vote "1.1")))

      (end-session! session-id))))

(deftest invalid-mote-reference-rejection-test
  (testing "Invalid mote reference is rejected when loading"
    (init-repo!)
    (create-root-mote! "1" "Reference test theorem")

    ;; Loading non-existent mote returns nil
    (is (nil? (load-mote "999")))))

(deftest duplicate-vote-rejection-test
  (testing "Same agent cannot vote twice on same mote"
    (init-repo! :vote-quorum 2)
    (create-root-mote! "1" "Double vote test")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    ;; First vote
    (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "First vote")

    ;; Second vote from same agent should fail
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"[Aa]lready voted"
         (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "Second vote")))))

(deftest duplicate-proposal-rejection-test
  (testing "Cannot create proposal when one already exists"
    (init-repo!)
    (create-root-mote! "1" "Double proposal test")
    (add-decomposition-taint! "1")

    ;; Create first proposal
    (proposal/create-proposal! *temp-dir* "1"
                               [{:claim "Child 1"}]
                               "proposer-1")

    ;; Try to create second proposal - should fail
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"[Aa]lready.*proposal"
         (proposal/create-proposal! *temp-dir* "1"
                                    [{:claim "Different child"}]
                                    "proposer-2")))))

;; =============================================================================
;; 6. Job Discovery Tests
;; =============================================================================

(deftest job-discovery-test
  (testing "Job selection finds available work"
    (init-repo! :vote-quorum 1)
    (create-root-mote! "1" "Job discovery test")
    (create-child-mote! "1.1" "Needs verification" "1")
    (add-verification-taint! "1.1")

    (testing "Select jobs finds mote needing verification"
      (let [motes (load-all-motes)
            ;; Filter for verifier role to get the child mote with :needs-verification
            jobs (job/select-jobs motes :role :verifier :max 10)]
        (is (seq jobs))
        (is (= "1.1" (:mote-id (first jobs))))
        (is (= :verifier (:role (first jobs))))))))

(deftest job-priority-ordering-test
  (testing "Jobs are ordered by priority"
    (init-repo!)
    (create-root-mote! "1" "Low priority" :priority :p3)
    (create-root-mote! "2" "High priority" :priority :p1)
    (create-root-mote! "3" "Medium priority" :priority :p2)
    (create-child-mote! "1.1" "Low prio child" "1" :priority :p3)
    (create-child-mote! "2.1" "High prio child" "2" :priority :p1)
    (create-child-mote! "3.1" "Med prio child" "3" :priority :p2)
    (add-verification-taint! "1.1")
    (add-verification-taint! "2.1")
    (add-verification-taint! "3.1")

    (let [motes (load-all-motes)
          ;; Filter for verifier role to get child motes with :needs-verification
          jobs (job/select-jobs motes :role :verifier :max 10)]
      ;; High priority should come first
      (is (= "2.1" (:mote-id (first jobs))))
      (is (= :p1 (:priority (first jobs)))))))

;; =============================================================================
;; 7. Contested Verification Test
;; =============================================================================

(deftest contested-verification-test
  (testing "Mixed votes lead to contested status"
    (init-repo! :vote-quorum 2)
    (create-root-mote! "1" "Controversial theorem")
    (create-child-mote! "1.1" "Contested claim" "1")
    (add-verification-taint! "1.1")

    ;; First verifier votes FOR
    (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "I agree")

    ;; Second verifier votes AGAINST
    (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-2" :against
                                    :reason "I disagree")]
      (is (= :contested (:quorum-status (:result result)))))

    ;; Final status should be contested
    (is (= :contested (:status (load-mote "1.1"))))))

(deftest refuted-verification-test
  (testing "Unanimous against votes lead to refuted status"
    (init-repo! :vote-quorum 2)
    (create-root-mote! "1" "Wrong theorem")
    (create-child-mote! "1.1" "False claim" "1")
    (add-verification-taint! "1.1")

    ;; First verifier votes AGAINST
    (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :against :reason "This is wrong")

    ;; Second verifier votes AGAINST
    (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-2" :against
                                    :reason "Agree, this is wrong")]
      (is (= :refuted (:quorum-status (:result result)))))

    ;; Final status should be refuted
    (is (= :refuted (:status (load-mote "1.1"))))))

;; =============================================================================
;; 8. Full Proof Lifecycle Test
;; =============================================================================

(deftest full-proof-lifecycle-test
  (testing "Complete proof lifecycle from creation to verification"
    (init-repo! :proposal-quorum 1 :vote-quorum 1)

    ;; Create root theorem
    (create-root-mote! "1" "Main Theorem: P implies Q")
    (add-decomposition-taint! "1")

    ;; Proposer decomposes
    (let [proposer-sess (claim-mote! "1" "proposer" :proposer)]
      (proposal/create-proposal! *temp-dir* "1"
                                 [{:claim "Lemma 1: P"}
                                  {:claim "Lemma 2: P -> Q"}]
                                 "proposer")
      (end-session! (:session-id proposer-sess)))

    ;; Advisor approves
    (let [advisor-sess (claim-mote! "1" "advisor" :advisor)]
      (proposal/approve-proposal! *temp-dir* "1" "advisor"
                                  :reason "Good decomposition")
      (end-session! (:session-id advisor-sess)))

    ;; Verify children are promoted
    (is (= :fixed (:status (load-mote "1.1"))))
    (is (= :fixed (:status (load-mote "1.2"))))

    ;; Add verification taints
    (add-verification-taint! "1.1")
    (add-verification-taint! "1.2")

    ;; Verify first child
    (let [v1-sess (claim-mote! "1.1" "verifier-1" :verifier)]
      (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "Verified")
      (end-session! (:session-id v1-sess)))

    ;; Verify second child
    (let [v2-sess (claim-mote! "1.2" "verifier-2" :verifier)]
      (verify/cast-vote! *temp-dir* "1.2" "verifier-2" :for :reason "Verified")
      (end-session! (:session-id v2-sess)))

    ;; Both children should be verified
    (is (= :verified (:status (load-mote "1.1"))))
    (is (= :verified (:status (load-mote "1.2"))))

    ;; DAG should be valid
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (:valid? validation))
      (is (empty? (:errors validation))))))

;; =============================================================================
;; 9. Session Reservation Tests
;; =============================================================================

(deftest session-reservation-lifecycle-test
  (testing "Reservation workflow: reserve -> claim -> session"
    (init-repo!)
    (create-root-mote! "1" "Reservation test")
    (create-child-mote! "1.1" "Test child" "1")
    (add-verification-taint! "1.1")

    (session/ensure-session-dirs! *temp-dir*)

    ;; Create reservation
    (let [reservation (session/create-reservation! *temp-dir* "1.1" :verifier)]
      (is (some? (:token reservation)))
      (is (= "1.1" (:mote-id reservation)))
      (is (= :verifier (:role reservation)))

      ;; Claim reservation - use a different agent than the mote creator
      ;; (mote creator is "test-agent", contributors can't vote on their own work)
      (let [sess (session/claim-reservation! *temp-dir* (:token reservation) "verifier-agent")]
        (is (some? (:session-id sess)))
        (is (= "1.1" (:mote-id sess)))
        (is (= :verifier (:role sess)))
        (is (= "verifier-agent" (:agent sess)))

        ;; Reservation should be consumed (deleted)
        (is (nil? (session/load-reservation *temp-dir* (:token reservation))))

        ;; Can use session for actions (using the session agent, not creator)
        (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-agent" :for
                                        :reason "Test")]
          (is (some? (:result result))))))))

(deftest expired-reservation-rejection-test
  (testing "Expired reservations cannot be claimed"
    (init-repo!)
    (create-root-mote! "1" "Expiry test")
    (create-child-mote! "1.1" "Test child" "1")

    (session/ensure-session-dirs! *temp-dir*)

    ;; Create reservation with 0 duration
    (let [reservation (session/create-reservation! *temp-dir* "1.1" :verifier
                                                   :duration-seconds 0)]
      ;; Wait for expiration
      (Thread/sleep 10)

      ;; Should fail to claim expired reservation
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"[Ii]nvalid.*[Ee]xpired|[Ee]xpired.*[Rr]eservation"
           (session/claim-reservation! *temp-dir* (:token reservation) "test-agent"))))))

;; =============================================================================
;; 10. DAG Consistency Tests
;; =============================================================================

(deftest dag-consistency-after-operations-test
  (testing "DAG remains consistent after complex operations"
    (init-repo! :proposal-quorum 1)

    ;; Build a complex DAG
    (create-root-mote! "1" "Main theorem")
    (proposal/create-proposal! *temp-dir* "1"
                               [{:claim "Lemma 1"}
                                {:claim "Lemma 2"}]
                               "proposer")
    (proposal/approve-proposal! *temp-dir* "1" "advisor")

    ;; Add internal assumptions
    (let [mote-1-2 (load-mote "1.2")
          ;; 1.2 assumes 1.1
          updated-1-2 (mote/add-assumption mote-1-2 {:type :internal :ref "1.1"})]
      (store/save-mote! *temp-dir* updated-1-2)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Add assumption"))

    ;; Verify DAG is consistent
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (:valid? validation))
      (is (empty? (:errors validation))))))
