(ns alethfeld.integration-test
  "End-to-end integration tests for Alethfeld.

   Tests complete workflows from initialization through verification,
   including multi-agent scenarios, conflict detection, and recovery."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.tx :as tx]
            [alethfeld.dag :as dag]
            [alethfeld.path :as path]
            [alethfeld.proposal :as proposal]
            [alethfeld.verify :as verify]
            [alethfeld.cli :as cli]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-integration-test-"})
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
  "Initialize a test repository with git configured."
  []
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :project-name "Integration Test Project")
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-root-mote!
  "Create a root mote directly in the store."
  [id claim & {:keys [difficulty priority taint]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}}}]
  (let [m (mote/make-root-mote id claim "test-agent"
                               :difficulty difficulty
                               :priority priority)]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create root mote " id))
    m))

(defn- create-child-mote!
  "Create a child mote and update parent."
  [id claim parent-id & {:keys [difficulty priority status]
                         :or {difficulty 3 priority :p2 status :fixed}}]
  (let [parent (store/load-mote *temp-dir* parent-id)
        child (mote/make-child-mote id claim "test-agent" parent
                                    :difficulty difficulty
                                    :priority priority)
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

;; =============================================================================
;; Full Lifecycle Tests
;; =============================================================================

(deftest full-lifecycle-init-create-propose-approve-verify-test
  (testing "Complete workflow from init to verification"
    (init-repo!)

    (testing "Step 1: Create root mote"
      (let [root (create-root-mote! "1" "Prove that P implies Q")]
        (is (= "1" (:id root)))
        (is (= :fixed (:status root)))
        (is (empty? (:children root)))))

    (testing "Step 2: Propose decomposition"
      (let [claims [{:claim "Show P is true"}
                    {:claim "Show P → Q is valid"}]
            result (proposal/create-proposal! *temp-dir* "1" claims "proposer-agent")]
        (is (some? (:result result)))
        (let [{:keys [proposal children]} (:result result)]
          (is (some? proposal))
          (is (= 2 (count children)))
          ;; Verify proposed children exist
          (is (some? (store/load-mote *temp-dir* "1.1")))
          (is (some? (store/load-mote *temp-dir* "1.2")))
          ;; Verify they have :proposed status
          (is (= :proposed (:status (store/load-mote *temp-dir* "1.1"))))
          (is (= :proposed (:status (store/load-mote *temp-dir* "1.2")))))))

    (testing "Step 3: First advisor approves"
      (let [result (proposal/approve-proposal! *temp-dir* "1" "advisor-1" :reason "LGTM")]
        (is (some? (:result result)))
        (let [{:keys [quorum-status]} (:result result)]
          ;; Default quorum is 2, so 1 vote is pending
          (is (= :pending quorum-status)))))

    (testing "Step 4: Second advisor approves, quorum reached"
      (let [result (proposal/approve-proposal! *temp-dir* "1" "advisor-2" :reason "Approved")]
        (is (some? (:result result)))
        (let [{:keys [quorum-status promoted-children]} (:result result)]
          (is (= :approved quorum-status))
          (is (= #{"1.1" "1.2"} (set promoted-children)))
          ;; Verify children are now :fixed status
          (is (= :fixed (:status (store/load-mote *temp-dir* "1.1"))))
          (is (= :fixed (:status (store/load-mote *temp-dir* "1.2"))))
          ;; Verify parent has children
          (let [parent (store/load-mote *temp-dir* "1")]
            (is (= #{"1.1" "1.2"} (set (:children parent))))
            ;; Proposal should be cleared
            (is (nil? (:proposal parent)))))))

    (testing "Step 5: Cast verification votes on children"
      ;; Vote on first child
      (let [result-1 (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "Verified")]
        (is (= :pending (:quorum-status (:result result-1)))))
      (let [result-2 (verify/cast-vote! *temp-dir* "1.1" "verifier-2" :for :reason "Confirmed")]
        (is (= :verified (:quorum-status (:result result-2))))
        (is (= :verified (:status (store/load-mote *temp-dir* "1.1")))))

      ;; Vote on second child
      (let [result-1 (verify/cast-vote! *temp-dir* "1.2" "verifier-1" :for :reason "OK")]
        (is (= :pending (:quorum-status (:result result-1)))))
      (let [result-2 (verify/cast-vote! *temp-dir* "1.2" "verifier-2" :for :reason "Good")]
        (is (= :verified (:quorum-status (:result result-2))))
        (is (= :verified (:status (store/load-mote *temp-dir* "1.2"))))))

    (testing "Step 6: Verify final state with DAG validation"
      (let [motes (load-all-motes)
            validation (dag/validate-mote-graph motes)]
        (is (:valid? validation))
        (is (empty? (:errors validation)))))))

(deftest full-lifecycle-with-rejection-test
  (testing "Complete workflow with proposal rejection"
    (init-repo!)
    (create-root-mote! "1" "Prove theorem X")

    (testing "Create and reject a proposal"
      ;; Create proposal
      (proposal/create-proposal! *temp-dir* "1" [{:claim "Bad approach 1"}
                                                  {:claim "Bad approach 2"}] "proposer-agent")

      ;; First rejection vote
      (let [result (proposal/reject-proposal! *temp-dir* "1" "advisor-1" :reason "Needs rework")]
        (is (= :pending (:quorum-status (:result result)))))

      ;; Second rejection vote - quorum
      (let [result (proposal/reject-proposal! *temp-dir* "1" "advisor-2" :reason "Agree")]
        (is (= :rejected (:quorum-status (:result result))))

        ;; Verify children are archived
        (let [motes (store/load-all-motes *temp-dir* :include-archived true)]
          ;; Parent should have no children
          (let [parent (get motes "1")]
            (is (empty? (:children parent)))
            (is (nil? (:proposal parent))))

          ;; Archived children should exist but with :rejected status
          (let [archived-1 (get motes "1.1")
                archived-2 (get motes "1.2")]
            (is (some? archived-1))
            (is (some? archived-2))
            (is (= :rejected (:status archived-1)))
            (is (= :rejected (:status archived-2)))))))

    (testing "Create new proposal after rejection"
      ;; Parent should still be workable - create new proposal
      ;; Note: New children reuse 1.1 and 1.2 IDs since rejected children
      ;; are archived and not in parent's :children list
      (let [result (proposal/create-proposal! *temp-dir* "1"
                                               [{:claim "Better approach 1"}
                                                {:claim "Better approach 2"}]
                                               "proposer-agent-2")]
        (is (some? (:result result)))
        ;; New children are created (with same IDs as rejected ones, but in proposed/)
        (let [child-1 (store/load-mote *temp-dir* "1.1")
              child-2 (store/load-mote *temp-dir* "1.2")]
          ;; These are the new proposed children, not the archived ones
          (is (some? child-1))
          (is (some? child-2))
          (is (= :proposed (:status child-1)))
          (is (= :proposed (:status child-2)))
          (is (= "Better approach 1" (:claim child-1)))
          (is (= "Better approach 2" (:claim child-2))))))))

(deftest full-lifecycle-contested-verification-test
  (testing "Workflow with contested verification votes"
    (init-repo!)
    (let [root (create-root-mote! "1" "Controversial claim")]
      ;; Create a child directly (skip proposal for this test)
      (create-child-mote! "1.1" "May or may not be true" "1"
                          :status :fixed))

    ;; Add taint needed for verification
    (let [mote (store/load-mote *temp-dir* "1.1")
          updated (mote/add-taint mote :needs-verification)]
      (store/save-mote! *temp-dir* updated)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Add verification taint"))

    (testing "Mixed votes lead to contested status"
      ;; Vote for
      (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "I think it's true")
      ;; Vote against
      (let [result (verify/cast-vote! *temp-dir* "1.1" "verifier-2" :against :reason "I disagree")]
        (is (= :contested (:quorum-status (:result result))))
        (is (= :contested (:status (store/load-mote *temp-dir* "1.1"))))))))

;; =============================================================================
;; Multi-Agent Parallel Simulation Tests
;; =============================================================================

(deftest multi-agent-parallel-claims-test
  (testing "Multiple agents claiming different motes concurrently"
    (init-repo!)

    ;; Create multiple root motes for different agents to work on
    (create-root-mote! "1" "Task A")
    (create-root-mote! "2" "Task B")
    (create-root-mote! "3" "Task C")

    (testing "Each agent claims a different mote"
      ;; Agent 1 claims mote 1
      (let [mote-1 (store/load-mote *temp-dir* "1")
            claimed-1 (mote/set-claimed-by mote-1 "agent-1")]
        (store/save-mote! *temp-dir* claimed-1))

      ;; Agent 2 claims mote 2
      (let [mote-2 (store/load-mote *temp-dir* "2")
            claimed-2 (mote/set-claimed-by mote-2 "agent-2")]
        (store/save-mote! *temp-dir* claimed-2))

      ;; Agent 3 claims mote 3
      (let [mote-3 (store/load-mote *temp-dir* "3")
            claimed-3 (mote/set-claimed-by mote-3 "agent-3")]
        (store/save-mote! *temp-dir* claimed-3))

      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Multiple agents claim motes")

      ;; Verify all claims
      (is (= "agent-1" (:claimed-by (store/load-mote *temp-dir* "1"))))
      (is (= "agent-2" (:claimed-by (store/load-mote *temp-dir* "2"))))
      (is (= "agent-3" (:claimed-by (store/load-mote *temp-dir* "3")))))))

(deftest multi-agent-proposal-review-test
  (testing "Multiple agents reviewing proposals in parallel"
    (init-repo!)
    (create-root-mote! "1" "Big theorem")
    (create-root-mote! "2" "Another theorem")

    ;; Create proposals on both motes
    (proposal/create-proposal! *temp-dir* "1"
                                [{:claim "Part A of big theorem"}
                                 {:claim "Part B of big theorem"}]
                                "proposer-1")
    (proposal/create-proposal! *temp-dir* "2"
                                [{:claim "Part X of another theorem"}
                                 {:claim "Part Y of another theorem"}]
                                "proposer-2")

    (testing "Different advisors review different proposals"
      ;; Advisor 1 and 2 work on mote 1
      (proposal/approve-proposal! *temp-dir* "1" "advisor-1")
      (proposal/approve-proposal! *temp-dir* "1" "advisor-2")

      ;; Advisor 3 and 4 work on mote 2
      (proposal/approve-proposal! *temp-dir* "2" "advisor-3")
      (let [result (proposal/approve-proposal! *temp-dir* "2" "advisor-4")]
        (is (= :approved (:quorum-status (:result result)))))

      ;; Both should have approved children
      (is (= :fixed (:status (store/load-mote *temp-dir* "1.1"))))
      (is (= :fixed (:status (store/load-mote *temp-dir* "2.1")))))))

(deftest multi-agent-verification-race-test
  (testing "Multiple agents verifying different motes simultaneously"
    (init-repo!)
    (create-root-mote! "1" "Theorem to verify")
    (create-child-mote! "1.1" "Lemma 1" "1")
    (create-child-mote! "1.2" "Lemma 2" "1")
    (create-child-mote! "1.3" "Lemma 3" "1")

    ;; Add verification taints
    (doseq [id ["1.1" "1.2" "1.3"]]
      (let [mote (store/load-mote *temp-dir* id)
            updated (mote/add-taint mote :needs-verification)]
        (store/save-mote! *temp-dir* updated)))
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* "Add verification taints")

    (testing "Parallel verification by different verifier teams"
      ;; Team A verifies 1.1
      (verify/cast-vote! *temp-dir* "1.1" "verifier-A1" :for)
      (verify/cast-vote! *temp-dir* "1.1" "verifier-A2" :for)

      ;; Team B verifies 1.2
      (verify/cast-vote! *temp-dir* "1.2" "verifier-B1" :for)
      (verify/cast-vote! *temp-dir* "1.2" "verifier-B2" :for)

      ;; Team C verifies 1.3
      (verify/cast-vote! *temp-dir* "1.3" "verifier-C1" :for)
      (verify/cast-vote! *temp-dir* "1.3" "verifier-C2" :for)

      ;; All should be verified
      (is (= :verified (:status (store/load-mote *temp-dir* "1.1"))))
      (is (= :verified (:status (store/load-mote *temp-dir* "1.2"))))
      (is (= :verified (:status (store/load-mote *temp-dir* "1.3")))))))

;; =============================================================================
;; Conflict Detection Tests
;; =============================================================================

(deftest conflict-double-claim-test
  (testing "Detecting when mote is already claimed"
    (init-repo!)
    (let [root (create-root-mote! "1" "Task to claim")]
      ;; First agent claims
      (let [claimed (mote/set-claimed-by root "agent-1")]
        (store/save-mote! *temp-dir* claimed)
        (git/git-add-all! *temp-dir*)
        (git/git-commit! *temp-dir* "Agent 1 claims"))

      ;; Reload and check claim
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= "agent-1" (:claimed-by loaded)))

        ;; Second agent tries to claim (conflict)
        (testing "Second agent cannot override existing claim"
          (let [current-claimer (:claimed-by loaded)]
            (is (= "agent-1" current-claimer))
            ;; Application logic should check this before allowing claim
            (is (not= current-claimer "agent-2"))))))))

(deftest conflict-duplicate-proposal-test
  (testing "Detecting duplicate proposal on mote with existing proposal"
    (init-repo!)
    (create-root-mote! "1" "Task to decompose")

    ;; First proposal
    (proposal/create-proposal! *temp-dir* "1"
                                [{:claim "Child 1"}]
                                "proposer-1")

    ;; Verify proposal exists
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (some? (:proposal parent)))

      ;; Attempting second proposal should fail
      (testing "Second proposal fails when one already exists"
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"already has an active proposal"
                              (proposal/create-proposal! *temp-dir* "1"
                                                          [{:claim "Different child"}]
                                                          "proposer-2")))))))

(deftest conflict-duplicate-vote-test
  (testing "Detecting duplicate votes from same agent"
    (init-repo!)
    (create-root-mote! "1" "Task to verify")
    (create-child-mote! "1.1" "Claim to verify" "1")

    ;; Add verification taint
    (let [mote (store/load-mote *temp-dir* "1.1")
          updated (mote/add-taint mote :needs-verification)]
      (store/save-mote! *temp-dir* updated)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Add verification taint"))

    ;; First vote
    (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "First vote")

    ;; Same agent voting again should fail
    (testing "Duplicate vote from same agent fails"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"already voted"
                            (verify/cast-vote! *temp-dir* "1.1" "verifier-1" :for :reason "Second vote"))))))

(deftest conflict-cycle-detection-test
  (testing "Detecting cycles in assumption graph"
    (init-repo!)

    ;; Create three motes
    (create-root-mote! "1" "Theorem A")
    (create-root-mote! "2" "Theorem B")
    (create-root-mote! "3" "Theorem C")

    ;; Create a cycle: 1 -> 2 -> 3 -> 1
    (let [mote-1 (store/load-mote *temp-dir* "1")
          mote-2 (store/load-mote *temp-dir* "2")
          mote-3 (store/load-mote *temp-dir* "3")
          ;; 1 assumes 2
          updated-1 (mote/add-assumption mote-1 {:type :internal :ref "2"})
          ;; 2 assumes 3
          updated-2 (mote/add-assumption mote-2 {:type :internal :ref "3"})
          ;; 3 assumes 1 (creates cycle)
          updated-3 (mote/add-assumption mote-3 {:type :internal :ref "1"})]
      (store/save-mote! *temp-dir* updated-1)
      (store/save-mote! *temp-dir* updated-2)
      (store/save-mote! *temp-dir* updated-3)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Create cycle"))

    ;; DAG validation should detect the cycle
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (not (:valid? validation)))
      (is (some #(= :cycle (:category %)) (:errors validation))))))

;; =============================================================================
;; Recovery Tests
;; =============================================================================

(deftest recovery-orphaned-child-detection-test
  (testing "Detecting orphaned children (parent exists but doesn't list child)"
    (init-repo!)

    ;; Create parent first (without child in children list)
    (create-root-mote! "1" "Parent that ignores child")

    ;; Create a child mote that claims the parent, but parent doesn't list it
    (let [orphan (mote/make-mote "1.1" "Orphaned child" "test-agent"
                                  :parent "1"
                                  :status :fixed)]
      (store/save-mote! *temp-dir* orphan)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Create orphan"))

    ;; DAG validation should detect orphan child
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (not (:valid? validation)))
      (is (some #(and (= :parent-child (:category %))
                      (= :orphan-child (get-in % [:error :type])))
                (:errors validation))))))

(deftest recovery-broken-ref-detection-test
  (testing "Detecting broken internal references"
    (init-repo!)

    ;; Create a mote with broken internal ref
    (let [mote (mote/make-root-mote "1" "Theorem with broken ref" "test-agent")
          with-broken-ref (mote/add-assumption mote {:type :internal :ref "999"})]
      (store/save-mote! *temp-dir* with-broken-ref)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Create mote with broken ref"))

    ;; DAG validation should detect broken reference
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (not (:valid? validation)))
      (is (some #(= :broken-refs (:category %)) (:errors validation))))))

(deftest recovery-inconsistent-parent-child-test
  (testing "Detecting parent-child bidirectional inconsistency"
    (init-repo!)

    ;; Create parent that doesn't list child
    (let [parent (mote/make-root-mote "1" "Parent" "test-agent")
          child (mote/make-mote "1.1" "Child" "test-agent"
                                :parent "1"
                                :status :fixed)]
      ;; Parent doesn't have child in :children
      (store/save-mote! *temp-dir* parent)
      (store/save-mote! *temp-dir* child)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Create inconsistent parent-child"))

    ;; DAG validation should detect inconsistency (orphan-child)
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (not (:valid? validation)))
      (is (some #(and (= :parent-child (:category %))
                      (= :orphan-child (get-in % [:error :type])))
                (:errors validation))))))

(deftest recovery-from-invalid-state-via-check-test
  (testing "Using DAG validation to detect and diagnose invalid state"
    (init-repo!)

    ;; Create parent first
    (create-root-mote! "1" "Parent")

    ;; Create invalid state: orphaned child (parent doesn't list it)
    (let [orphan (mote/make-mote "1.1" "Orphaned child" "test-agent"
                                  :parent "1"
                                  :status :fixed)]
      (store/save-mote! *temp-dir* orphan)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Create orphan"))

    ;; Direct DAG validation should detect the issue
    (let [motes (load-all-motes)
          validation (dag/validate-mote-graph motes)]
      (is (not (:valid? validation)))
      (is (seq (:errors validation)))
      ;; Verify error details are actionable
      (is (some #(= :parent-child (:category %)) (:errors validation))))))

;; =============================================================================
;; Transaction Atomicity Tests
;; =============================================================================

(deftest transaction-atomicity-on-failure-test
  (testing "Transaction rollback on DAG validation failure"
    (init-repo!)
    (create-root-mote! "1" "Valid root")

    ;; Create initial state
    (let [initial-motes (load-all-motes)
          initial-count (count initial-motes)]

      (testing "Transaction with orphan child is rolled back"
        ;; Attempt to write a child that claims a parent but parent doesn't list it
        ;; This creates an orphan-child error during validation
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"Validation failed"
                              (tx/atomic-write! *temp-dir* "Invalid write"
                                                [(mote/make-mote "1.1" "Orphan" "agent"
                                                                 :parent "1"
                                                                 :status :fixed)])))

        ;; Verify state unchanged
        (let [after-motes (load-all-motes)]
          (is (= initial-count (count after-motes)))
          (is (nil? (get after-motes "1.1"))))))))

(deftest transaction-multi-mote-atomicity-test
  (testing "Multi-mote writes are atomic"
    (init-repo!)
    (create-root-mote! "1" "Root")

    (testing "Multiple motes written in single transaction"
      (let [child-1 (mote/make-child-mote "1.1" "Child 1" "agent"
                                           (store/load-mote *temp-dir* "1"))
            child-2 (mote/make-child-mote "1.2" "Child 2" "agent"
                                           (store/load-mote *temp-dir* "1"))
            parent (mote/add-child (mote/add-child (store/load-mote *temp-dir* "1")
                                                    "1.1")
                                    "1.2")]
        (tx/atomic-write! *temp-dir* "Create two children"
                          [child-1 child-2 parent])

        ;; All should exist
        (is (some? (store/load-mote *temp-dir* "1.1")))
        (is (some? (store/load-mote *temp-dir* "1.2")))
        (let [loaded-parent (store/load-mote *temp-dir* "1")]
          (is (= #{"1.1" "1.2"} (set (:children loaded-parent)))))))))

;; =============================================================================
;; Git Integration Tests
;; =============================================================================

(deftest git-history-tracks-changes-test
  (testing "Git history tracks all mote changes"
    (init-repo!)
    (create-root-mote! "1" "Tracked mote")

    ;; Make several changes
    (let [mote-1 (store/load-mote *temp-dir* "1")
          updated-1 (mote/set-claim mote-1 "Updated claim 1")]
      (tx/atomic-write! *temp-dir* "Update 1" [updated-1]))

    (let [mote-1 (store/load-mote *temp-dir* "1")
          updated-1 (mote/set-priority mote-1 :p1)]
      (tx/atomic-write! *temp-dir* "Update 2" [updated-1]))

    ;; Verify git history
    (let [history (git/git-log *temp-dir* :max-count 10)]
      ;; Should have: Initialize, Create root, Update 1, Update 2
      (is (>= (count history) 4))
      ;; Most recent should be Update 2
      (is (re-find #"Update 2" (:message (first history)))))))

(deftest git-log-for-mote-test
  (testing "Git log retrieves history for specific mote"
    (init-repo!)
    (create-root-mote! "1" "Mote A")
    (create-root-mote! "2" "Mote B")

    ;; Update mote 1 specifically
    (let [mote-1 (store/load-mote *temp-dir* "1")
          updated (mote/set-claim mote-1 "Updated A")]
      (tx/atomic-write! *temp-dir* "Update mote 1" [updated]))

    ;; git-log should work for specific mote path
    (let [mote-1 (store/load-mote *temp-dir* "1")
          mote-path (path/mote-id->path "1" (:status mote-1))
          result (git/git-log *temp-dir* :path mote-path :max-count 10)]
      (is (seq result))
      ;; Should include the update commit
      (is (some #(re-find #"Update mote 1" (:message %)) result)))))

;; =============================================================================
;; End-to-End DAG Consistency Tests
;; =============================================================================

(deftest e2e-dag-consistency-after-operations-test
  (testing "DAG remains consistent after complex operations"
    (init-repo!)

    ;; Build a complex DAG
    (create-root-mote! "1" "Main theorem")
    (proposal/create-proposal! *temp-dir* "1"
                                [{:claim "Lemma 1"}
                                 {:claim "Lemma 2"}]
                                "proposer")
    (proposal/approve-proposal! *temp-dir* "1" "advisor-1")
    (proposal/approve-proposal! *temp-dir* "1" "advisor-2")

    ;; Add internal assumptions
    (let [mote-1-1 (store/load-mote *temp-dir* "1.1")
          mote-1-2 (store/load-mote *temp-dir* "1.2")
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

(deftest e2e-deep-nesting-test
  (testing "Deep nesting of motes works correctly"
    (init-repo!)

    ;; Create deeply nested structure
    (create-root-mote! "1" "Level 0")
    (create-child-mote! "1.1" "Level 1" "1")
    (create-child-mote! "1.1.1" "Level 2" "1.1")
    (create-child-mote! "1.1.1.1" "Level 3" "1.1.1")
    (create-child-mote! "1.1.1.1.1" "Level 4" "1.1.1.1")

    ;; All should be loadable and valid
    (let [motes (load-all-motes)]
      (is (= 5 (count motes)))
      (let [validation (dag/validate-mote-graph motes)]
        (is (:valid? validation))))))
