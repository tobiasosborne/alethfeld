(ns alethfeld.proposal-test
  "Tests for proposal workflow."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [alethfeld.proposal :as proposal]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.io :as io]
            [alethfeld.path :as path]
            [babashka.fs :as fs]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *test-repo* nil)

(defn with-temp-repo [f]
  (let [temp-dir (str (fs/create-temp-dir {:prefix "alethfeld-test-"}))]
    (try
      (store/init-repo! temp-dir :config {:project-name "Test"
                                          :version "0.1"
                                          :default-difficulty 3
                                          :vote-quorum 2
                                          :proposal-quorum 2
                                          :claim-timeout-minutes 30})
      (binding [*test-repo* temp-dir]
        (f))
      (finally
        (fs/delete-tree temp-dir)))))

(use-fixtures :each with-temp-repo)

;; -----------------------------------------------------------------------------
;; Helper Functions
;; -----------------------------------------------------------------------------

(defn create-test-mote!
  "Create and save a test mote."
  [id claim & {:keys [status taint difficulty priority]
               :or {status :fixed
                    taint #{:needs-decomposition}
                    difficulty 3
                    priority :p2}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :status status
                          :taint taint
                          :difficulty difficulty
                          :priority priority)]
    (store/save-mote! *test-repo* m)
    m))

(defn file-exists-in?
  "Check if a mote file exists in a specific directory."
  [mote-id dir]
  (let [filename (str mote-id ".edn")
        path (str *test-repo* "/.alethfeld/" dir "/" filename)]
    (io/file-exists? path)))

;; -----------------------------------------------------------------------------
;; Pure Function Tests
;; -----------------------------------------------------------------------------

(deftest count-votes-test
  (testing "empty votes"
    (let [proposal {:id "p1" :votes []}]
      (is (= {:approve 0 :reject 0} (proposal/count-votes proposal)))))

  (testing "approve votes only"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :approve}
                            {:agent "a2" :vote :approve}]}]
      (is (= {:approve 2 :reject 0} (proposal/count-votes proposal)))))

  (testing "reject votes only"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :reject}]}]
      (is (= {:approve 0 :reject 1} (proposal/count-votes proposal)))))

  (testing "mixed votes"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :approve}
                            {:agent "a2" :vote :reject}
                            {:agent "a3" :vote :approve}]}]
      (is (= {:approve 2 :reject 1} (proposal/count-votes proposal))))))

(deftest check-proposal-quorum-test
  (testing "pending with no votes"
    (let [proposal {:id "p1" :votes []}]
      (is (= :pending (proposal/check-proposal-quorum proposal 2)))))

  (testing "pending with one approve"
    (let [proposal {:id "p1" :votes [{:agent "a1" :vote :approve}]}]
      (is (= :pending (proposal/check-proposal-quorum proposal 2)))))

  (testing "approved at quorum"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :approve}
                            {:agent "a2" :vote :approve}]}]
      (is (= :approved (proposal/check-proposal-quorum proposal 2)))))

  (testing "approved above quorum"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :approve}
                            {:agent "a2" :vote :approve}
                            {:agent "a3" :vote :approve}]}]
      (is (= :approved (proposal/check-proposal-quorum proposal 2)))))

  (testing "rejected at quorum"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :reject}
                            {:agent "a2" :vote :reject}]}]
      (is (= :rejected (proposal/check-proposal-quorum proposal 2)))))

  (testing "quorum of 1"
    (let [proposal {:id "p1" :votes [{:agent "a1" :vote :approve}]}]
      (is (= :approved (proposal/check-proposal-quorum proposal 1)))))

  (testing "mixed votes not at quorum"
    (let [proposal {:id "p1"
                    :votes [{:agent "a1" :vote :approve}
                            {:agent "a2" :vote :reject}]}]
      (is (= :pending (proposal/check-proposal-quorum proposal 2))))))

(deftest has-voted-test
  (testing "agent has not voted"
    (let [proposal {:id "p1" :votes [{:agent "other" :vote :approve}]}]
      (is (not (proposal/has-voted? proposal "agent1")))))

  (testing "agent has voted"
    (let [proposal {:id "p1" :votes [{:agent "agent1" :vote :approve}]}]
      (is (proposal/has-voted? proposal "agent1"))))

  (testing "empty votes"
    (let [proposal {:id "p1" :votes []}]
      (is (not (proposal/has-voted? proposal "agent1"))))))

;; -----------------------------------------------------------------------------
;; create-proposal! Tests
;; -----------------------------------------------------------------------------

(deftest create-proposal-basic-test
  (testing "creates proposed children"
    (create-test-mote! "1" "Root claim")
    (let [result (proposal/create-proposal!
                  *test-repo* "1"
                  [{:claim "First step"}
                   {:claim "Second step"}]
                  "proposer-1")
          {:keys [proposal children]} (:result result)]
      ;; Check proposal structure
      (is (string? (:id proposal)))
      (is (= "proposer-1" (:proposed-by proposal)))
      (is (= :pending (:status proposal)))
      (is (= ["1.1" "1.2"] (:children proposal)))
      (is (empty? (:votes proposal)))

      ;; Check children were created
      (is (= 2 (count children)))
      (is (= "1.1" (:id (first children))))
      (is (= "First step" (:claim (first children))))
      (is (= :proposed (:status (first children))))

      ;; Check files exist in proposed/
      (is (file-exists-in? "1.1" "proposed"))
      (is (file-exists-in? "1.2" "proposed")))))

(deftest create-proposal-updates-parent-test
  (testing "parent gets proposal and taint update"
    (create-test-mote! "1" "Root claim" :taint #{:needs-decomposition})
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [parent (store/load-mote *test-repo* "1")]
      (is (some? (:proposal parent)))
      (is (contains? (:taint parent) :needs-proposal-review))
      (is (not (contains? (:taint parent) :needs-decomposition))))))

(deftest create-proposal-inherits-difficulty-test
  (testing "children inherit difficulty from parent"
    (create-test-mote! "1" "Root" :difficulty 4)
    (let [result (proposal/create-proposal!
                  *test-repo* "1"
                  [{:claim "Step without difficulty"}
                   {:claim "Step with difficulty" :difficulty 2}]
                  "proposer-1")
          children (:children (:result result))]
      (is (= 4 (:difficulty (first children))))  ;; inherited
      (is (= 2 (:difficulty (second children))))))) ;; overridden

(deftest create-proposal-generates-sequential-ids-test
  (testing "child IDs are sequential"
    (create-test-mote! "1" "Root")
    (let [result (proposal/create-proposal!
                  *test-repo* "1"
                  [{:claim "A"} {:claim "B"} {:claim "C"}]
                  "proposer-1")
          child-ids (mapv :id (:children (:result result)))]
      (is (= ["1.1" "1.2" "1.3"] child-ids)))))

(deftest create-proposal-error-parent-not-found-test
  (testing "throws when parent not found"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Parent mote not found"
         (proposal/create-proposal!
          *test-repo* "nonexistent"
          [{:claim "Step"}]
          "proposer-1")))))

(deftest create-proposal-error-already-has-proposal-test
  (testing "throws when parent already has proposal"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"already has an active proposal"
         (proposal/create-proposal!
          *test-repo* "1"
          [{:claim "Another step"}]
          "proposer-2")))))

;; -----------------------------------------------------------------------------
;; approve-proposal! Tests
;; -----------------------------------------------------------------------------

(deftest approve-proposal-single-vote-test
  (testing "single approve vote - pending"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [result (proposal/approve-proposal!
                  *test-repo* "1" "advisor-1"
                  :reason "Looks good")
          {:keys [vote-cast quorum-status promoted-children]} (:result result)]
      ;; Vote was cast
      (is (= :approve (:vote vote-cast)))
      (is (= "advisor-1" (:agent vote-cast)))
      (is (= "Looks good" (:reason vote-cast)))
      ;; Not at quorum yet
      (is (= :pending quorum-status))
      (is (nil? promoted-children))
      ;; Child still in proposed/
      (is (file-exists-in? "1.1" "proposed")))))

(deftest approve-proposal-quorum-reached-test
  (testing "second approve vote reaches quorum - children promoted"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step A"} {:claim "Step B"}]
     "proposer-1")
    ;; First vote
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    ;; Second vote - quorum!
    (let [result (proposal/approve-proposal! *test-repo* "1" "advisor-2")
          {:keys [quorum-status promoted-children]} (:result result)]
      (is (= :approved quorum-status))
      (is (= ["1.1" "1.2"] promoted-children))
      ;; Children moved to motes/
      (is (not (file-exists-in? "1.1" "proposed")))
      (is (not (file-exists-in? "1.2" "proposed")))
      ;; Check children are now :fixed in motes/
      (let [child1 (store/load-mote *test-repo* "1.1")
            child2 (store/load-mote *test-repo* "1.2")]
        (is (= :fixed (:status child1)))
        (is (= :fixed (:status child2)))))))

(deftest approve-proposal-updates-parent-test
  (testing "parent updated after quorum approval"
    (create-test-mote! "1" "Root" :taint #{})
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-2")
    (let [parent (store/load-mote *test-repo* "1")]
      ;; Proposal cleared
      (is (nil? (:proposal parent)))
      ;; Children populated
      (is (= ["1.1"] (:children parent)))
      ;; Taint updated
      (is (not (contains? (:taint parent) :needs-proposal-review))))))

(deftest approve-proposal-error-no-proposal-test
  (testing "throws when no active proposal"
    (create-test-mote! "1" "Root")
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"No active proposal"
         (proposal/approve-proposal! *test-repo* "1" "advisor-1")))))

(deftest approve-proposal-error-already-voted-test
  (testing "throws when agent already voted"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"already voted"
         (proposal/approve-proposal! *test-repo* "1" "advisor-1")))))

;; -----------------------------------------------------------------------------
;; reject-proposal! Tests
;; -----------------------------------------------------------------------------

(deftest reject-proposal-single-vote-test
  (testing "single reject vote - pending"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [result (proposal/reject-proposal!
                  *test-repo* "1" "advisor-1"
                  :reason "Incomplete")
          {:keys [vote-cast quorum-status archived-children]} (:result result)]
      (is (= :reject (:vote vote-cast)))
      (is (= "Incomplete" (:reason vote-cast)))
      (is (= :pending quorum-status))
      (is (nil? archived-children))
      ;; Child still in proposed/
      (is (file-exists-in? "1.1" "proposed")))))

(deftest reject-proposal-quorum-reached-test
  (testing "second reject vote reaches quorum - children archived"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step A"} {:claim "Step B"}]
     "proposer-1")
    ;; First vote
    (proposal/reject-proposal! *test-repo* "1" "advisor-1")
    ;; Second vote - quorum!
    (let [result (proposal/reject-proposal! *test-repo* "1" "advisor-2")
          {:keys [quorum-status archived-children]} (:result result)]
      (is (= :rejected quorum-status))
      (is (= ["1.1" "1.2"] archived-children))
      ;; Children moved to archive/
      (is (not (file-exists-in? "1.1" "proposed")))
      (is (not (file-exists-in? "1.2" "proposed")))
      ;; Check children are now :rejected in archive/
      (let [child1 (store/load-mote *test-repo* "1.1")
            child2 (store/load-mote *test-repo* "1.2")]
        (is (= :rejected (:status child1)))
        (is (= :rejected (:status child2)))))))

(deftest reject-proposal-updates-parent-test
  (testing "parent updated after quorum rejection"
    (create-test-mote! "1" "Root" :taint #{})
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (proposal/reject-proposal! *test-repo* "1" "advisor-1")
    (proposal/reject-proposal! *test-repo* "1" "advisor-2")
    (let [parent (store/load-mote *test-repo* "1")]
      ;; Proposal cleared
      (is (nil? (:proposal parent)))
      ;; Children NOT populated (they were rejected)
      (is (empty? (:children parent)))
      ;; Taint updated - needs new decomposition
      (is (contains? (:taint parent) :needs-decomposition))
      (is (not (contains? (:taint parent) :needs-proposal-review))))))

;; -----------------------------------------------------------------------------
;; Mixed Voting Tests
;; -----------------------------------------------------------------------------

(deftest mixed-votes-test
  (testing "mixed votes don't reach quorum"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    ;; One approve, one reject
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (let [result (proposal/reject-proposal! *test-repo* "1" "advisor-2")
          {:keys [quorum-status]} (:result result)]
      ;; Still pending
      (is (= :pending quorum-status))
      ;; Child still in proposed/
      (is (file-exists-in? "1.1" "proposed"))
      ;; Parent still has proposal
      (let [parent (store/load-mote *test-repo* "1")]
        (is (some? (:proposal parent)))))))

(deftest third-vote-breaks-tie-test
  (testing "third vote breaks tie"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    ;; One approve, one reject
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (proposal/reject-proposal! *test-repo* "1" "advisor-2")
    ;; Third vote approves
    (let [result (proposal/approve-proposal! *test-repo* "1" "advisor-3")
          {:keys [quorum-status promoted-children]} (:result result)]
      (is (= :approved quorum-status))
      (is (= ["1.1"] promoted-children)))))

;; -----------------------------------------------------------------------------
;; proposal-status Tests
;; -----------------------------------------------------------------------------

(deftest proposal-status-no-proposal-test
  (testing "status when no proposal exists"
    (create-test-mote! "1" "Root")
    (let [status (proposal/proposal-status *test-repo* "1")]
      (is (not (:has-proposal status)))
      (is (nil? (:proposal status)))
      (is (= 2 (:quorum status))))))

(deftest proposal-status-with-votes-test
  (testing "status with pending proposal"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (let [status (proposal/proposal-status *test-repo* "1")]
      (is (:has-proposal status))
      (is (= :pending (:quorum-status status)))
      (is (= 1 (:votes-for status)))
      (is (= 0 (:votes-against status)))
      (is (= 1 (:votes-needed status))))))

;; -----------------------------------------------------------------------------
;; Git Transaction Tests
;; -----------------------------------------------------------------------------

(deftest proposal-creates-commit-test
  (testing "create-proposal! creates git commit"
    (create-test-mote! "1" "Root")
    (let [result (proposal/create-proposal!
                  *test-repo* "1"
                  [{:claim "Step"}]
                  "proposer-1")]
      (is (some? (:commit result)))
      (is (string? (get-in result [:commit :sha]))))))

(deftest approve-creates-commit-test
  (testing "approve-proposal! creates git commit"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [result (proposal/approve-proposal! *test-repo* "1" "advisor-1")]
      (is (some? (:commit result))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest nested-proposal-test
  (testing "proposal on nested mote"
    ;; Create parent and child
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Child"}]
     "proposer-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-2")
    ;; Now propose on the child
    (let [result (proposal/create-proposal!
                  *test-repo* "1.1"
                  [{:claim "Grandchild A"} {:claim "Grandchild B"}]
                  "proposer-2")
          child-ids (mapv :id (:children (:result result)))]
      (is (= ["1.1.1" "1.1.2"] child-ids))
      (is (file-exists-in? "1.1.1" "proposed"))
      (is (file-exists-in? "1.1.2" "proposed")))))

(deftest quorum-one-test
  (testing "quorum of 1 approves immediately"
    ;; Create repo with quorum = 1
    (store/save-config! *test-repo* {:project-name "Test"
                                     :proposal-quorum 1})
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [result (proposal/approve-proposal! *test-repo* "1" "advisor-1")
          {:keys [quorum-status promoted-children]} (:result result)]
      (is (= :approved quorum-status))
      (is (= ["1.1"] promoted-children)))))

(deftest proposal-preserves-existing-children-test
  (testing "approval preserves existing children"
    (create-test-mote! "1" "Root")
    ;; First proposal
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Child 1"}]
     "proposer-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    (proposal/approve-proposal! *test-repo* "1" "advisor-2")
    ;; Second proposal
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Child 2"}]
     "proposer-2")
    (proposal/approve-proposal! *test-repo* "1" "advisor-3")
    (proposal/approve-proposal! *test-repo* "1" "advisor-4")
    ;; Both children should exist
    (let [parent (store/load-mote *test-repo* "1")]
      (is (= ["1.1" "1.2"] (:children parent))))))

;; -----------------------------------------------------------------------------
;; withdraw-proposal! Tests
;; -----------------------------------------------------------------------------

(deftest withdraw-proposal-basic-test
  (testing "proposer can withdraw their own proposal"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step A"} {:claim "Step B"}]
     "proposer-1")
    (let [result (proposal/withdraw-proposal! *test-repo* "1" "proposer-1")
          {:keys [withdrawn-children]} (:result result)]
      (is (= ["1.1" "1.2"] withdrawn-children))
      ;; Children no longer in proposed
      (is (not (file-exists-in? "1.1" "proposed")))
      (is (not (file-exists-in? "1.2" "proposed")))
      ;; Children are now in archive with :rejected status
      (let [child1 (store/load-mote *test-repo* "1.1")
            child2 (store/load-mote *test-repo* "1.2")]
        (is (= :rejected (:status child1)))
        (is (= :rejected (:status child2)))))))

(deftest withdraw-proposal-updates-parent-test
  (testing "parent updated after withdrawal"
    (create-test-mote! "1" "Root" :taint #{})
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    ;; Verify parent has :needs-proposal-review
    (let [parent-before (store/load-mote *test-repo* "1")]
      (is (contains? (:taint parent-before) :needs-proposal-review)))
    ;; Withdraw
    (proposal/withdraw-proposal! *test-repo* "1" "proposer-1")
    (let [parent (store/load-mote *test-repo* "1")]
      ;; Proposal cleared
      (is (nil? (:proposal parent)))
      ;; Taint updated - needs new decomposition
      (is (contains? (:taint parent) :needs-decomposition))
      (is (not (contains? (:taint parent) :needs-proposal-review))))))

(deftest withdraw-proposal-after-votes-test
  (testing "proposer can withdraw even after votes (but before quorum)"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    ;; Add one vote (not yet at quorum)
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    ;; Proposer withdraws
    (let [result (proposal/withdraw-proposal! *test-repo* "1" "proposer-1")
          {:keys [withdrawn-children]} (:result result)]
      (is (= ["1.1"] withdrawn-children))
      ;; Child archived with rejected status
      (let [child (store/load-mote *test-repo* "1.1")]
        (is (= :rejected (:status child)))))))

(deftest withdraw-proposal-error-not-proposer-test
  (testing "throws when non-proposer tries to withdraw"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Only the proposer can withdraw"
         (proposal/withdraw-proposal! *test-repo* "1" "other-agent")))))

(deftest withdraw-proposal-error-no-proposal-test
  (testing "throws when no active proposal"
    (create-test-mote! "1" "Root")
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"No active proposal"
         (proposal/withdraw-proposal! *test-repo* "1" "agent-1")))))

(deftest withdraw-proposal-error-not-pending-test
  (testing "throws when proposal already approved"
    (create-test-mote! "1" "Root")
    ;; Set quorum to 1 for quick approval
    (store/save-config! *test-repo* {:project-name "Test"
                                     :proposal-quorum 1})
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    ;; Approve it (quorum=1 means it's approved immediately)
    (proposal/approve-proposal! *test-repo* "1" "advisor-1")
    ;; Now trying to withdraw should fail
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"(No active proposal|Proposal is not pending)"
         (proposal/withdraw-proposal! *test-repo* "1" "proposer-1")))))

(deftest withdraw-proposal-error-parent-not-found-test
  (testing "throws when parent not found"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Parent mote not found"
         (proposal/withdraw-proposal! *test-repo* "nonexistent" "agent-1")))))

(deftest withdraw-proposal-creates-commit-test
  (testing "withdraw-proposal! creates git commit"
    (create-test-mote! "1" "Root")
    (proposal/create-proposal!
     *test-repo* "1"
     [{:claim "Step"}]
     "proposer-1")
    (let [result (proposal/withdraw-proposal! *test-repo* "1" "proposer-1")]
      (is (some? (:commit result)))
      (is (string? (get-in result [:commit :sha]))))))
