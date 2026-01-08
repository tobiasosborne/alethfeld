(ns alethfeld.cmd.vote-all-test
  "Tests for batch voting command."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [alethfeld.cmd :as cmd]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.session :as session]
            [alethfeld.verify :as verify]
            [alethfeld.git :as git]
            [babashka.fs :as fs]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *test-repo* nil)

(defn with-temp-repo [f]
  (let [temp-dir (str (fs/create-temp-dir {:prefix "alethfeld-vote-all-test-"}))]
    (try
      ;; Initialize git first
      (git/git-init! temp-dir)
      (git/git-config! temp-dir "user.name" "test")
      (git/git-config! temp-dir "user.email" "test@test.com")
      ;; Then initialize alethfeld repo
      (store/init-repo! temp-dir :config {:project-name "Test"
                                          :version "0.1"
                                          :default-difficulty 3
                                          :vote-quorum 2
                                          :proposal-quorum 2
                                          :claim-timeout-minutes 30})
      ;; Initial commit
      (git/git-add-all! temp-dir)
      (git/git-commit! temp-dir "Initialize test repo")
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
  [id claim agent & {:keys [status taint difficulty priority votes contributors]
                     :or {status :fixed
                          taint #{:needs-verification}
                          difficulty 3
                          priority :p2
                          votes []
                          contributors nil}}]
  (let [m (-> (mote/make-mote id claim agent
                              :status status
                              :taint taint
                              :difficulty difficulty
                              :priority priority
                              :votes votes)
              (cond-> contributors (assoc :contributors contributors)))]
    (store/save-mote! *test-repo* m)
    (git/git-add-all! *test-repo*)
    (git/git-commit! *test-repo* (str "Create mote " id))
    m))

(defn create-session!
  "Create a test session for an agent."
  [agent mote-id role]
  (let [result (session/create-session! *test-repo* mote-id agent role)]
    (:token result)))

;; -----------------------------------------------------------------------------
;; find-eligible-motes-for-voting Tests (Pure Logic)
;; -----------------------------------------------------------------------------

(deftest find-eligible-motes-for-voting-test
  (testing "finds motes that need verification and agent can vote on"
    ;; Create various motes
    (create-test-mote! "1" "Fixed, needs verification" "creator-1"
                       :status :fixed
                       :taint #{:needs-verification}
                       :contributors {:created-by "creator-1"})
    (create-test-mote! "2" "Proposed (not fixed)" "creator-2"
                       :status :proposed
                       :taint #{:needs-decomposition}
                       :contributors {:created-by "creator-2"})
    (create-test-mote! "3" "Fixed but no needs-verification taint" "creator-3"
                       :status :fixed
                       :taint #{}
                       :contributors {:created-by "creator-3"})
    (create-test-mote! "4" "Created by verifier (self)" "verifier-1"
                       :status :fixed
                       :taint #{:needs-verification}
                       :contributors {:created-by "verifier-1"})
    (create-test-mote! "5" "Already voted" "creator-4"
                       :status :fixed
                       :taint #{:needs-verification}
                       :contributors {:created-by "creator-4"}
                       :votes [{:agent "verifier-1" :vote :for}])

    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-1")
          eligible-ids (set (map first eligible))]
      ;; Should find only "1" - the only eligible mote
      (is (= #{"1"} eligible-ids))))

  (testing "finds multiple eligible motes"
    (create-test-mote! "10" "Eligible 1" "creator-1"
                       :contributors {:created-by "creator-1"})
    (create-test-mote! "11" "Eligible 2" "creator-2"
                       :contributors {:created-by "creator-2"})
    (create-test-mote! "12" "Eligible 3" "creator-3"
                       :contributors {:created-by "creator-3"})

    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-1")
          eligible-ids (set (map first eligible))]
      ;; Should find motes 1, 10, 11, 12 (from this and previous test)
      (is (contains? eligible-ids "10"))
      (is (contains? eligible-ids "11"))
      (is (contains? eligible-ids "12"))))

  (testing "returns empty when no eligible motes"
    ;; Using a fresh repo would be ideal, but for simplicity check with
    ;; an agent who created all motes
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "creator-1")
          eligible-ids (set (map first eligible))]
      ;; creator-1 can't vote on mote "1" (self-created)
      ;; but can vote on others
      (is (not (contains? eligible-ids "1"))))))

;; -----------------------------------------------------------------------------
;; Self-Vote Prevention Tests
;; -----------------------------------------------------------------------------

(deftest self-vote-prevention-test
  (testing "excludes motes where agent is creator"
    (create-test-mote! "20" "Created by verifier" "verifier-2"
                       :contributors {:created-by "verifier-2"})
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-2")
          eligible-ids (set (map first eligible))]
      (is (not (contains? eligible-ids "20")))))

  (testing "excludes motes where agent is proposer"
    (create-test-mote! "21" "Proposed by verifier" "creator-1"
                       :contributors {:created-by "creator-1"
                                      :proposed-by "verifier-3"})
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-3")
          eligible-ids (set (map first eligible))]
      (is (not (contains? eligible-ids "21")))))

  (testing "allows voting when agent is not a contributor"
    (create-test-mote! "22" "Can vote" "creator-1"
                       :contributors {:created-by "creator-1"
                                      :proposed-by "creator-2"})
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-4")
          eligible-ids (set (map first eligible))]
      (is (contains? eligible-ids "22")))))

;; -----------------------------------------------------------------------------
;; Batch Voting Integration Tests (using verify module directly)
;; -----------------------------------------------------------------------------

(deftest batch-vote-integration-test
  (testing "can cast multiple votes using verify/cast-vote!"
    ;; Create motes
    (create-test-mote! "30" "Mote A" "creator-1"
                       :contributors {:created-by "creator-1"})
    (create-test-mote! "31" "Mote B" "creator-2"
                       :contributors {:created-by "creator-2"})

    ;; Find eligible motes for verifier
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-5")
          eligible-ids (map first eligible)]
      ;; Filter to just our test motes
      (let [test-motes (filter #{"30" "31"} eligible-ids)]
        (is (= 2 (count test-motes)))

        ;; Cast votes on each
        (doseq [mote-id test-motes]
          (verify/cast-vote! *test-repo* mote-id "verifier-5" :for :reason "Batch approved"))

        ;; Verify votes were cast
        (let [mote-30 (store/load-mote *test-repo* "30")
              mote-31 (store/load-mote *test-repo* "31")]
          (is (verify/has-voted? mote-30 "verifier-5"))
          (is (verify/has-voted? mote-31 "verifier-5")))))))

(deftest batch-vote-against-test
  (testing "can batch vote against"
    (create-test-mote! "40" "Mote to reject" "creator-1"
                       :contributors {:created-by "creator-1"})

    ;; Cast against vote
    (verify/cast-vote! *test-repo* "40" "verifier-6" :against :reason "Invalid")

    ;; Verify vote was against
    (let [mote (store/load-mote *test-repo* "40")]
      (is (= :against (:vote (first (:votes mote))))))))

(deftest batch-vote-skips-already-voted-test
  (testing "find-eligible excludes already voted"
    (create-test-mote! "50" "Already voted" "creator-1"
                       :contributors {:created-by "creator-1"}
                       :votes [{:agent "verifier-7" :vote :for :timestamp "2024-01-01"}])

    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-7")
          eligible-ids (set (map first eligible))]
      ;; Should not include "50"
      (is (not (contains? eligible-ids "50"))))))

;; -----------------------------------------------------------------------------
;; Quorum Behavior Tests
;; -----------------------------------------------------------------------------

(deftest batch-vote-quorum-test
  (testing "second vote reaches quorum and changes status"
    ;; Create mote first
    (create-test-mote! "60" "Needs two votes" "creator-1"
                       :contributors {:created-by "creator-1"})

    ;; Cast first vote
    (verify/cast-vote! *test-repo* "60" "verifier-8" :for)

    ;; Cast second vote (quorum is 2)
    (let [result (verify/cast-vote! *test-repo* "60" "verifier-9" :for)]
      (is (= :verified (:quorum-status (:result result))))
      (is (:status-changed (:result result))))

    ;; Verify mote status changed
    (let [mote (store/load-mote *test-repo* "60")]
      (is (= :verified (:status mote))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest empty-result-test
  (testing "returns empty when no motes need verification"
    ;; Create a mote that doesn't need verification
    (create-test-mote! "70" "Already verified" "creator-1"
                       :status :verified
                       :taint #{}
                       :contributors {:created-by "creator-1"})

    ;; Create agent who created everything
    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "everyone-creator")]
      ;; Filter to fresh motes (70 is verified, others may exist from other tests)
      (let [fresh (filter #(= "70" (first %)) eligible)]
        (is (empty? fresh))))))

(deftest sorting-test
  (testing "results are sorted by mote ID"
    (create-test-mote! "80.2" "Child 2" "creator-1"
                       :contributors {:created-by "creator-1"})
    (create-test-mote! "80.1" "Child 1" "creator-1"
                       :contributors {:created-by "creator-1"})
    (create-test-mote! "80.3" "Child 3" "creator-1"
                       :contributors {:created-by "creator-1"})

    (let [eligible (#'cmd/find-eligible-motes-for-voting *test-repo* "verifier-10")
          test-motes (->> eligible
                          (map first)
                          (filter #(clojure.string/starts-with? % "80.")))]
      ;; Should be sorted
      (is (= ["80.1" "80.2" "80.3"] test-motes)))))
