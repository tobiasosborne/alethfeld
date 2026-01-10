(ns alethfeld.verify-test
  "Tests for verification workflow."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [alethfeld.verify :as verify]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
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
  [id claim & {:keys [status taint difficulty priority votes]
               :or {status :fixed
                    taint #{:needs-verification}
                    difficulty 3
                    priority :p2
                    votes []}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :status status
                          :taint taint
                          :difficulty difficulty
                          :priority priority
                          :votes votes)]
    (store/save-mote! *test-repo* m)
    m))

;; -----------------------------------------------------------------------------
;; Pure Function Tests
;; -----------------------------------------------------------------------------

(deftest count-votes-by-type-test
  (testing "empty votes"
    (let [entity {:id "1" :votes []}]
      (is (= {:yes 0 :no 0} (verify/count-votes-by-type entity :yes :no)))))

  (testing "positive votes only"
    (let [entity {:id "1"
                  :votes [{:agent "v1" :vote :yes}
                          {:agent "v2" :vote :yes}]}]
      (is (= {:yes 2 :no 0} (verify/count-votes-by-type entity :yes :no)))))

  (testing "negative votes only"
    (let [entity {:id "1"
                  :votes [{:agent "v1" :vote :no}]}]
      (is (= {:yes 0 :no 1} (verify/count-votes-by-type entity :yes :no)))))

  (testing "mixed votes"
    (let [entity {:id "1"
                  :votes [{:agent "v1" :vote :yes}
                          {:agent "v2" :vote :no}
                          {:agent "v3" :vote :yes}]}]
      (is (= {:yes 2 :no 1} (verify/count-votes-by-type entity :yes :no)))))

  (testing "works with different key names"
    (let [entity {:id "1"
                  :votes [{:agent "v1" :vote :approve}
                          {:agent "v2" :vote :reject}]}]
      (is (= {:approve 1 :reject 1} (verify/count-votes-by-type entity :approve :reject)))))

  (testing "nil votes treated as empty"
    (let [entity {:id "1"}]
      (is (= {:a 0 :b 0} (verify/count-votes-by-type entity :a :b))))))

(deftest count-verification-votes-test
  (testing "empty votes"
    (let [m {:id "1" :votes []}]
      (is (= {:for 0 :against 0} (verify/count-verification-votes m)))))

  (testing "for votes only"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :for}]}]
      (is (= {:for 2 :against 0} (verify/count-verification-votes m)))))

  (testing "against votes only"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :against}]}]
      (is (= {:for 0 :against 1} (verify/count-verification-votes m)))))

  (testing "mixed votes"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :against}
                     {:agent "v3" :vote :for}]}]
      (is (= {:for 2 :against 1} (verify/count-verification-votes m))))))

(deftest check-verification-quorum-test
  (testing "pending with no votes"
    (let [m {:id "1" :votes []}]
      (is (= :pending (verify/check-verification-quorum m 2)))))

  (testing "pending with one vote"
    (let [m {:id "1" :votes [{:agent "v1" :vote :for}]}]
      (is (= :pending (verify/check-verification-quorum m 2)))))

  (testing "verified - unanimous for at quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :for}]}]
      (is (= :verified (verify/check-verification-quorum m 2)))))

  (testing "verified - unanimous for above quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :for}
                     {:agent "v3" :vote :for}]}]
      (is (= :verified (verify/check-verification-quorum m 2)))))

  (testing "refuted - unanimous against at quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :against}
                     {:agent "v2" :vote :against}]}]
      (is (= :refuted (verify/check-verification-quorum m 2)))))

  (testing "refuted - unanimous against above quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :against}
                     {:agent "v2" :vote :against}
                     {:agent "v3" :vote :against}]}]
      (is (= :refuted (verify/check-verification-quorum m 2)))))

  (testing "contested - mixed votes at quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :against}]}]
      (is (= :contested (verify/check-verification-quorum m 2)))))

  (testing "contested - mixed votes above quorum"
    (let [m {:id "1"
             :votes [{:agent "v1" :vote :for}
                     {:agent "v2" :vote :against}
                     {:agent "v3" :vote :for}]}]
      (is (= :contested (verify/check-verification-quorum m 2)))))

  (testing "quorum of 1 - single for vote"
    (let [m {:id "1" :votes [{:agent "v1" :vote :for}]}]
      (is (= :verified (verify/check-verification-quorum m 1)))))

  (testing "quorum of 1 - single against vote"
    (let [m {:id "1" :votes [{:agent "v1" :vote :against}]}]
      (is (= :refuted (verify/check-verification-quorum m 1))))))

(deftest has-voted-test
  (testing "agent has not voted"
    (let [m {:id "1" :votes [{:agent "other" :vote :for}]}]
      (is (not (verify/has-voted? m "agent1")))))

  (testing "agent has voted"
    (let [m {:id "1" :votes [{:agent "agent1" :vote :for}]}]
      (is (verify/has-voted? m "agent1"))))

  (testing "empty votes"
    (let [m {:id "1" :votes []}]
      (is (not (verify/has-voted? m "agent1"))))))

(deftest needs-verification-test
  (testing "needs verification - fixed with taint"
    (let [m {:id "1" :status :fixed :taint #{:needs-verification}}]
      (is (verify/needs-verification? m))))

  (testing "no verification needed - wrong status"
    (let [m {:id "1" :status :verified :taint #{:needs-verification}}]
      (is (not (verify/needs-verification? m)))))

  (testing "no verification needed - no taint"
    (let [m {:id "1" :status :fixed :taint #{}}]
      (is (not (verify/needs-verification? m)))))

  (testing "no verification needed - proposed status"
    (let [m {:id "1" :status :proposed :taint #{:needs-verification}}]
      (is (not (verify/needs-verification? m))))))

;; -----------------------------------------------------------------------------
;; cast-vote! Tests
;; -----------------------------------------------------------------------------

(deftest cast-vote-single-for-test
  (testing "single for vote - pending"
    (create-test-mote! "1" "Test claim")
    (let [result (verify/cast-vote!
                  *test-repo* "1" "verifier-1" :for
                  :reason "Proof looks correct")
          {:keys [vote-cast quorum-status status-changed new-status]} (:result result)]
      ;; Vote was cast
      (is (= :for (:vote vote-cast)))
      (is (= "verifier-1" (:agent vote-cast)))
      (is (= "Proof looks correct" (:reason vote-cast)))
      ;; Not at quorum yet
      (is (= :pending quorum-status))
      (is (not status-changed))
      (is (= :fixed new-status))
      ;; Check mote state
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :fixed (:status m)))
        (is (= 1 (count (:votes m))))
        (is (contains? (:taint m) :needs-votes))))))

(deftest cast-vote-single-against-test
  (testing "single against vote - pending"
    (create-test-mote! "1" "Test claim")
    (let [result (verify/cast-vote!
                  *test-repo* "1" "verifier-1" :against
                  :reason "Found a gap")
          {:keys [vote-cast quorum-status]} (:result result)]
      (is (= :against (:vote vote-cast)))
      (is (= "Found a gap" (:reason vote-cast)))
      (is (= :pending quorum-status)))))

(deftest cast-vote-verified-test
  (testing "second for vote reaches quorum - verified"
    (create-test-mote! "1" "Test claim")
    ;; First vote
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    ;; Second vote - quorum!
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
          {:keys [quorum-status status-changed new-status]} (:result result)]
      (is (= :verified quorum-status))
      (is status-changed)
      (is (= :verified new-status))
      ;; Check mote state
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :verified (:status m)))
        (is (= 2 (count (:votes m))))
        (is (not (contains? (:taint m) :needs-verification)))
        (is (not (contains? (:taint m) :needs-votes)))))))

(deftest cast-vote-refuted-test
  (testing "second against vote reaches quorum - refuted"
    (create-test-mote! "1" "Test claim")
    ;; First vote
    (verify/cast-vote! *test-repo* "1" "verifier-1" :against)
    ;; Second vote - quorum!
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
          {:keys [quorum-status status-changed new-status]} (:result result)]
      (is (= :refuted quorum-status))
      (is status-changed)
      (is (= :refuted new-status))
      ;; Check mote state
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :refuted (:status m)))
        (is (= 2 (count (:votes m))))
        (is (not (contains? (:taint m) :needs-verification)))
        (is (not (contains? (:taint m) :needs-votes)))))))

(deftest cast-vote-contested-test
  (testing "mixed votes at quorum - contested"
    (create-test-mote! "1" "Test claim")
    ;; For vote
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    ;; Against vote - quorum reached with mixed votes
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
          {:keys [quorum-status status-changed new-status]} (:result result)]
      (is (= :contested quorum-status))
      (is status-changed)
      (is (= :contested new-status))
      ;; Check mote state
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :contested (:status m)))
        (is (= 2 (count (:votes m))))
        (is (not (contains? (:taint m) :needs-verification)))
        (is (contains? (:taint m) :needs-votes))))))

(deftest cast-vote-error-not-found-test
  (testing "throws when mote not found"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Mote not found"
         (verify/cast-vote! *test-repo* "nonexistent" "verifier-1" :for)))))

(deftest cast-vote-error-wrong-status-test
  (testing "throws when mote is not fixed"
    (create-test-mote! "1" "Test claim" :status :proposed)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Can only vote on fixed motes"
         (verify/cast-vote! *test-repo* "1" "verifier-1" :for))))

  (testing "throws when mote is already verified"
    (create-test-mote! "1" "Verified claim" :status :verified)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Can only vote on fixed motes"
         (verify/cast-vote! *test-repo* "1" "verifier-1" :for)))))

(deftest cast-vote-error-already-voted-test
  (testing "throws when agent already voted"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"already voted"
         (verify/cast-vote! *test-repo* "1" "verifier-1" :against)))))

;; -----------------------------------------------------------------------------
;; Taint Management Tests
;; -----------------------------------------------------------------------------

(deftest taint-updated-on-pending-test
  (testing "pending vote adds needs-votes taint"
    (create-test-mote! "1" "Test claim" :taint #{:needs-verification})
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (contains? (:taint m) :needs-votes))
      (is (contains? (:taint m) :needs-verification)))))

(deftest taint-updated-on-verified-test
  (testing "verified removes needs-verification and needs-votes"
    (create-test-mote! "1" "Test claim" :taint #{:needs-verification :needs-votes})
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (not (contains? (:taint m) :needs-verification)))
      (is (not (contains? (:taint m) :needs-votes))))))

(deftest taint-updated-on-refuted-test
  (testing "refuted removes needs-verification and needs-votes"
    (create-test-mote! "1" "Test claim" :taint #{:needs-verification :needs-votes})
    (verify/cast-vote! *test-repo* "1" "verifier-1" :against)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
    (let [m (store/load-mote *test-repo* "1")]
      (is (not (contains? (:taint m) :needs-verification)))
      (is (not (contains? (:taint m) :needs-votes))))))

(deftest taint-updated-on-contested-test
  (testing "contested removes needs-verification but keeps needs-votes"
    (create-test-mote! "1" "Test claim" :taint #{:needs-verification})
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
    (let [m (store/load-mote *test-repo* "1")]
      (is (not (contains? (:taint m) :needs-verification)))
      (is (contains? (:taint m) :needs-votes)))))

;; -----------------------------------------------------------------------------
;; verification-status Tests
;; -----------------------------------------------------------------------------

(deftest verification-status-no-mote-test
  (testing "status when mote doesn't exist"
    (let [status (verify/verification-status *test-repo* "nonexistent")]
      (is (nil? (:status status)))
      (is (= 2 (:quorum status)))
      (is (nil? (:quorum-status status))))))

(deftest verification-status-no-votes-test
  (testing "status with no votes"
    (create-test-mote! "1" "Test claim")
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :fixed (:status status)))
      (is (= 2 (:quorum status)))
      (is (= :pending (:quorum-status status)))
      (is (= 0 (:votes-for status)))
      (is (= 0 (:votes-against status)))
      (is (= 2 (:votes-needed status))))))

(deftest verification-status-with-votes-test
  (testing "status with pending votes"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :fixed (:status status)))
      (is (= :pending (:quorum-status status)))
      (is (= 1 (:votes-for status)))
      (is (= 0 (:votes-against status)))
      (is (= 1 (:votes-needed status))))))

(deftest verification-status-after-quorum-test
  (testing "status after verification complete"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :verified (:status status)))
      (is (= :verified (:quorum-status status)))
      (is (= 2 (:votes-for status)))
      (is (= 0 (:votes-against status)))
      (is (= 0 (:votes-needed status))))))

;; -----------------------------------------------------------------------------
;; Git Transaction Tests
;; -----------------------------------------------------------------------------

(deftest cast-vote-creates-commit-test
  (testing "cast-vote! creates git commit"
    (create-test-mote! "1" "Test claim")
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-1" :for)]
      (is (some? (:commit result)))
      (is (string? (get-in result [:commit :sha]))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest quorum-of-one-test
  (testing "quorum of 1 verifies immediately"
    ;; Create repo with quorum = 1
    (store/save-config! *test-repo* {:project-name "Test"
                                     :vote-quorum 1})
    (create-test-mote! "1" "Test claim")
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
          {:keys [quorum-status new-status]} (:result result)]
      (is (= :verified quorum-status))
      (is (= :verified new-status)))))

(deftest multiple-agents-voting-test
  (testing "multiple agents can vote (up to quorum)"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= 2 (count (:votes m))))
      (is (= :verified (:status m))))))

(deftest vote-without-reason-test
  (testing "vote can be cast without reason"
    (create-test-mote! "1" "Test claim")
    (let [result (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
          vote-cast (:vote-cast (:result result))]
      (is (nil? (:reason vote-cast))))))

(deftest contested-needs-arbitration-test
  (testing "contested mote keeps needs-votes for arbitration"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
    (let [m (store/load-mote *test-repo* "1")]
      ;; Status is contested
      (is (= :contested (:status m)))
      ;; Still needs votes to resolve
      (is (contains? (:taint m) :needs-votes)))))

(deftest third-vote-after-contested-test
  (testing "third vote on contested mote"
    ;; This test checks that we can't vote on contested motes
    ;; (since only :fixed status allows voting)
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :against)
    ;; Now status is :contested, can't vote anymore
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Can only vote on fixed motes"
         (verify/cast-vote! *test-repo* "1" "verifier-3" :for)))))

(deftest preserves-other-taints-test
  (testing "verification preserves unrelated taints"
    (create-test-mote! "1" "Test claim"
                       :taint #{:needs-verification :needs-refinement})
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :verified (:status m)))
      ;; Refinement taint should still be there
      (is (contains? (:taint m) :needs-refinement))
      ;; Verification taint should be removed
      (is (not (contains? (:taint m) :needs-verification))))))

;; -----------------------------------------------------------------------------
;; Dependency Verification Tests
;; -----------------------------------------------------------------------------

(deftest unverified-dependencies-test
  (testing "mote without dependencies returns empty"
    (create-test-mote! "1" "No dependencies")
    (let [m (store/load-mote *test-repo* "1")]
      (is (empty? (verify/unverified-dependencies *test-repo* m)))))

  (testing "mote with verified dependency returns empty"
    (create-test-mote! "1" "Dependency" :status :verified)
    (let [m2 (mote/make-mote "2" "Depends on 1" "test-agent"
                             :status :fixed
                             :depends-on [{:ref "1"}])]
      (store/save-mote! *test-repo* m2)
      (is (empty? (verify/unverified-dependencies *test-repo* m2)))))

  (testing "mote with unverified dependency returns it"
    (create-test-mote! "1" "Not verified yet" :status :fixed)
    (let [m2 (mote/make-mote "2" "Depends on 1" "test-agent"
                             :status :fixed
                             :depends-on [{:ref "1"}])]
      (store/save-mote! *test-repo* m2)
      (is (= ["1"] (verify/unverified-dependencies *test-repo* m2)))))

  (testing "returns all unverified dependencies"
    (create-test-mote! "1" "Verified" :status :verified)
    (create-test-mote! "2" "Fixed" :status :fixed)
    (create-test-mote! "3" "Proposed" :status :proposed)
    (let [m4 (mote/make-mote "4" "Depends on all" "test-agent"
                             :status :fixed
                             :depends-on [{:ref "1"} {:ref "2"} {:ref "3"}])]
      (store/save-mote! *test-repo* m4)
      (let [unverified (verify/unverified-dependencies *test-repo* m4)]
        (is (= 2 (count unverified)))
        (is (some #{"2"} unverified))
        (is (some #{"3"} unverified))))))

(deftest vote-blocked-by-unverified-dependencies-test
  (testing "cannot vote when dependency is not verified"
    (create-test-mote! "1" "Dependency" :status :fixed)
    (let [m2 (mote/make-mote "2" "Depends on 1" "test-agent"
                             :status :fixed
                             :taint #{:needs-verification}
                             :depends-on [{:ref "1"}])]
      (store/save-mote! *test-repo* m2)
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"unverified dependencies"
           (verify/cast-vote! *test-repo* "2" "verifier-1" :for)))))

  (testing "can vote after dependency is verified"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    ;; First, verify the dependency
    (create-test-mote! "1" "Dependency" :status :verified)
    ;; Then the dependent mote can be voted on
    (let [m2 (mote/make-mote "2" "Depends on 1" "test-agent"
                             :status :fixed
                             :taint #{:needs-verification}
                             :depends-on [{:ref "1"}])]
      (store/save-mote! *test-repo* m2)
      (let [result (verify/cast-vote! *test-repo* "2" "verifier-1" :for)]
        (is (= :verified (:quorum-status (:result result))))))))

(deftest vote-blocked-error-details-test
  (testing "error includes list of unverified dependencies"
    (create-test-mote! "10" "Dep 1" :status :fixed)
    (create-test-mote! "11" "Dep 2" :status :fixed)
    (let [m (mote/make-mote "12" "Depends on both" "test-agent"
                            :status :fixed
                            :taint #{:needs-verification}
                            :depends-on [{:ref "10"} {:ref "11"}])]
      (store/save-mote! *test-repo* m)
      (try
        (verify/cast-vote! *test-repo* "12" "verifier-1" :for)
        (is false "Should have thrown")
        (catch clojure.lang.ExceptionInfo e
          (let [data (ex-data e)]
            (is (= :unverified-dependencies (:type data)))
            (is (= "12" (:mote-id data)))
            (is (= 2 (count (:unverified-deps data))))))))))

;; -----------------------------------------------------------------------------
;; Full Verification Workflow Tests
;; -----------------------------------------------------------------------------

(deftest full-workflow-single-mote-test
  (testing "complete workflow: fixed -> verified with two verifiers"
    ;; Create a fixed mote needing verification
    (create-test-mote! "1" "Claim to verify"
                       :status :fixed
                       :taint #{:needs-verification})
    ;; Initial state
    (let [m0 (store/load-mote *test-repo* "1")]
      (is (= :fixed (:status m0)))
      (is (contains? (:taint m0) :needs-verification))
      (is (empty? (:votes m0))))
    ;; First verifier casts vote
    (verify/cast-vote! *test-repo* "1" "alice" :for :reason "Looks correct")
    (let [m1 (store/load-mote *test-repo* "1")]
      (is (= :fixed (:status m1)) "Status should still be fixed")
      (is (= 1 (count (:votes m1))))
      (is (contains? (:taint m1) :needs-votes) "Should have needs-votes taint"))
    ;; Second verifier casts vote - reaches quorum
    (verify/cast-vote! *test-repo* "1" "bob" :for :reason "Verified independently")
    (let [m2 (store/load-mote *test-repo* "1")]
      (is (= :verified (:status m2)) "Status should now be verified")
      (is (= 2 (count (:votes m2))))
      (is (not (contains? (:taint m2) :needs-verification)))
      (is (not (contains? (:taint m2) :needs-votes))))))

(deftest full-workflow-refutation-test
  (testing "complete workflow: fixed -> refuted with two verifiers"
    (create-test-mote! "1" "Flawed claim"
                       :status :fixed
                       :taint #{:needs-verification})
    ;; Two against votes reach refutation
    (verify/cast-vote! *test-repo* "1" "alice" :against :reason "Found error in line 3")
    (verify/cast-vote! *test-repo* "1" "bob" :against :reason "Same issue confirmed")
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :refuted (:status m)))
      (is (not (contains? (:taint m) :needs-verification))))))

(deftest full-workflow-contested-resolution-test
  (testing "workflow: fixed -> contested (mixed votes at quorum)"
    (create-test-mote! "1" "Controversial claim"
                       :status :fixed
                       :taint #{:needs-verification})
    (verify/cast-vote! *test-repo* "1" "alice" :for :reason "Valid")
    (verify/cast-vote! *test-repo* "1" "bob" :against :reason "Invalid")
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :contested (:status m)) "Mixed votes should lead to contested")
      (is (contains? (:taint m) :needs-votes) "Contested needs more votes"))))

;; -----------------------------------------------------------------------------
;; Extended Quorum Tests
;; -----------------------------------------------------------------------------

(deftest quorum-three-verifiers-test
  (testing "quorum of 3 requires three matching votes"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 3})
    (create-test-mote! "1" "High stakes claim")
    ;; Two votes not enough
    (verify/cast-vote! *test-repo* "1" "alice" :for)
    (verify/cast-vote! *test-repo* "1" "bob" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :fixed (:status m)) "Still pending with 2/3 votes"))
    ;; Third vote reaches quorum
    (verify/cast-vote! *test-repo* "1" "charlie" :for)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :verified (:status m)) "Verified with 3/3 votes"))))

(deftest quorum-three-mixed-test
  (testing "quorum of 3 with mixed votes goes contested"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 3})
    (create-test-mote! "1" "Debatable claim")
    (verify/cast-vote! *test-repo* "1" "alice" :for)
    (verify/cast-vote! *test-repo* "1" "bob" :for)
    (verify/cast-vote! *test-repo* "1" "charlie" :against)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :contested (:status m)) "Mixed 2-1 vote at quorum is contested"))))

(deftest quorum-three-refuted-test
  (testing "quorum of 3 unanimous against"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 3})
    (create-test-mote! "1" "Bad claim")
    (verify/cast-vote! *test-repo* "1" "alice" :against)
    (verify/cast-vote! *test-repo* "1" "bob" :against)
    (verify/cast-vote! *test-repo* "1" "charlie" :against)
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :refuted (:status m)) "Unanimous against is refuted"))))

(deftest quorum-exact-boundary-test
  (testing "quorum status changes exactly at boundary"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 2})
    (create-test-mote! "1" "Test claim")
    ;; Before quorum
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :pending (:quorum-status status)))
      (is (= 2 (:votes-needed status))))
    ;; One vote
    (verify/cast-vote! *test-repo* "1" "alice" :for)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :pending (:quorum-status status)))
      (is (= 1 (:votes-needed status))))
    ;; At quorum
    (verify/cast-vote! *test-repo* "1" "bob" :for)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :verified (:quorum-status status)))
      (is (= 0 (:votes-needed status))))))

;; -----------------------------------------------------------------------------
;; Transitive Dependency Tests
;; -----------------------------------------------------------------------------

(deftest transitive-dependencies-test
  (testing "transitive dependency chain must all be verified"
    ;; 100 -> 101 -> 102 (102 depends on 101, 101 depends on 100)
    (create-test-mote! "100" "Base claim" :status :fixed)
    (let [mote-b (mote/make-mote "101" "Builds on 100" "test-agent"
                                 :status :fixed
                                 :taint #{:needs-verification}
                                 :depends-on [{:ref "100"}])]
      (store/save-mote! *test-repo* mote-b))
    (let [mote-c (mote/make-mote "102" "Builds on 101" "test-agent"
                                 :status :fixed
                                 :taint #{:needs-verification}
                                 :depends-on [{:ref "101"}])]
      (store/save-mote! *test-repo* mote-c))
    ;; Cannot vote on 102 because 101 is not verified
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"unverified dependencies"
         (verify/cast-vote! *test-repo* "102" "verifier-1" :for)))
    ;; Cannot vote on 101 because 100 is not verified
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"unverified dependencies"
         (verify/cast-vote! *test-repo* "101" "verifier-1" :for)))))

(deftest dependency-chain-verification-order-test
  (testing "verify dependency chain in correct order"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    ;; 100 -> 101 -> 102 (102 depends on 101, 101 depends on 100)
    (create-test-mote! "100" "Base claim" :status :fixed :taint #{:needs-verification})
    (let [mote-b (mote/make-mote "101" "Builds on 100" "test-agent"
                                 :status :fixed
                                 :taint #{:needs-verification}
                                 :depends-on [{:ref "100"}])]
      (store/save-mote! *test-repo* mote-b))
    (let [mote-c (mote/make-mote "102" "Builds on 101" "test-agent"
                                 :status :fixed
                                 :taint #{:needs-verification}
                                 :depends-on [{:ref "101"}])]
      (store/save-mote! *test-repo* mote-c))
    ;; Verify 100 first
    (verify/cast-vote! *test-repo* "100" "verifier-1" :for)
    (is (= :verified (:status (store/load-mote *test-repo* "100"))))
    ;; Now 101 can be verified
    (verify/cast-vote! *test-repo* "101" "verifier-1" :for)
    (is (= :verified (:status (store/load-mote *test-repo* "101"))))
    ;; Now 102 can be verified
    (verify/cast-vote! *test-repo* "102" "verifier-1" :for)
    (is (= :verified (:status (store/load-mote *test-repo* "102"))))))

(deftest multiple-dependencies-all-must-verify-test
  (testing "mote with multiple dependencies requires all verified"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    ;; Create two independent dependencies (using numeric IDs)
    (create-test-mote! "200" "First dependency" :status :verified)
    (create-test-mote! "201" "Second dependency" :status :fixed)
    (let [m (mote/make-mote "202" "Depends on both" "test-agent"
                            :status :fixed
                            :taint #{:needs-verification}
                            :depends-on [{:ref "200"} {:ref "201"}])]
      (store/save-mote! *test-repo* m))
    ;; Cannot vote because 201 not verified
    (let [unverified (verify/unverified-dependencies *test-repo*
                                                     (store/load-mote *test-repo* "202"))]
      (is (= ["201"] unverified)))
    ;; Verify 201
    (verify/cast-vote! *test-repo* "201" "verifier-1" :for)
    ;; Now 202 can be verified
    (let [unverified (verify/unverified-dependencies *test-repo*
                                                     (store/load-mote *test-repo* "202"))]
      (is (empty? unverified)))
    (verify/cast-vote! *test-repo* "202" "verifier-1" :for)
    (is (= :verified (:status (store/load-mote *test-repo* "202"))))))

;; -----------------------------------------------------------------------------
;; Verification Status Propagation Tests (Pure Functions)
;; -----------------------------------------------------------------------------

(deftest all-siblings-verified-pure-test
  (testing "all-siblings-verified? with no siblings (pure function)"
    ;; Create in-memory motes map
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1"]}
                 "1.1" {:id "1.1" :status :verified}}]
      (is (verify/all-siblings-verified? motes "1.1") "Single child has no unverified siblings")))

  (testing "all-siblings-verified? with verified siblings (pure function)"
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1" "1.2" "1.3"]}
                 "1.1" {:id "1.1" :status :verified}
                 "1.2" {:id "1.2" :status :verified}
                 "1.3" {:id "1.3" :status :verified}}]
      (is (verify/all-siblings-verified? motes "1.1"))
      (is (verify/all-siblings-verified? motes "1.2"))
      (is (verify/all-siblings-verified? motes "1.3"))))

  (testing "all-siblings-verified? with unverified sibling (pure function)"
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1" "1.2"]}
                 "1.1" {:id "1.1" :status :verified}
                 "1.2" {:id "1.2" :status :fixed}}]
      ;; When checking "1.1", its sibling "1.2" is NOT verified -> false
      (is (not (verify/all-siblings-verified? motes "1.1")) "Sibling 1.2 is not verified")
      ;; When checking "1.2", its sibling "1.1" IS verified -> true
      ;; The function checks OTHER siblings, not the current mote
      (is (verify/all-siblings-verified? motes "1.2") "Sibling 1.1 is verified")))

  (testing "all-siblings-verified? returns nil for root mote (pure function)"
    (let [motes {"1" {:id "1" :status :verified}}]
      (is (nil? (verify/all-siblings-verified? motes "1")) "Root has no parent")))

  (testing "all-siblings-verified? with missing parent (pure function)"
    (let [motes {"1.1" {:id "1.1" :status :verified}}]
      ;; Parent "1" doesn't exist in motes
      (is (nil? (verify/all-siblings-verified? motes "1.1")) "Parent not found"))))

(deftest can-propagate-to-parent-pure-test
  (testing "can propagate when parent is fixed and all children verified (pure function)"
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1"] :created-by "other-agent"}
                 "1.1" {:id "1.1" :status :verified}}]
      (is (verify/can-propagate-to-parent? motes "1" "verifier-1"))))

  (testing "cannot propagate when parent not fixed (pure function)"
    (let [motes {"1" {:id "1" :status :proposed :children ["1.1"] :created-by "other-agent"}
                 "1.1" {:id "1.1" :status :verified}}]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))))

  (testing "cannot propagate when children not all verified (pure function)"
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1" "1.2"] :created-by "other-agent"}
                 "1.1" {:id "1.1" :status :verified}
                 "1.2" {:id "1.2" :status :fixed}}]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))))

  (testing "cannot propagate when agent already voted on parent (pure function)"
    (let [motes {"1" {:id "1" :status :fixed :children ["1.1"] :created-by "other-agent"
                      :votes [{:agent "verifier-1" :vote :for}]}
                 "1.1" {:id "1.1" :status :verified}}]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))))

  (testing "cannot propagate when parent doesn't exist (pure function)"
    (let [motes {"1.1" {:id "1.1" :status :verified}}]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1"))))))

(deftest propagate-verification-root-test
  (testing "propagation stops at root mote"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    ;; Just a root mote, no parent
    (create-test-mote! "1" "Root" :status :fixed)
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (let [propagated (verify/propagate-verification! *test-repo* "1" "verifier-1")]
      (is (empty? propagated) "Nothing to propagate to from root"))))

(deftest propagate-verification-no-parent-test
  (testing "propagation returns empty when parent doesn't exist"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    ;; Child mote without parent in store
    (create-test-mote! "99.1" "Orphan child" :status :fixed)
    (verify/cast-vote! *test-repo* "99.1" "verifier-1" :for)
    (let [propagated (verify/propagate-verification! *test-repo* "99.1" "verifier-1")]
      (is (empty? propagated) "No parent to propagate to"))))

;; -----------------------------------------------------------------------------
;; Vote Reason Edge Cases
;; -----------------------------------------------------------------------------

(deftest vote-reasons-preserved-test
  (testing "vote reasons are preserved in mote"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "alice" :for :reason "Clear and correct")
    (verify/cast-vote! *test-repo* "1" "bob" :for :reason "Double-checked the math")
    (let [m (store/load-mote *test-repo* "1")
          votes (:votes m)]
      (is (= 2 (count votes)))
      (is (= "Clear and correct" (:reason (first votes))))
      (is (= "Double-checked the math" (:reason (second votes)))))))

(deftest vote-empty-reason-test
  (testing "empty string reason is allowed"
    (create-test-mote! "1" "Test claim")
    (verify/cast-vote! *test-repo* "1" "alice" :for :reason "")
    (let [m (store/load-mote *test-repo* "1")]
      (is (= "" (:reason (first (:votes m))))))))

;; -----------------------------------------------------------------------------
;; Status Query Edge Cases
;; -----------------------------------------------------------------------------

(deftest verification-status-contested-test
  (testing "verification status for contested mote"
    (create-test-mote! "1" "Controversial claim")
    (verify/cast-vote! *test-repo* "1" "alice" :for)
    (verify/cast-vote! *test-repo* "1" "bob" :against)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :contested (:status status)))
      (is (= :contested (:quorum-status status)))
      (is (= 1 (:votes-for status)))
      (is (= 1 (:votes-against status)))
      (is (= 0 (:votes-needed status)) "Quorum reached, even if contested"))))

(deftest verification-status-refuted-test
  (testing "verification status for refuted mote"
    (create-test-mote! "1" "Flawed claim")
    (verify/cast-vote! *test-repo* "1" "alice" :against)
    (verify/cast-vote! *test-repo* "1" "bob" :against)
    (let [status (verify/verification-status *test-repo* "1")]
      (is (= :refuted (:status status)))
      (is (= :refuted (:quorum-status status)))
      (is (= 0 (:votes-for status)))
      (is (= 2 (:votes-against status))))))

;; -----------------------------------------------------------------------------
;; needs-verification? Edge Cases
;; -----------------------------------------------------------------------------

(deftest needs-verification-edge-cases-test
  (testing "contested mote does not need verification (already resolved)"
    (let [m {:id "1" :status :contested :taint #{:needs-verification}}]
      (is (not (verify/needs-verification? m)))))

  (testing "refuted mote does not need verification"
    (let [m {:id "1" :status :refuted :taint #{:needs-verification}}]
      (is (not (verify/needs-verification? m)))))

  (testing "fixed mote without taint does not need verification"
    (let [m {:id "1" :status :fixed :taint #{}}]
      (is (not (verify/needs-verification? m)))))

  (testing "fixed mote with only needs-votes does not need verification"
    (let [m {:id "1" :status :fixed :taint #{:needs-votes}}]
      (is (not (verify/needs-verification? m)))))

  (testing "fixed mote with needs-verification needs verification"
    (let [m {:id "1" :status :fixed :taint #{:needs-verification}}]
      (is (verify/needs-verification? m)))))

;; -----------------------------------------------------------------------------
;; Concurrent Verification Scenarios
;; -----------------------------------------------------------------------------

(deftest multiple-motes-independent-verification-test
  (testing "multiple motes can be verified independently"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    (create-test-mote! "1" "First claim" :taint #{:needs-verification})
    (create-test-mote! "2" "Second claim" :taint #{:needs-verification})
    (create-test-mote! "3" "Third claim" :taint #{:needs-verification})
    ;; Verify in any order
    (verify/cast-vote! *test-repo* "2" "verifier" :for)
    (verify/cast-vote! *test-repo* "1" "verifier" :for)
    (verify/cast-vote! *test-repo* "3" "verifier" :for)
    (is (= :verified (:status (store/load-mote *test-repo* "1"))))
    (is (= :verified (:status (store/load-mote *test-repo* "2"))))
    (is (= :verified (:status (store/load-mote *test-repo* "3"))))))

;; -----------------------------------------------------------------------------
;; Non-Standard Vote Quorum Configuration Tests
;; -----------------------------------------------------------------------------

(deftest vote-quorum-1-single-verifier-test
  (testing "vote-quorum=1 verifies with single vote"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    (create-test-mote! "1" "Simple claim")
    (let [result (verify/cast-vote! *test-repo* "1" "solo-verifier" :for)
          {:keys [quorum-status new-status]} (:result result)]
      (is (= :verified quorum-status))
      (is (= :verified new-status))
      ;; Verify mote state
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :verified (:status m)))
        (is (= 1 (count (:votes m))))))))

(deftest vote-quorum-1-single-refutation-test
  (testing "vote-quorum=1 refutes with single against vote"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 1})
    (create-test-mote! "1" "Flawed claim")
    (let [result (verify/cast-vote! *test-repo* "1" "solo-verifier" :against
                                     :reason "Found error")
          {:keys [quorum-status new-status]} (:result result)]
      (is (= :refuted quorum-status))
      (is (= :refuted new-status))
      (let [m (store/load-mote *test-repo* "1")]
        (is (= :refuted (:status m)))))))

(deftest vote-quorum-3-requires-three-votes-test
  (testing "vote-quorum=3 requires three matching votes"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 3})
    (create-test-mote! "1" "Needs three verifiers")
    ;; First two votes are pending
    (let [r1 (verify/cast-vote! *test-repo* "1" "verifier-1" :for)]
      (is (= :pending (:quorum-status (:result r1))))
      (is (= :fixed (:new-status (:result r1)))))
    (let [r2 (verify/cast-vote! *test-repo* "1" "verifier-2" :for)]
      (is (= :pending (:quorum-status (:result r2)))))
    ;; Third vote reaches quorum
    (let [r3 (verify/cast-vote! *test-repo* "1" "verifier-3" :for)]
      (is (= :verified (:quorum-status (:result r3))))
      (is (= :verified (:new-status (:result r3)))))
    ;; Verify final state
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :verified (:status m)))
      (is (= 3 (count (:votes m)))))))

(deftest vote-quorum-5-requires-five-votes-test
  (testing "vote-quorum=5 requires five matching votes for verification"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 5})
    (create-test-mote! "1" "High-stakes claim")
    ;; First four votes are pending
    (doseq [i (range 1 5)]
      (let [result (verify/cast-vote! *test-repo* "1" (str "verifier-" i) :for)]
        (is (= :pending (:quorum-status (:result result)))
            (str "Vote " i " should be pending"))))
    ;; Fifth vote reaches quorum
    (let [r5 (verify/cast-vote! *test-repo* "1" "verifier-5" :for)]
      (is (= :verified (:quorum-status (:result r5)))))
    ;; Verify final state
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :verified (:status m)))
      (is (= 5 (count (:votes m)))))))

(deftest vote-quorum-10-requires-ten-votes-test
  (testing "vote-quorum=10 requires ten matching votes"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 10})
    (create-test-mote! "1" "Critical theorem")
    ;; First nine votes are pending
    (doseq [i (range 1 10)]
      (let [result (verify/cast-vote! *test-repo* "1" (str "verifier-" i) :for)]
        (is (= :pending (:quorum-status (:result result)))
            (str "Vote " i " should be pending"))))
    ;; Tenth vote reaches quorum
    (let [r10 (verify/cast-vote! *test-repo* "1" "verifier-10" :for)]
      (is (= :verified (:quorum-status (:result r10)))))
    (is (= :verified (:status (store/load-mote *test-repo* "1"))))))

(deftest vote-quorum-3-refutation-test
  (testing "vote-quorum=3 refutation requires three against votes"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 3})
    (create-test-mote! "1" "Incorrect claim")
    ;; First two against votes are pending
    (let [r1 (verify/cast-vote! *test-repo* "1" "verifier-1" :against)]
      (is (= :pending (:quorum-status (:result r1)))))
    (let [r2 (verify/cast-vote! *test-repo* "1" "verifier-2" :against)]
      (is (= :pending (:quorum-status (:result r2)))))
    ;; Third vote reaches quorum for refutation
    (let [r3 (verify/cast-vote! *test-repo* "1" "verifier-3" :against)]
      (is (= :refuted (:quorum-status (:result r3))))
      (is (= :refuted (:new-status (:result r3)))))
    (is (= :refuted (:status (store/load-mote *test-repo* "1"))))))

(deftest vote-quorum-exact-boundary-for-test
  (testing "quorum boundary - verified at exact quorum"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 4})
    (create-test-mote! "1" "Test claim")
    ;; Cast exactly 4 votes
    (doseq [i (range 1 4)]
      (verify/cast-vote! *test-repo* "1" (str "verifier-" i) :for))
    (let [r4 (verify/cast-vote! *test-repo* "1" "verifier-4" :for)]
      (is (= :verified (:quorum-status (:result r4))))
      (is (= 0 (:votes-needed (verify/verification-status *test-repo* "1")))))))

(deftest vote-quorum-exact-boundary-against-test
  (testing "quorum boundary - refuted at exact quorum"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 4})
    (create-test-mote! "1" "Test claim")
    ;; Cast exactly 4 against votes
    (doseq [i (range 1 4)]
      (verify/cast-vote! *test-repo* "1" (str "verifier-" i) :against))
    (let [r4 (verify/cast-vote! *test-repo* "1" "verifier-4" :against)]
      (is (= :refuted (:quorum-status (:result r4)))))))

(deftest vote-quorum-cannot-vote-after-quorum-test
  (testing "cannot vote after quorum is reached - verified"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 2})
    (create-test-mote! "1" "Test claim")
    ;; Reach quorum
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1" "verifier-2" :for)
    ;; Try to vote after quorum - should fail because status is now :verified
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Can only vote on fixed motes"
                          (verify/cast-vote! *test-repo* "1" "verifier-3" :for)))))

(deftest vote-quorum-5-contested-with-mixed-votes-test
  (testing "vote-quorum=5 with mixed votes leads to contested"
    (store/save-config! *test-repo* {:project-name "Test" :vote-quorum 5})
    (create-test-mote! "1" "Debatable claim")
    ;; 3 for votes
    (doseq [i (range 1 4)]
      (verify/cast-vote! *test-repo* "1" (str "pro-" i) :for))
    ;; 2 against votes to reach quorum
    (verify/cast-vote! *test-repo* "1" "con-1" :against)
    (let [r5 (verify/cast-vote! *test-repo* "1" "con-2" :against)]
      (is (= :contested (:quorum-status (:result r5))))
      (is (= :contested (:new-status (:result r5)))))
    ;; Verify final state
    (let [m (store/load-mote *test-repo* "1")]
      (is (= :contested (:status m)))
      (is (= 5 (count (:votes m))))
      (is (contains? (:taint m) :needs-votes)))))
