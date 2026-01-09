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
