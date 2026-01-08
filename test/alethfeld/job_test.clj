(ns alethfeld.job-test
  (:require [clojure.test :refer [deftest testing is are]]
            [alethfeld.job :as job]
            [alethfeld.mote :as mote]))

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- test-mote
  "Create a minimal valid mote for testing.
   Accepts overrides for any mote field."
  [& {:keys [id claim status taint priority difficulty
             claimed-by claimed-at]
      :or {id "1"
           claim "Test claim"
           status :fixed
           taint #{}
           priority :p2
           difficulty 3}}]
  (cond-> (mote/make-mote id claim "test-agent"
                          :status status
                          :taint taint
                          :priority priority
                          :difficulty difficulty)
    claimed-by (mote/set-claimed-by claimed-by)))

;; =============================================================================
;; mote->roles Tests
;; =============================================================================

(deftest mote->roles-empty-taint-test
  (testing "Mote with no taints returns empty set"
    (let [m (test-mote :taint #{})]
      (is (= #{} (job/mote->roles m))))))

(deftest mote->roles-single-taint-test
  (testing "Each taint maps to its corresponding role"
    (are [taint expected-role]
         (= #{expected-role} (job/mote->roles (test-mote :taint #{taint})))

      :needs-decomposition   :proposer
      :needs-proposal-review :advisor
      :needs-refinement      :prover
      :needs-verification    :verifier
      :needs-refs            :ref-checker
      :needs-counterexample  :counterexample)))

(deftest mote->roles-needs-votes-test
  (testing ":needs-votes does not map to any role"
    (let [m (test-mote :taint #{:needs-votes})]
      (is (= #{} (job/mote->roles m))))))

(deftest mote->roles-multiple-taints-test
  (testing "Multiple taints return multiple roles"
    (let [m (test-mote :taint #{:needs-decomposition :needs-verification})]
      (is (= #{:proposer :verifier} (job/mote->roles m)))))

  (testing "All taints return all corresponding roles"
    (let [m (test-mote :taint #{:needs-decomposition
                                :needs-proposal-review
                                :needs-refinement
                                :needs-verification
                                :needs-refs
                                :needs-counterexample})]
      (is (= #{:proposer :advisor :prover :verifier :ref-checker :counterexample}
             (job/mote->roles m))))))

(deftest mote->roles-mixed-with-needs-votes-test
  (testing ":needs-votes mixed with other taints is ignored"
    (let [m (test-mote :taint #{:needs-votes :needs-verification})]
      (is (= #{:verifier} (job/mote->roles m))))))

;; =============================================================================
;; mote->role Tests (Primary Role Selection)
;; =============================================================================

(deftest mote->role-no-taints-test
  (testing "Returns nil when no role-mapped taints"
    (is (nil? (job/mote->role (test-mote :taint #{}))))
    (is (nil? (job/mote->role (test-mote :taint #{:needs-votes}))))))

(deftest mote->role-single-taint-test
  (testing "Returns the single mapped role"
    (are [taint expected-role]
         (= expected-role (job/mote->role (test-mote :taint #{taint})))

      :needs-decomposition   :proposer
      :needs-proposal-review :advisor
      :needs-refinement      :prover
      :needs-verification    :verifier
      :needs-refs            :ref-checker
      :needs-counterexample  :counterexample)))

(deftest mote->role-priority-order-test
  (testing "Returns highest priority role when multiple taints present"
    ;; Priority: advisor > proposer > prover > verifier > ref-checker > counterexample

    (testing "Advisor takes priority over proposer"
      (let [m (test-mote :taint #{:needs-decomposition :needs-proposal-review})]
        (is (= :advisor (job/mote->role m)))))

    (testing "Proposer takes priority over prover"
      (let [m (test-mote :taint #{:needs-decomposition :needs-refinement})]
        (is (= :proposer (job/mote->role m)))))

    (testing "Prover takes priority over verifier"
      (let [m (test-mote :taint #{:needs-refinement :needs-verification})]
        (is (= :prover (job/mote->role m)))))

    (testing "Verifier takes priority over ref-checker"
      (let [m (test-mote :taint #{:needs-verification :needs-refs})]
        (is (= :verifier (job/mote->role m)))))

    (testing "Ref-checker takes priority over counterexample"
      (let [m (test-mote :taint #{:needs-refs :needs-counterexample})]
        (is (= :ref-checker (job/mote->role m)))))

    (testing "All roles returns advisor (highest priority)"
      (let [m (test-mote :taint #{:needs-decomposition
                                  :needs-proposal-review
                                  :needs-refinement
                                  :needs-verification
                                  :needs-refs
                                  :needs-counterexample})]
        (is (= :advisor (job/mote->role m)))))))

;; =============================================================================
;; workable? Tests
;; =============================================================================

(deftest workable-basic-test
  (testing "Unclaimed mote with role-taint is workable"
    (let [m (test-mote :status :fixed :taint #{:needs-verification})]
      (is (true? (job/workable? m)))))

  (testing "Proposed mote with taint is workable"
    (let [m (test-mote :status :proposed :taint #{:needs-proposal-review})]
      (is (true? (job/workable? m)))))

  (testing "Contested mote with taint is workable"
    (let [m (test-mote :status :contested :taint #{:needs-verification})]
      (is (true? (job/workable? m))))))

(deftest workable-terminal-status-test
  (testing "Verified mote is not workable"
    (let [m (test-mote :status :verified :taint #{:needs-verification})]
      (is (false? (job/workable? m)))))

  (testing "Rejected mote is not workable"
    (let [m (test-mote :status :rejected :taint #{:needs-verification})]
      (is (false? (job/workable? m)))))

  (testing "Refuted mote is not workable"
    (let [m (test-mote :status :refuted :taint #{:needs-verification})]
      (is (false? (job/workable? m))))))

(deftest workable-claimed-test
  (testing "Claimed mote is not workable"
    (let [m (test-mote :status :fixed
                       :taint #{:needs-verification}
                       :claimed-by "some-agent")]
      (is (false? (job/workable? m))))))

(deftest workable-no-role-taint-test
  (testing "Mote with no taints is not workable"
    (let [m (test-mote :status :fixed :taint #{})]
      (is (false? (job/workable? m)))))

  (testing "Mote with only :needs-votes is not workable (no role)"
    (let [m (test-mote :status :fixed :taint #{:needs-votes})]
      (is (false? (job/workable? m))))))

(deftest workable-combined-conditions-test
  (testing "Terminal + unclaimed + taint = not workable"
    (let [m (test-mote :status :verified :taint #{:needs-verification})]
      (is (false? (job/workable? m)))))

  (testing "Fixed + claimed + taint = not workable"
    (let [m (test-mote :status :fixed
                       :taint #{:needs-verification}
                       :claimed-by "agent")]
      (is (false? (job/workable? m)))))

  (testing "Fixed + unclaimed + no-role-taint = not workable"
    (let [m (test-mote :status :fixed :taint #{:needs-votes})]
      (is (false? (job/workable? m))))))

;; =============================================================================
;; matches-filter? Tests - Role Filtering
;; =============================================================================

(deftest matches-filter-no-options-test
  (testing "Empty options matches any mote"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {}))))))

(deftest matches-filter-role-test
  (testing "Role filter matches when mote has that role"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {:role :verifier})))))

  (testing "Role filter rejects when mote doesn't have that role"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (false? (job/matches-filter? m {:role :proposer})))))

  (testing "Role filter matches one of multiple roles"
    (let [m (test-mote :taint #{:needs-decomposition :needs-verification})]
      (is (true? (job/matches-filter? m {:role :proposer})))
      (is (true? (job/matches-filter? m {:role :verifier})))))

  (testing "Role filter rejects mote with no taints"
    (let [m (test-mote :taint #{})]
      (is (false? (job/matches-filter? m {:role :verifier}))))))

;; =============================================================================
;; matches-filter? Tests - Difficulty Filtering
;; =============================================================================

(deftest matches-filter-difficulty-exact-test
  (testing "Exact difficulty match"
    (let [m (test-mote :difficulty 3)]
      (is (true? (job/matches-filter? m {:difficulty 3})))
      (is (false? (job/matches-filter? m {:difficulty 2})))
      (is (false? (job/matches-filter? m {:difficulty 4}))))))

(deftest matches-filter-difficulty-range-test
  (testing "Difficulty range match"
    (let [m3 (test-mote :difficulty 3)]
      (is (true? (job/matches-filter? m3 {:difficulty [1 5]})))
      (is (true? (job/matches-filter? m3 {:difficulty [3 3]})))
      (is (true? (job/matches-filter? m3 {:difficulty [2 4]})))
      (is (false? (job/matches-filter? m3 {:difficulty [4 5]})))
      (is (false? (job/matches-filter? m3 {:difficulty [1 2]})))))

  (testing "Edge cases for difficulty range"
    (let [m1 (test-mote :difficulty 1)
          m5 (test-mote :difficulty 5)]
      (is (true? (job/matches-filter? m1 {:difficulty [1 3]})))
      (is (true? (job/matches-filter? m5 {:difficulty [3 5]})))
      (is (false? (job/matches-filter? m1 {:difficulty [2 5]})))
      (is (false? (job/matches-filter? m5 {:difficulty [1 4]}))))))

;; =============================================================================
;; matches-filter? Tests - Priority Filtering
;; =============================================================================

(deftest matches-filter-priority-exact-test
  (testing "Exact priority match"
    (let [m (test-mote :priority :p2)]
      (is (true? (job/matches-filter? m {:priority :p2})))
      (is (false? (job/matches-filter? m {:priority :p1})))
      (is (false? (job/matches-filter? m {:priority :p3}))))))

(deftest matches-filter-priority-range-test
  (testing "Priority range match (p0 is highest urgency)"
    (let [mp2 (test-mote :priority :p2)]
      ;; Range [:p1 :p3] means p1, p2, or p3
      (is (true? (job/matches-filter? mp2 {:priority [:p0 :p4]})))
      (is (true? (job/matches-filter? mp2 {:priority [:p2 :p2]})))
      (is (true? (job/matches-filter? mp2 {:priority [:p1 :p3]})))
      (is (false? (job/matches-filter? mp2 {:priority [:p0 :p1]})))
      (is (false? (job/matches-filter? mp2 {:priority [:p3 :p4]})))))

  (testing "Edge cases for priority range"
    (let [mp0 (test-mote :priority :p0)
          mp4 (test-mote :priority :p4)]
      (is (true? (job/matches-filter? mp0 {:priority [:p0 :p2]})))
      (is (true? (job/matches-filter? mp4 {:priority [:p2 :p4]})))
      (is (false? (job/matches-filter? mp0 {:priority [:p1 :p4]})))
      (is (false? (job/matches-filter? mp4 {:priority [:p0 :p3]}))))))

;; =============================================================================
;; matches-filter? Tests - Combined Filters
;; =============================================================================

(deftest matches-filter-combined-test
  (testing "Multiple filters must all match"
    (let [m (test-mote :taint #{:needs-verification}
                       :difficulty 3
                       :priority :p2)]
      ;; All match
      (is (true? (job/matches-filter? m {:role :verifier
                                         :difficulty 3
                                         :priority :p2})))
      ;; Role doesn't match
      (is (false? (job/matches-filter? m {:role :proposer
                                          :difficulty 3
                                          :priority :p2})))
      ;; Difficulty doesn't match
      (is (false? (job/matches-filter? m {:role :verifier
                                          :difficulty 5
                                          :priority :p2})))
      ;; Priority doesn't match
      (is (false? (job/matches-filter? m {:role :verifier
                                          :difficulty 3
                                          :priority :p0})))))

  (testing "Range filters combined"
    (let [m (test-mote :taint #{:needs-decomposition :needs-verification}
                       :difficulty 3
                       :priority :p1)]
      (is (true? (job/matches-filter? m {:role :verifier
                                         :difficulty [2 4]
                                         :priority [:p0 :p2]})))
      (is (true? (job/matches-filter? m {:role :proposer
                                         :difficulty [1 5]
                                         :priority [:p1 :p1]}))))))

;; =============================================================================
;; matches-filter? Tests - Ignored Options
;; =============================================================================

(deftest matches-filter-ignores-other-options-test
  (testing ":agent option is ignored by matches-filter?"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {:agent "some-agent"})))))

  (testing ":max option is ignored by matches-filter?"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {:max 5})))))

  (testing ":no-claim option is ignored by matches-filter?"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {:no-claim true})))))

  (testing ":format option is ignored by matches-filter?"
    (let [m (test-mote :taint #{:needs-verification})]
      (is (true? (job/matches-filter? m {:format :json}))))))
