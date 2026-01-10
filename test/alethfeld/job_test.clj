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
    ;; Priority: verifier > proposer > advisor > prover > ref-checker > counterexample

    (testing "Proposer takes priority over advisor"
      (let [m (test-mote :taint #{:needs-decomposition :needs-proposal-review})]
        (is (= :proposer (job/mote->role m)))))

    (testing "Proposer takes priority over prover"
      (let [m (test-mote :taint #{:needs-decomposition :needs-refinement})]
        (is (= :proposer (job/mote->role m)))))

    (testing "Verifier takes priority over prover"
      (let [m (test-mote :taint #{:needs-refinement :needs-verification})]
        (is (= :verifier (job/mote->role m)))))

    (testing "Verifier takes priority over ref-checker"
      (let [m (test-mote :taint #{:needs-verification :needs-refs})]
        (is (= :verifier (job/mote->role m)))))

    (testing "Ref-checker takes priority over counterexample"
      (let [m (test-mote :taint #{:needs-refs :needs-counterexample})]
        (is (= :ref-checker (job/mote->role m)))))

    (testing "All roles returns verifier (highest priority)"
      (let [m (test-mote :taint #{:needs-decomposition
                                  :needs-proposal-review
                                  :needs-refinement
                                  :needs-verification
                                  :needs-refs
                                  :needs-counterexample})]
        (is (= :verifier (job/mote->role m)))))))

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

;; =============================================================================
;; priority->rank Tests
;; =============================================================================

(deftest priority->rank-test
  (testing "All priorities map to correct ranks"
    (is (= 0 (job/priority->rank :p0)))
    (is (= 1 (job/priority->rank :p1)))
    (is (= 2 (job/priority->rank :p2)))
    (is (= 3 (job/priority->rank :p3)))
    (is (= 4 (job/priority->rank :p4))))

  (testing "Ranks maintain correct ordering"
    (is (< (job/priority->rank :p0) (job/priority->rank :p1)))
    (is (< (job/priority->rank :p1) (job/priority->rank :p2)))
    (is (< (job/priority->rank :p2) (job/priority->rank :p3)))
    (is (< (job/priority->rank :p3) (job/priority->rank :p4)))))

(deftest priority->rank-nil-test
  (testing "nil priority returns high rank (sorts last)"
    (is (= 999 (job/priority->rank nil)))
    (is (> (job/priority->rank nil) (job/priority->rank :p4)))))

(deftest priority->rank-invalid-test
  (testing "Invalid priority keyword returns high rank (sorts last)"
    (is (= 999 (job/priority->rank :invalid)))
    (is (= 999 (job/priority->rank :p5)))
    (is (= 999 (job/priority->rank :high)))
    (is (> (job/priority->rank :invalid) (job/priority->rank :p4)))))

;; =============================================================================
;; job-comparator Tests
;; =============================================================================

(deftest job-comparator-priority-test
  (testing "Higher priority (lower p-number) comes first"
    (let [m-p0 (test-mote :priority :p0 :difficulty 3)
          m-p1 (test-mote :priority :p1 :difficulty 3)
          m-p2 (test-mote :priority :p2 :difficulty 3)]
      (is (neg? (job/job-comparator m-p0 m-p1)))
      (is (neg? (job/job-comparator m-p0 m-p2)))
      (is (neg? (job/job-comparator m-p1 m-p2)))
      (is (pos? (job/job-comparator m-p2 m-p1)))
      (is (pos? (job/job-comparator m-p2 m-p0))))))

(deftest job-comparator-difficulty-test
  (testing "Lower difficulty comes first when priority is equal"
    (let [m-d1 (test-mote :priority :p2 :difficulty 1)
          m-d3 (test-mote :priority :p2 :difficulty 3)
          m-d5 (test-mote :priority :p2 :difficulty 5)]
      (is (neg? (job/job-comparator m-d1 m-d3)))
      (is (neg? (job/job-comparator m-d1 m-d5)))
      (is (neg? (job/job-comparator m-d3 m-d5)))
      (is (pos? (job/job-comparator m-d5 m-d3)))
      (is (pos? (job/job-comparator m-d5 m-d1))))))

(deftest job-comparator-equal-test
  (testing "Equal priority and difficulty returns 0"
    (let [m1 (test-mote :priority :p2 :difficulty 3)
          m2 (test-mote :priority :p2 :difficulty 3)]
      (is (zero? (job/job-comparator m1 m2))))))

(deftest job-comparator-priority-beats-difficulty-test
  (testing "Priority takes precedence over difficulty"
    (let [m-high-pri-high-diff (test-mote :priority :p0 :difficulty 5)
          m-low-pri-low-diff (test-mote :priority :p4 :difficulty 1)]
      ;; p0/d5 should come before p4/d1
      (is (neg? (job/job-comparator m-high-pri-high-diff m-low-pri-low-diff))))))

(deftest job-comparator-sort-test
  (testing "Sorting a collection produces correct order"
    (let [m1 (test-mote :id "1" :priority :p2 :difficulty 3)
          m2 (test-mote :id "2" :priority :p0 :difficulty 5)
          m3 (test-mote :id "3" :priority :p2 :difficulty 1)
          m4 (test-mote :id "4" :priority :p1 :difficulty 2)
          sorted (sort job/job-comparator [m1 m2 m3 m4])]
      ;; Expected order: p0/d5, p1/d2, p2/d1, p2/d3
      (is (= ["2" "4" "3" "1"] (mapv :id sorted))))))

(deftest job-comparator-nil-priority-test
  (testing "nil priority does not cause NPE"
    (let [m-nil (assoc (test-mote :id "1" :difficulty 3) :priority nil)
          m-p2 (test-mote :id "2" :priority :p2 :difficulty 3)]
      ;; Should not throw NPE
      (is (integer? (job/job-comparator m-nil m-p2)))
      (is (integer? (job/job-comparator m-p2 m-nil)))))

  (testing "nil priority sorts after valid priorities"
    (let [m-nil (assoc (test-mote :id "1" :difficulty 3) :priority nil)
          m-p4 (test-mote :id "2" :priority :p4 :difficulty 3)]
      ;; nil should come after p4 (lowest valid priority)
      (is (pos? (job/job-comparator m-nil m-p4)))
      (is (neg? (job/job-comparator m-p4 m-nil)))))

  (testing "Two nil priorities compare by difficulty"
    (let [m-nil-d1 (assoc (test-mote :id "1" :difficulty 1) :priority nil)
          m-nil-d5 (assoc (test-mote :id "2" :difficulty 5) :priority nil)]
      (is (neg? (job/job-comparator m-nil-d1 m-nil-d5)))
      (is (pos? (job/job-comparator m-nil-d5 m-nil-d1))))))

(deftest job-comparator-invalid-priority-test
  (testing "Invalid priority does not cause NPE"
    (let [m-invalid (assoc (test-mote :id "1" :difficulty 3) :priority :invalid)
          m-p2 (test-mote :id "2" :priority :p2 :difficulty 3)]
      ;; Should not throw NPE
      (is (integer? (job/job-comparator m-invalid m-p2)))
      (is (integer? (job/job-comparator m-p2 m-invalid)))))

  (testing "Invalid priority sorts after valid priorities"
    (let [m-invalid (assoc (test-mote :id "1" :difficulty 3) :priority :p99)
          m-p4 (test-mote :id "2" :priority :p4 :difficulty 3)]
      ;; Invalid should come after p4
      (is (pos? (job/job-comparator m-invalid m-p4)))
      (is (neg? (job/job-comparator m-p4 m-invalid)))))

  (testing "Sorting collection with nil/invalid priorities"
    (let [m1 (test-mote :id "1" :priority :p2 :difficulty 3)
          m2 (assoc (test-mote :id "2" :difficulty 2) :priority nil)
          m3 (assoc (test-mote :id "3" :difficulty 1) :priority :invalid)
          m4 (test-mote :id "4" :priority :p0 :difficulty 5)
          sorted (sort job/job-comparator [m1 m2 m3 m4])]
      ;; Expected: p0/d5, p2/d3, then nil/invalid by difficulty (d1, d2)
      (is (= ["4" "1" "3" "2"] (mapv :id sorted))))))

;; =============================================================================
;; build-job Tests
;; =============================================================================

(defn- test-mote-with-parent
  "Create a mote with parent relationship set up."
  [id parent-id & opts]
  (apply mote/make-mote id "Test claim" "test-agent"
         :parent parent-id
         opts))

(deftest build-job-basic-test
  (testing "Builds job with correct fields"
    (let [m (test-mote :id "1" :taint #{:needs-verification}
                       :priority :p1 :difficulty 2)
          motes {"1" m}
          job (job/build-job m motes)]
      (is (string? (:job-id job)))
      (is (clojure.string/starts-with? (:job-id job) "job-"))
      (is (= "1" (:mote-id job)))
      (is (= :verifier (:role job)))
      (is (= 2 (:difficulty job)))
      (is (= :p1 (:priority job)))
      (is (= m (:mote job)))
      (is (nil? (:parent job)))
      (is (= [] (:siblings job)))
      (is (string? (:prompt job))))))

(deftest build-job-role-override-test
  (testing "Role can be overridden"
    (let [m (test-mote :id "1" :taint #{:needs-verification})
          motes {"1" m}
          job (job/build-job m motes :role :proposer)]
      (is (= :proposer (:role job))))))

(deftest build-job-prompt-override-test
  (testing "Prompt can be provided"
    (let [m (test-mote :id "1" :taint #{:needs-verification})
          motes {"1" m}
          job (job/build-job m motes :prompt "Custom prompt")]
      (is (= "Custom prompt" (:prompt job))))))

(deftest build-job-with-parent-test
  (testing "Parent is included when present"
    (let [parent (-> (test-mote :id "1" :taint #{:needs-decomposition})
                     (assoc :children ["1.1" "1.2"]))
          child (test-mote-with-parent "1.1" "1"
                                       :taint #{:needs-verification})
          motes {"1" parent "1.1" child}
          job (job/build-job child motes)]
      (is (= parent (:parent job))))))

(deftest build-job-with-siblings-test
  (testing "Siblings are included when parent exists"
    (let [parent (-> (test-mote :id "1" :taint #{:needs-decomposition})
                     (assoc :children ["1.1" "1.2" "1.3"]))
          child1 (test-mote-with-parent "1.1" "1" :taint #{:needs-verification})
          child2 (test-mote-with-parent "1.2" "1" :taint #{:needs-refinement})
          child3 (test-mote-with-parent "1.3" "1" :taint #{:needs-refs})
          motes {"1" parent "1.1" child1 "1.2" child2 "1.3" child3}
          job (job/build-job child1 motes)]
      (is (= 2 (count (:siblings job))))
      (is (= #{"1.2" "1.3"} (set (map :id (:siblings job))))))))

(deftest build-job-missing-siblings-test
  (testing "Missing siblings are skipped gracefully"
    (let [parent (-> (test-mote :id "1" :taint #{:needs-decomposition})
                     (assoc :children ["1.1" "1.2" "1.3"]))
          child1 (test-mote-with-parent "1.1" "1" :taint #{:needs-verification})
          child2 (test-mote-with-parent "1.2" "1" :taint #{:needs-refinement})
          ;; child3 not in motes map
          motes {"1" parent "1.1" child1 "1.2" child2}
          job (job/build-job child1 motes)]
      (is (= 1 (count (:siblings job))))
      (is (= "1.2" (:id (first (:siblings job))))))))

;; =============================================================================
;; select-jobs Tests
;; =============================================================================

(deftest select-jobs-empty-test
  (testing "Empty motes returns empty vector"
    (is (= [] (job/select-jobs {}))))

  (testing "No workable motes returns empty vector"
    (let [verified (test-mote :id "1" :status :verified :taint #{:needs-verification})
          claimed (test-mote :id "2" :status :fixed :taint #{:needs-verification}
                             :claimed-by "agent")
          no-taint (test-mote :id "3" :status :fixed :taint #{})
          motes {"1" verified "2" claimed "3" no-taint}]
      (is (= [] (job/select-jobs motes))))))

(deftest select-jobs-single-test
  (testing "Selects single workable mote"
    (let [m (test-mote :id "1" :taint #{:needs-verification})
          motes {"1" m}
          jobs (job/select-jobs motes)]
      (is (= 1 (count jobs)))
      (is (= "1" (:mote-id (first jobs)))))))

(deftest select-jobs-default-max-test
  (testing "Default max is 1"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification} :priority :p1)
          m2 (test-mote :id "2" :taint #{:needs-verification} :priority :p2)
          motes {"1" m1 "2" m2}
          jobs (job/select-jobs motes)]
      (is (= 1 (count jobs))))))

(deftest select-jobs-max-test
  (testing "Respects :max option"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification} :priority :p1)
          m2 (test-mote :id "2" :taint #{:needs-verification} :priority :p2)
          m3 (test-mote :id "3" :taint #{:needs-verification} :priority :p3)
          motes {"1" m1 "2" m2 "3" m3}]
      (is (= 2 (count (job/select-jobs motes :max 2))))
      (is (= 3 (count (job/select-jobs motes :max 3))))
      (is (= 3 (count (job/select-jobs motes :max 10)))))))

(deftest select-jobs-sorting-test
  (testing "Jobs are sorted by priority then difficulty"
    (let [m1 (test-mote :id "a" :taint #{:needs-verification} :priority :p2 :difficulty 3)
          m2 (test-mote :id "b" :taint #{:needs-verification} :priority :p0 :difficulty 5)
          m3 (test-mote :id "c" :taint #{:needs-verification} :priority :p2 :difficulty 1)
          m4 (test-mote :id "d" :taint #{:needs-verification} :priority :p1 :difficulty 2)
          motes {"a" m1 "b" m2 "c" m3 "d" m4}
          jobs (job/select-jobs motes :max 4)]
      ;; Expected order: p0/d5, p1/d2, p2/d1, p2/d3
      (is (= ["b" "d" "c" "a"] (mapv :mote-id jobs))))))

(deftest select-jobs-role-filter-test
  (testing "Filters by role"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (test-mote :id "2" :taint #{:needs-decomposition})
          m3 (test-mote :id "3" :taint #{:needs-verification})
          motes {"1" m1 "2" m2 "3" m3}
          jobs (job/select-jobs motes :role :verifier :max 10)]
      (is (= 2 (count jobs)))
      (is (= #{:verifier} (set (map :role jobs)))))))

(deftest select-jobs-difficulty-filter-test
  (testing "Filters by difficulty"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification} :difficulty 1)
          m2 (test-mote :id "2" :taint #{:needs-verification} :difficulty 3)
          m3 (test-mote :id "3" :taint #{:needs-verification} :difficulty 5)
          motes {"1" m1 "2" m2 "3" m3}]
      ;; Exact match
      (is (= 1 (count (job/select-jobs motes :difficulty 3 :max 10))))
      ;; Range
      (is (= 2 (count (job/select-jobs motes :difficulty [1 3] :max 10)))))))

(deftest select-jobs-priority-filter-test
  (testing "Filters by priority"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification} :priority :p0)
          m2 (test-mote :id "2" :taint #{:needs-verification} :priority :p2)
          m3 (test-mote :id "3" :taint #{:needs-verification} :priority :p4)
          motes {"1" m1 "2" m2 "3" m3}]
      ;; Exact match
      (is (= 1 (count (job/select-jobs motes :priority :p2 :max 10))))
      ;; Range
      (is (= 2 (count (job/select-jobs motes :priority [:p0 :p2] :max 10)))))))

(deftest select-jobs-combined-filters-test
  (testing "Multiple filters applied together"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification}
                        :priority :p1 :difficulty 2)
          m2 (test-mote :id "2" :taint #{:needs-decomposition}
                        :priority :p1 :difficulty 2)
          m3 (test-mote :id "3" :taint #{:needs-verification}
                        :priority :p3 :difficulty 2)
          m4 (test-mote :id "4" :taint #{:needs-verification}
                        :priority :p1 :difficulty 4)
          motes {"1" m1 "2" m2 "3" m3 "4" m4}
          jobs (job/select-jobs motes
                                :role :verifier
                                :priority [:p0 :p2]
                                :difficulty [1 3]
                                :max 10)]
      ;; Only m1 matches: verifier, p1 (in p0-p2), difficulty 2 (in 1-3)
      (is (= 1 (count jobs)))
      (is (= "1" (:mote-id (first jobs)))))))

(deftest select-jobs-filters-then-sorts-test
  (testing "Filtering happens before sorting"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification} :priority :p3)
          m2 (test-mote :id "2" :taint #{:needs-verification} :priority :p1)
          m3 (test-mote :id "3" :taint #{:needs-decomposition} :priority :p0)
          motes {"1" m1 "2" m2 "3" m3}
          jobs (job/select-jobs motes :role :verifier :max 10)]
      ;; m3 filtered out (wrong role), remaining sorted by priority
      (is (= ["2" "1"] (mapv :mote-id jobs))))))

(deftest select-jobs-role-propagated-to-job-test
  (testing "Role from options is used in built jobs"
    (let [m (test-mote :id "1" :taint #{:needs-decomposition :needs-verification})
          motes {"1" m}
          jobs (job/select-jobs motes :role :verifier)]
      ;; Even though mote has both roles, :verifier was specified
      (is (= :verifier (:role (first jobs)))))))

;; =============================================================================
;; Claim Timeout Tests
;; =============================================================================

(deftest workable-claim-timeout-test
  (testing "Claimed mote is not workable without timeout"
    (let [m (test-mote :status :fixed
                       :taint #{:needs-verification}
                       :claimed-by "some-agent")]
      (is (false? (job/workable? m)))))

  (testing "Claimed mote is not workable with timeout when claim is fresh"
    (let [m (test-mote :status :fixed
                       :taint #{:needs-verification}
                       :claimed-by "some-agent")]
      ;; Fresh claim (just created) should not be expired
      (is (false? (job/workable? m :claim-timeout 30)))))

  (testing "Claimed mote becomes workable when claim expires"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 60 60 1000))) ;; 60 minutes ago
          m (-> (test-mote :status :fixed
                           :taint #{:needs-verification})
                (assoc :claimed-by "some-agent")
                (assoc :claimed-at old-time))]
      ;; Without timeout: not workable (claimed)
      (is (false? (job/workable? m)))
      ;; With 30-minute timeout: workable (claim expired)
      (is (true? (job/workable? m :claim-timeout 30))))))

(deftest select-jobs-claim-timeout-test
  (testing "select-jobs includes motes with expired claims when timeout provided"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 60 60 1000))) ;; 60 minutes ago
          m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (-> (test-mote :id "2" :taint #{:needs-verification})
                 (assoc :claimed-by "stale-agent")
                 (assoc :claimed-at old-time))
          motes {"1" m1 "2" m2}]
      ;; Without timeout: only m1 is available
      (is (= ["1"] (mapv :mote-id (job/select-jobs motes :max 10))))
      ;; With timeout: both available (m2's claim expired)
      (is (= #{"1" "2"} (set (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout 30)))))))

  (testing "select-jobs excludes motes with fresh claims even with timeout"
    (let [m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (test-mote :id "2" :taint #{:needs-verification} :claimed-by "active-agent")
          motes {"1" m1 "2" m2}]
      ;; With timeout: only m1 available (m2's claim is fresh)
      (is (= ["1"] (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout 30)))))))

;; =============================================================================
;; Claim Timeout Hours Tests (job.clj claim-expired? wrapper)
;; =============================================================================

(deftest claim-expired-hours-test
  (testing "claim-expired? returns false for unclaimed mote"
    (let [m (test-mote)]
      (is (false? (job/claim-expired? m)))))

  (testing "claim-expired? returns false for mote with no claimed-at"
    (let [m (assoc (test-mote) :claimed-by "agent-1")]
      (is (false? (job/claim-expired? m)))))

  (testing "claim-expired? returns false for fresh claim with default 24h timeout"
    (let [m (mote/set-claimed-by (test-mote) "agent-1")]
      (is (false? (job/claim-expired? m)))))

  (testing "claim-expired? returns true for claim older than 24 hours (default)"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000))) ;; 25 hours ago
          m (-> (test-mote)
                (assoc :claimed-by "agent-1")
                (assoc :claimed-at old-time))]
      (is (true? (job/claim-expired? m)))))

  (testing "claim-expired? respects custom timeout-hours"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 2 60 60 1000))) ;; 2 hours ago
          m (-> (test-mote)
                (assoc :claimed-by "agent-1")
                (assoc :claimed-at old-time))]
      ;; Not expired with 4-hour timeout
      (is (false? (job/claim-expired? m :timeout-hours 4)))
      ;; Expired with 1-hour timeout
      (is (true? (job/claim-expired? m :timeout-hours 1)))))

  (testing "claim-expired? with explicit now parameter"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m (-> (test-mote)
                (assoc :claimed-by "agent-1")
                (assoc :claimed-at claimed-time))
          ;; 23 hours later - not expired with 24h timeout
          now-23h (.plus base-instant (java.time.Duration/ofHours 23))
          ;; 25 hours later - expired with 24h timeout
          now-25h (.plus base-instant (java.time.Duration/ofHours 25))]
      (is (false? (job/claim-expired? m :now now-23h)))
      (is (true? (job/claim-expired? m :now now-25h)))))

  (testing "claim-expired? boundary condition at exactly 24 hours"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m (-> (test-mote)
                (assoc :claimed-by "agent-1")
                (assoc :claimed-at claimed-time))
          ;; Exactly 24 hours later - NOT expired (boundary is exclusive)
          now-exactly-24h (.plus base-instant (java.time.Duration/ofHours 24))]
      (is (false? (job/claim-expired? m :now now-exactly-24h)))))

  (testing "claim-expired? boundary condition 1ms after 24 hours"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m (-> (test-mote)
                (assoc :claimed-by "agent-1")
                (assoc :claimed-at claimed-time))
          ;; 24 hours + 1ms - expired
          now-just-after (.plusMillis (.plus base-instant (java.time.Duration/ofHours 24)) 1)]
      (is (true? (job/claim-expired? m :now now-just-after))))))

(deftest default-timeout-hours-test
  (testing "*default-timeout-hours* is 24"
    (is (= 24 job/*default-timeout-hours*)))

  (testing "*default-timeout-hours* can be rebound"
    (binding [job/*default-timeout-hours* 1]
      (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 2 60 60 1000))) ;; 2 hours ago
            m (-> (test-mote)
                  (assoc :claimed-by "agent-1")
                  (assoc :claimed-at old-time))]
        ;; With 1-hour default timeout, 2-hour old claim is expired
        (is (true? (job/claim-expired? m)))))))

;; =============================================================================
;; filter-expired-claims Tests
;; =============================================================================

(deftest filter-expired-claims-empty-test
  (testing "Empty collection returns empty sequence"
    (is (empty? (job/filter-expired-claims [])))
    (is (empty? (job/filter-expired-claims {})))))

(deftest filter-expired-claims-no-claims-test
  (testing "Motes without claims are not returned"
    (let [m1 (test-mote :id "1")
          m2 (test-mote :id "2")
          motes {"1" m1 "2" m2}]
      (is (empty? (job/filter-expired-claims motes))))))

(deftest filter-expired-claims-fresh-claims-test
  (testing "Motes with fresh claims are not returned"
    (let [m1 (mote/set-claimed-by (test-mote :id "1") "agent-1")
          m2 (mote/set-claimed-by (test-mote :id "2") "agent-2")
          motes {"1" m1 "2" m2}]
      (is (empty? (job/filter-expired-claims motes))))))

(deftest filter-expired-claims-expired-claims-test
  (testing "Motes with expired claims are returned"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000))) ;; 25 hours ago
          m1 (test-mote :id "1") ;; No claim
          m2 (-> (test-mote :id "2")
                 (assoc :claimed-by "stale-agent")
                 (assoc :claimed-at old-time))
          m3 (mote/set-claimed-by (test-mote :id "3") "active-agent") ;; Fresh claim
          motes {"1" m1 "2" m2 "3" m3}
          expired (job/filter-expired-claims motes)]
      (is (= 1 (count expired)))
      (is (= "2" (:id (first expired)))))))

(deftest filter-expired-claims-custom-timeout-test
  (testing "filter-expired-claims respects custom timeout-hours"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 2 60 60 1000))) ;; 2 hours ago
          m1 (-> (test-mote :id "1")
                 (assoc :claimed-by "agent-1")
                 (assoc :claimed-at old-time))
          motes {"1" m1}]
      ;; Not expired with 4-hour timeout
      (is (empty? (job/filter-expired-claims motes :timeout-hours 4)))
      ;; Expired with 1-hour timeout
      (is (= 1 (count (job/filter-expired-claims motes :timeout-hours 1)))))))

(deftest filter-expired-claims-vector-input-test
  (testing "filter-expired-claims works with vector input"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000)))
          m1 (test-mote :id "1")
          m2 (-> (test-mote :id "2")
                 (assoc :claimed-by "stale-agent")
                 (assoc :claimed-at old-time))
          expired (job/filter-expired-claims [m1 m2])]
      (is (= 1 (count expired)))
      (is (= "2" (:id (first expired)))))))

(deftest filter-expired-claims-with-now-test
  (testing "filter-expired-claims respects :now parameter"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m1 (-> (test-mote :id "1")
                 (assoc :claimed-by "agent-1")
                 (assoc :claimed-at claimed-time))
          motes {"1" m1}
          ;; 23 hours later - not expired
          now-23h (.plus base-instant (java.time.Duration/ofHours 23))
          ;; 25 hours later - expired
          now-25h (.plus base-instant (java.time.Duration/ofHours 25))]
      (is (empty? (job/filter-expired-claims motes :now now-23h)))
      (is (= 1 (count (job/filter-expired-claims motes :now now-25h)))))))

;; =============================================================================
;; filter-active-claims Tests
;; =============================================================================

(deftest filter-active-claims-empty-test
  (testing "Empty collection returns empty sequence"
    (is (empty? (job/filter-active-claims [])))
    (is (empty? (job/filter-active-claims {})))))

(deftest filter-active-claims-no-claims-test
  (testing "Motes without claims are not returned"
    (let [m1 (test-mote :id "1")
          m2 (test-mote :id "2")
          motes {"1" m1 "2" m2}]
      (is (empty? (job/filter-active-claims motes))))))

(deftest filter-active-claims-fresh-claims-test
  (testing "Motes with fresh claims are returned"
    (let [m1 (mote/set-claimed-by (test-mote :id "1") "agent-1")
          m2 (mote/set-claimed-by (test-mote :id "2") "agent-2")
          m3 (test-mote :id "3") ;; No claim
          motes {"1" m1 "2" m2 "3" m3}
          active (job/filter-active-claims motes)]
      (is (= 2 (count active)))
      (is (= #{"1" "2"} (set (map :id active)))))))

(deftest filter-active-claims-excludes-expired-test
  (testing "Motes with expired claims are not returned"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000))) ;; 25 hours ago
          m1 (mote/set-claimed-by (test-mote :id "1") "active-agent") ;; Fresh claim
          m2 (-> (test-mote :id "2")
                 (assoc :claimed-by "stale-agent")
                 (assoc :claimed-at old-time)) ;; Expired claim
          motes {"1" m1 "2" m2}
          active (job/filter-active-claims motes)]
      (is (= 1 (count active)))
      (is (= "1" (:id (first active)))))))

(deftest filter-active-claims-custom-timeout-test
  (testing "filter-active-claims respects custom timeout-hours"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 2 60 60 1000))) ;; 2 hours ago
          m1 (-> (test-mote :id "1")
                 (assoc :claimed-by "agent-1")
                 (assoc :claimed-at old-time))
          motes {"1" m1}]
      ;; Active with 4-hour timeout
      (is (= 1 (count (job/filter-active-claims motes :timeout-hours 4))))
      ;; Not active with 1-hour timeout
      (is (empty? (job/filter-active-claims motes :timeout-hours 1))))))

;; =============================================================================
;; workable? with claim-timeout-hours Tests
;; =============================================================================

(deftest workable-claim-timeout-hours-test
  (testing "claim-timeout-hours takes precedence over claim-timeout"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 90 60 1000))) ;; 90 minutes ago
          m (-> (test-mote :status :fixed :taint #{:needs-verification})
                (assoc :claimed-by "agent")
                (assoc :claimed-at old-time))]
      ;; claim-timeout=30 would make it workable (90 > 30 minutes)
      ;; claim-timeout-hours=2 would make it NOT workable (90 < 120 minutes)
      ;; claim-timeout-hours should take precedence
      (is (false? (job/workable? m :claim-timeout 30 :claim-timeout-hours 2)))))

  (testing "claim-timeout-hours=1 makes hour-old claim expired"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 90 60 1000))) ;; 90 minutes ago
          m (-> (test-mote :status :fixed :taint #{:needs-verification})
                (assoc :claimed-by "agent")
                (assoc :claimed-at old-time))]
      (is (true? (job/workable? m :claim-timeout-hours 1)))))

  (testing "claim-timeout-hours=24 makes day-old claim expired"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000))) ;; 25 hours ago
          m (-> (test-mote :status :fixed :taint #{:needs-verification})
                (assoc :claimed-by "agent")
                (assoc :claimed-at old-time))]
      (is (true? (job/workable? m :claim-timeout-hours 24)))))

  (testing "workable? with :now parameter for deterministic testing"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m (-> (test-mote :status :fixed :taint #{:needs-verification})
                (assoc :claimed-by "agent")
                (assoc :claimed-at claimed-time))
          now-23h (.plus base-instant (java.time.Duration/ofHours 23))
          now-25h (.plus base-instant (java.time.Duration/ofHours 25))]
      (is (false? (job/workable? m :claim-timeout-hours 24 :now now-23h)))
      (is (true? (job/workable? m :claim-timeout-hours 24 :now now-25h))))))

;; =============================================================================
;; select-jobs with claim-timeout-hours Tests
;; =============================================================================

(deftest select-jobs-claim-timeout-hours-test
  (testing "select-jobs with claim-timeout-hours includes expired claims"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 25 60 60 1000))) ;; 25 hours ago
          m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (-> (test-mote :id "2" :taint #{:needs-verification})
                 (assoc :claimed-by "stale-agent")
                 (assoc :claimed-at old-time))
          motes {"1" m1 "2" m2}]
      ;; Without timeout: only m1
      (is (= ["1"] (mapv :mote-id (job/select-jobs motes :max 10))))
      ;; With 24-hour timeout: both (m2's claim expired)
      (is (= #{"1" "2"} (set (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout-hours 24)))))))

  (testing "select-jobs claim-timeout-hours takes precedence over claim-timeout"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 90 60 1000))) ;; 90 minutes ago
          m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (-> (test-mote :id "2" :taint #{:needs-verification})
                 (assoc :claimed-by "agent")
                 (assoc :claimed-at old-time))
          motes {"1" m1 "2" m2}]
      ;; claim-timeout=30 would make m2 available
      ;; claim-timeout-hours=2 would keep m2 unavailable
      (is (= ["1"] (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout 30 :claim-timeout-hours 2))))))

  (testing "select-jobs with :now parameter for deterministic testing"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          m1 (test-mote :id "1" :taint #{:needs-verification})
          m2 (-> (test-mote :id "2" :taint #{:needs-verification})
                 (assoc :claimed-by "agent")
                 (assoc :claimed-at claimed-time))
          motes {"1" m1 "2" m2}
          now-23h (.plus base-instant (java.time.Duration/ofHours 23))
          now-25h (.plus base-instant (java.time.Duration/ofHours 25))]
      ;; At 23 hours: m2's claim not expired
      (is (= ["1"] (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout-hours 24 :now now-23h))))
      ;; At 25 hours: m2's claim expired
      (is (= #{"1" "2"} (set (mapv :mote-id (job/select-jobs motes :max 10 :claim-timeout-hours 24 :now now-25h))))))))

;; =============================================================================
;; Integration: Abandoned Job Recovery Workflow
;; =============================================================================

(deftest abandoned-job-recovery-workflow-test
  (testing "Workflow: claimed job becomes available after timeout"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          ;; Agent claims a job
          claimed-time (java.util.Date/from base-instant)
          m (-> (test-mote :id "1" :taint #{:needs-verification} :priority :p0)
                (assoc :claimed-by "agent-alice")
                (assoc :claimed-at claimed-time))
          motes {"1" m}

          ;; At claim time: job is NOT available (actively claimed)
          now-0h base-instant

          ;; After 12 hours: still not available (within 24h timeout)
          now-12h (.plus base-instant (java.time.Duration/ofHours 12))

          ;; After 25 hours: job IS available (claim expired)
          now-25h (.plus base-instant (java.time.Duration/ofHours 25))]

      ;; Immediately after claim: not available
      (is (empty? (job/select-jobs motes :claim-timeout-hours 24 :now now-0h)))
      (is (= 1 (count (job/filter-active-claims motes :now now-0h))))
      (is (empty? (job/filter-expired-claims motes :now now-0h)))

      ;; At 12 hours: still not available
      (is (empty? (job/select-jobs motes :claim-timeout-hours 24 :now now-12h)))
      (is (= 1 (count (job/filter-active-claims motes :now now-12h))))
      (is (empty? (job/filter-expired-claims motes :now now-12h)))

      ;; At 25 hours: available for re-claiming
      (is (= 1 (count (job/select-jobs motes :claim-timeout-hours 24 :now now-25h))))
      (is (empty? (job/filter-active-claims motes :now now-25h)))
      (is (= 1 (count (job/filter-expired-claims motes :now now-25h))))))

  (testing "Workflow: multiple agents, mixed claim states"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          ;; Various claim states
          unclaimed-m (test-mote :id "1" :taint #{:needs-verification} :priority :p1)
          fresh-claim-m (-> (test-mote :id "2" :taint #{:needs-verification} :priority :p2)
                            (assoc :claimed-by "agent-bob")
                            (assoc :claimed-at (java.util.Date/from base-instant)))
          stale-claim-m (-> (test-mote :id "3" :taint #{:needs-verification} :priority :p0)
                            (assoc :claimed-by "agent-charlie")
                            (assoc :claimed-at (java.util.Date/from (.minus base-instant (java.time.Duration/ofHours 30)))))
          verified-m (test-mote :id "4" :taint #{:needs-verification} :priority :p0 :status :verified)
          motes {"1" unclaimed-m "2" fresh-claim-m "3" stale-claim-m "4" verified-m}

          now (.plus base-instant (java.time.Duration/ofHours 1))]

      ;; Available jobs: unclaimed + expired claim (not fresh claim, not verified)
      (let [jobs (job/select-jobs motes :max 10 :claim-timeout-hours 24 :now now)]
        (is (= 2 (count jobs)))
        ;; Sorted by priority: p0 (stale-claim) then p1 (unclaimed)
        (is (= ["3" "1"] (mapv :mote-id jobs))))

      ;; Active claims: only the fresh one
      (is (= ["2"] (mapv :id (job/filter-active-claims motes :now now))))

      ;; Expired claims: the 30-hour old one
      (is (= ["3"] (mapv :id (job/filter-expired-claims motes :now now)))))))
