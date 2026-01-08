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
