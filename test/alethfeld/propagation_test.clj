(ns alethfeld.propagation-test
  "Tests for auto-propagation of verification votes."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [alethfeld.verify :as verify]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.session :as session]
            [babashka.fs :as fs]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *test-repo* nil)

(defn with-temp-repo [f]
  (let [temp-dir (str (fs/create-temp-dir {:prefix "alethfeld-prop-test-"}))]
    (try
      (store/init-repo! temp-dir :config {:project-name "Propagation Test"
                                          :version "0.1"
                                          :default-difficulty 3
                                          :vote-quorum 1  ; Use quorum=1 for easier testing
                                          :proposal-quorum 1
                                          :claim-timeout-minutes 30})
      (session/ensure-session-dirs! temp-dir)
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
  [id claim & {:keys [status taint difficulty priority parent children contributors]
               :or {status :fixed
                    taint #{:needs-verification}
                    difficulty 3
                    priority :p2
                    children []}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :status status
                          :taint taint
                          :difficulty difficulty
                          :priority priority
                          :parent parent
                          :children children
                          :contributors (or contributors {:created-by "test-agent"}))]
    (store/save-mote! *test-repo* m)
    m))

(defn create-tree!
  "Create a simple tree structure for testing propagation.

   Creates:
   - parent (1): with children [1.1, 1.2]
   - child1 (1.1): verified
   - child2 (1.2): fixed (needs verification)

   Returns map of mote-id -> mote."
  [& {:keys [parent-status parent-contributors child1-status child2-status]
      :or {parent-status :fixed
           parent-contributors {:created-by "proposer-1"}
           child1-status :verified
           child2-status :fixed}}]
  (let [parent (create-test-mote! "1" "Root claim"
                                  :status parent-status
                                  :taint (if (= parent-status :fixed)
                                           #{:needs-verification}
                                           #{})
                                  :children ["1.1" "1.2"]
                                  :contributors parent-contributors)
        child1 (create-test-mote! "1.1" "Child 1 claim"
                                  :status child1-status
                                  :taint (if (= child1-status :fixed)
                                           #{:needs-verification}
                                           #{})
                                  :parent "1")
        child2 (create-test-mote! "1.2" "Child 2 claim"
                                  :status child2-status
                                  :taint (if (= child2-status :fixed)
                                           #{:needs-verification}
                                           #{})
                                  :parent "1")]
    {"1" parent "1.1" child1 "1.2" child2}))

(defn create-deep-tree!
  "Create a deeper tree structure for multi-level propagation testing.

   Creates:
   - 1: root (fixed)
     - 1.1: verified
     - 1.2: fixed
       - 1.2.1: verified
       - 1.2.2: fixed (needs verification)

   Returns map of mote-id -> mote."
  []
  (let [root (create-test-mote! "1" "Root"
                                :status :fixed
                                :taint #{:needs-verification}
                                :children ["1.1" "1.2"]
                                :contributors {:created-by "proposer-1"})
        c1 (create-test-mote! "1.1" "Child 1"
                              :status :verified
                              :taint #{}
                              :parent "1")
        c2 (create-test-mote! "1.2" "Child 2"
                              :status :fixed
                              :taint #{:needs-verification}
                              :parent "1"
                              :children ["1.2.1" "1.2.2"]
                              :contributors {:created-by "proposer-2"})
        c21 (create-test-mote! "1.2.1" "Grandchild 1"
                               :status :verified
                               :taint #{}
                               :parent "1.2")
        c22 (create-test-mote! "1.2.2" "Grandchild 2"
                               :status :fixed
                               :taint #{:needs-verification}
                               :parent "1.2")]
    {"1" root "1.1" c1 "1.2" c2 "1.2.1" c21 "1.2.2" c22}))

;; -----------------------------------------------------------------------------
;; Pure Function Tests: all-siblings-verified?
;; -----------------------------------------------------------------------------

(deftest all-siblings-verified-test
  (testing "returns true when all siblings are verified"
    (create-tree! :child1-status :verified :child2-status :verified)
    (let [motes (store/load-all-motes *test-repo*)]
      (is (verify/all-siblings-verified? motes "1.1"))
      (is (verify/all-siblings-verified? motes "1.2"))))

  (testing "returns false when some siblings are not verified"
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [motes (store/load-all-motes *test-repo*)]
      ;; 1.1's sibling (1.2) is not verified
      (is (not (verify/all-siblings-verified? motes "1.1")))
      ;; 1.2's sibling (1.1) is verified
      (is (verify/all-siblings-verified? motes "1.2"))))

  (testing "returns nil for root motes (no parent)"
    (create-tree!)
    (let [motes (store/load-all-motes *test-repo*)]
      (is (nil? (verify/all-siblings-verified? motes "1")))))

  (testing "returns true for single child (no siblings)"
    (let [parent (create-test-mote! "2" "Parent with one child"
                                    :children ["2.1"])
          child (create-test-mote! "2.1" "Only child"
                                   :status :verified
                                   :parent "2")]
      (let [motes (store/load-all-motes *test-repo*)]
        ;; Single child has no siblings, so "all siblings verified" is true (vacuously)
        (is (verify/all-siblings-verified? motes "2.1"))))))

;; -----------------------------------------------------------------------------
;; Pure Function Tests: can-propagate-to-parent?
;; -----------------------------------------------------------------------------

(deftest can-propagate-to-parent-basic-test
  (testing "can propagate when all conditions met"
    (create-tree! :child1-status :verified :child2-status :verified)
    (let [motes (store/load-all-motes *test-repo*)]
      ;; verifier-1 is not a contributor to parent
      (is (verify/can-propagate-to-parent? motes "1" "verifier-1"))))

  (testing "cannot propagate when parent is not fixed"
    (create-tree! :parent-status :proposed :child1-status :verified :child2-status :verified)
    (let [motes (store/load-all-motes *test-repo*)]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))))

  (testing "cannot propagate when not all children verified"
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [motes (store/load-all-motes *test-repo*)]
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1"))))))

(deftest can-propagate-to-parent-contributor-test
  (testing "cannot propagate when agent is parent contributor"
    (create-tree! :child1-status :verified
                  :child2-status :verified
                  :parent-contributors {:created-by "verifier-1"})
    (let [motes (store/load-all-motes *test-repo*)]
      ;; verifier-1 created the parent, cannot vote on it
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))
      ;; verifier-2 can vote
      (is (verify/can-propagate-to-parent? motes "1" "verifier-2")))))

(deftest can-propagate-to-parent-already-voted-test
  (testing "cannot propagate when agent already voted on parent"
    ;; Use quorum=2 so parent stays :fixed after one vote
    (store/save-config! *test-repo* {:project-name "Test"
                                     :vote-quorum 2})
    (create-tree! :child1-status :verified :child2-status :verified)
    ;; Cast a vote on the parent (doesn't reach quorum yet)
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    (let [motes (store/load-all-motes *test-repo*)]
      ;; verifier-1 already voted
      (is (not (verify/can-propagate-to-parent? motes "1" "verifier-1")))
      ;; verifier-2 can still vote
      (is (verify/can-propagate-to-parent? motes "1" "verifier-2")))))

;; -----------------------------------------------------------------------------
;; Integration Tests: propagate-verification!
;; -----------------------------------------------------------------------------

(deftest propagate-simple-test
  (testing "propagates to parent when last sibling verified"
    (create-tree! :child1-status :verified :child2-status :fixed)
    ;; Verify child 1.2 (the last unverified sibling)
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Now propagate
    (let [propagated (verify/propagate-verification! *test-repo* "1.2" "verifier-1")]
      ;; Should have voted on parent
      (is (= ["1"] propagated))
      ;; Parent should now be verified (quorum=1)
      (let [parent (store/load-mote *test-repo* "1")]
        (is (= :verified (:status parent)))))))

(deftest propagate-stops-when-siblings-not-verified-test
  (testing "does not propagate when siblings not verified"
    (create-tree! :child1-status :fixed :child2-status :fixed)
    ;; Verify only child 1.2
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Try to propagate - should stop because 1.1 is not verified
    (let [propagated (verify/propagate-verification! *test-repo* "1.2" "verifier-1")]
      (is (empty? propagated))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *test-repo* "1")]
        (is (= :fixed (:status parent)))))))

(deftest propagate-stops-at-contributor-boundary-test
  (testing "stops when agent is contributor to ancestor"
    (create-tree! :child1-status :verified
                  :child2-status :fixed
                  :parent-contributors {:created-by "verifier-1"})
    ;; Verify child 1.2 as verifier-1
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Try to propagate - should stop because verifier-1 created the parent
    (let [propagated (verify/propagate-verification! *test-repo* "1.2" "verifier-1")]
      (is (empty? propagated))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *test-repo* "1")]
        (is (= :fixed (:status parent)))))))

(deftest propagate-multi-level-test
  (testing "propagates up multiple levels"
    (create-deep-tree!)
    ;; Verify the last grandchild (1.2.2)
    (verify/cast-vote! *test-repo* "1.2.2" "verifier-1" :for)
    ;; Propagate from 1.2.2
    (let [propagated (verify/propagate-verification! *test-repo* "1.2.2" "verifier-1")]
      ;; Should have voted on 1.2 and then on 1
      (is (= ["1.2" "1"] propagated))
      ;; Both should now be verified
      (let [c2 (store/load-mote *test-repo* "1.2")
            root (store/load-mote *test-repo* "1")]
        (is (= :verified (:status c2)))
        (is (= :verified (:status root)))))))

(deftest propagate-stops-at-root-test
  (testing "propagation stops at root (no parent)"
    ;; Create just a root mote with no children
    (create-test-mote! "1" "Root only"
                       :status :fixed
                       :taint #{:needs-verification}
                       :children [])
    ;; Verify the root
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    ;; Try to propagate - should return empty (root has no parent)
    (let [propagated (verify/propagate-verification! *test-repo* "1" "verifier-1")]
      (is (empty? propagated)))))

(deftest propagate-with-reason-test
  (testing "propagated votes include reason"
    (create-tree! :child1-status :verified :child2-status :fixed)
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Propagate with custom reason
    (verify/propagate-verification! *test-repo* "1.2" "verifier-1"
                                    :reason "All children verified")
    ;; Check the vote on parent
    (let [parent (store/load-mote *test-repo* "1")
          vote (first (:votes parent))]
      (is (= "All children verified" (:reason vote))))))

(deftest propagate-default-reason-test
  (testing "propagated votes use default reason when none provided"
    (create-tree! :child1-status :verified :child2-status :fixed)
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Propagate without reason
    (verify/propagate-verification! *test-repo* "1.2" "verifier-1")
    ;; Check the vote on parent
    (let [parent (store/load-mote *test-repo* "1")
          vote (first (:votes parent))]
      (is (= "Auto-propagated from children" (:reason vote))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest propagate-partial-tree-test
  (testing "propagation works with partially verified tree"
    ;; Create a more complex structure
    (let [root (create-test-mote! "1" "Root"
                                  :status :fixed
                                  :taint #{:needs-verification}
                                  :children ["1.1" "1.2" "1.3"]
                                  :contributors {:created-by "proposer-1"})
          c1 (create-test-mote! "1.1" "Child 1"
                                :status :verified
                                :taint #{}
                                :parent "1")
          c2 (create-test-mote! "1.2" "Child 2"
                                :status :verified
                                :taint #{}
                                :parent "1")
          c3 (create-test-mote! "1.3" "Child 3"
                                :status :fixed
                                :taint #{:needs-verification}
                                :parent "1")]
      ;; Verify the last child
      (verify/cast-vote! *test-repo* "1.3" "verifier-1" :for)
      ;; Propagate
      (let [propagated (verify/propagate-verification! *test-repo* "1.3" "verifier-1")]
        (is (= ["1"] propagated))
        (let [root (store/load-mote *test-repo* "1")]
          (is (= :verified (:status root))))))))

(deftest propagate-stops-at-pending-parent-test
  (testing "propagation stops when parent needs more votes (quorum not met)"
    ;; Set up repo with quorum=2
    (store/save-config! *test-repo* {:project-name "Test"
                                     :vote-quorum 2})
    (create-tree! :child1-status :verified :child2-status :fixed)
    ;; Verify child 1.2 with 2 votes (to meet quorum)
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    (verify/cast-vote! *test-repo* "1.2" "verifier-2" :for)
    ;; Now 1.2 is verified, propagate with verifier-1
    (let [propagated (verify/propagate-verification! *test-repo* "1.2" "verifier-1")]
      ;; Should have voted on parent, but parent not yet verified (needs 2 votes)
      (is (= ["1"] propagated))
      (let [parent (store/load-mote *test-repo* "1")]
        ;; Parent has 1 vote but is still fixed (not verified yet)
        (is (= :fixed (:status parent)))
        (is (= 1 (count (:votes parent))))))))

(deftest propagate-no-double-vote-test
  (testing "propagation does not double-vote if already voted"
    (create-tree! :child1-status :verified :child2-status :fixed)
    ;; Vote on parent first
    (verify/cast-vote! *test-repo* "1" "verifier-1" :for)
    ;; Now verify child 1.2
    (verify/cast-vote! *test-repo* "1.2" "verifier-1" :for)
    ;; Propagate - should not vote again on parent
    (let [propagated (verify/propagate-verification! *test-repo* "1.2" "verifier-1")]
      (is (empty? propagated))
      ;; Parent should still have only 1 vote
      (let [parent (store/load-mote *test-repo* "1")]
        (is (= 1 (count (:votes parent))))))))
