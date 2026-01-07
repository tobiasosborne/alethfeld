(ns alethfeld.fsm.core-test
  "Tests for FSM core operations.

   Tests cover:
   - get-phase: Extract current phase from graph
   - can-transition?: Validate transition against matrix
   - transition!: Perform state transition with history
   - get-valid-transitions: List valid targets from current state"
  (:require [clojure.test :refer [deftest testing is are]]
            [alethfeld.fsm.core :as fsm]
            [alethfeld.fsm.schema :as fsm-schema]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(defn make-graph-with-fsm
  "Create a test graph with FSM state."
  [phase & {:keys [history previous-phase]
            :or {history []
                 previous-phase nil}}]
  (assoc (f/make-graph [])
         :fsm {:phase phase
               :phase-entered-at "2024-01-01T12:00:00Z"
               :previous-phase previous-phase
               :history history}))

;; =============================================================================
;; get-phase Tests
;; =============================================================================

(deftest get-phase-test
  (testing "Returns phase from graph with FSM state"
    (is (= :init (fsm/get-phase (make-graph-with-fsm :init))))
    (is (= :theorem-audit (fsm/get-phase (make-graph-with-fsm :theorem-audit))))
    (is (= :expand-verify-loop (fsm/get-phase (make-graph-with-fsm :expand-verify-loop))))
    (is (= :complete (fsm/get-phase (make-graph-with-fsm :complete)))))

  (testing "Returns :init for graph without FSM state"
    (is (= :init (fsm/get-phase (f/make-graph []))))
    (is (= :init (fsm/get-phase f/minimal-valid-graph))))

  (testing "Returns :init for nil or empty map"
    (is (= :init (fsm/get-phase nil)))
    (is (= :init (fsm/get-phase {})))))

;; =============================================================================
;; can-transition? Tests
;; =============================================================================

(deftest can-transition-from-init-test
  (testing ":init can only transition to :theorem-audit"
    (let [g (make-graph-with-fsm :init)]
      (is (fsm/can-transition? g :theorem-audit))
      (is (not (fsm/can-transition? g :strategy)))
      (is (not (fsm/can-transition? g :complete)))
      (is (not (fsm/can-transition? g :init))))))

(deftest can-transition-from-theorem-audit-test
  (testing ":theorem-audit can transition to :strategy or :escalated"
    (let [g (make-graph-with-fsm :theorem-audit)]
      (is (fsm/can-transition? g :strategy))
      (is (fsm/can-transition? g :escalated))
      (is (not (fsm/can-transition? g :init)))
      (is (not (fsm/can-transition? g :skeleton))))))

(deftest can-transition-with-self-loop-test
  (testing ":strategy allows self-loop"
    (let [g (make-graph-with-fsm :strategy)]
      (is (fsm/can-transition? g :strategy))
      (is (fsm/can-transition? g :skeleton))
      (is (fsm/can-transition? g :escalated)))))

(deftest can-transition-terminal-states-test
  (testing "Terminal states cannot transition"
    (let [g-complete (make-graph-with-fsm :complete)
          g-escalated (make-graph-with-fsm :escalated)]
      (is (not (fsm/can-transition? g-complete :init)))
      (is (not (fsm/can-transition? g-complete :theorem-audit)))
      (is (not (fsm/can-transition? g-escalated :init)))
      (is (not (fsm/can-transition? g-escalated :theorem-audit))))))

(deftest can-transition-graph-without-fsm-test
  (testing "Graph without FSM state treated as :init"
    (let [g (f/make-graph [])]
      (is (fsm/can-transition? g :theorem-audit))
      (is (not (fsm/can-transition? g :strategy))))))

(deftest can-transition-invalid-target-test
  (testing "Invalid target phases return false"
    (let [g (make-graph-with-fsm :init)]
      (is (not (fsm/can-transition? g :invalid)))
      (is (not (fsm/can-transition? g nil)))
      (is (not (fsm/can-transition? g "theorem-audit"))))))

;; =============================================================================
;; transition! Tests
;; =============================================================================

(deftest transition-success-test
  (testing "Valid transition returns success result"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :theorem-audit "Starting theorem audit")]
      (is (:ok result))
      (is (= :theorem-audit (fsm/get-phase (:ok result))))
      (is (= :init (get-in result [:ok :fsm :previous-phase]))))))

(deftest transition-updates-version-test
  (testing "Transition increments graph version"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :theorem-audit "test")]
      (is (= 2 (:version (:ok result)))))))

(deftest transition-records-history-test
  (testing "Transition appends to history"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :theorem-audit "Starting audit")
          history (get-in result [:ok :fsm :history])]
      (is (= 1 (count history)))
      (is (= :init (:from (first history))))
      (is (= :theorem-audit (:to (first history))))
      (is (= "Starting audit" (:reason (first history))))
      (is (some? (:at (first history)))))))

(deftest transition-preserves-history-test
  (testing "Multiple transitions accumulate history"
    (let [g1 (make-graph-with-fsm :init)
          r1 (fsm/transition! g1 :theorem-audit "first")
          r2 (fsm/transition! (:ok r1) :strategy "second")
          r3 (fsm/transition! (:ok r2) :skeleton "third")
          history (get-in r3 [:ok :fsm :history])]
      (is (= 3 (count history)))
      (is (= [:init :theorem-audit :strategy] (mapv :from history)))
      (is (= [:theorem-audit :strategy :skeleton] (mapv :to history))))))

(deftest transition-invalid-returns-error-test
  (testing "Invalid transition returns error"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :strategy "Invalid")]
      (is (:error result))
      (is (= :invalid-transition (get-in result [:error 0 :type])))))

  (testing "Transition from terminal state returns error"
    (let [g (make-graph-with-fsm :complete)
          result (fsm/transition! g :init "Cannot restart")]
      (is (:error result))
      (is (= :invalid-transition (get-in result [:error 0 :type]))))))

(deftest transition-invalid-target-error-test
  (testing "Invalid target phase returns error"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :invalid "Bad target")]
      (is (:error result))
      (is (= :invalid-phase (get-in result [:error 0 :type]))))))

(deftest transition-self-loop-test
  (testing "Self-loop transitions work correctly"
    (let [g (make-graph-with-fsm :strategy)
          result (fsm/transition! g :strategy "Retry with new approach")]
      (is (:ok result))
      (is (= :strategy (fsm/get-phase (:ok result))))
      (is (= :strategy (get-in result [:ok :fsm :previous-phase]))))))

(deftest transition-adds-fsm-to-legacy-graph-test
  (testing "Transition adds FSM state to graph without it"
    (let [g (f/make-graph [])
          result (fsm/transition! g :theorem-audit "Initialize FSM")]
      (is (:ok result))
      (is (some? (get-in result [:ok :fsm])))
      (is (= :theorem-audit (fsm/get-phase (:ok result))))
      (is (= :init (get-in result [:ok :fsm :previous-phase]))))))

;; =============================================================================
;; get-valid-transitions Tests
;; =============================================================================

(deftest get-valid-transitions-test
  (testing "Returns valid targets for each phase"
    (is (= #{:theorem-audit} (set (fsm/get-valid-transitions (make-graph-with-fsm :init)))))
    (is (= #{:strategy :escalated} (set (fsm/get-valid-transitions (make-graph-with-fsm :theorem-audit)))))
    (is (= #{:strategy :skeleton :escalated} (set (fsm/get-valid-transitions (make-graph-with-fsm :strategy)))))
    (is (= #{:skeleton-review} (set (fsm/get-valid-transitions (make-graph-with-fsm :skeleton)))))
    (is (= #{:decomposition :skeleton :escalated} (set (fsm/get-valid-transitions (make-graph-with-fsm :skeleton-review)))))
    (is (= #{:expand-verify-loop} (set (fsm/get-valid-transitions (make-graph-with-fsm :decomposition)))))
    (is (= #{:decomposition :reference-check :escalated} (set (fsm/get-valid-transitions (make-graph-with-fsm :expand-verify-loop)))))
    (is (= #{:expand-verify-loop :finalization} (set (fsm/get-valid-transitions (make-graph-with-fsm :reference-check)))))
    (is (= #{:complete} (set (fsm/get-valid-transitions (make-graph-with-fsm :finalization)))))))

(deftest get-valid-transitions-terminal-test
  (testing "Terminal states return empty list"
    (is (empty? (fsm/get-valid-transitions (make-graph-with-fsm :complete))))
    (is (empty? (fsm/get-valid-transitions (make-graph-with-fsm :escalated))))))

(deftest get-valid-transitions-legacy-graph-test
  (testing "Graph without FSM returns transitions from :init"
    (is (= [:theorem-audit] (fsm/get-valid-transitions (f/make-graph []))))))

;; =============================================================================
;; Phase Info Tests
;; =============================================================================

(deftest get-phase-info-test
  (testing "Returns comprehensive phase info"
    (let [g (make-graph-with-fsm :expand-verify-loop
                                 :previous-phase :decomposition
                                 :history [{:from :init :to :theorem-audit :at "t1" :reason "r1"}])
          info (fsm/get-phase-info g)]
      (is (= :expand-verify-loop (:phase info)))
      (is (= :decomposition (:previous-phase info)))
      (is (not (:terminal? info)))
      (is (= #{:decomposition :reference-check :escalated} (set (:valid-transitions info))))
      (is (= 1 (count (:history info)))))))

(deftest get-phase-info-terminal-test
  (testing "Terminal phase info shows terminal? true"
    (let [info (fsm/get-phase-info (make-graph-with-fsm :complete))]
      (is (:terminal? info))
      (is (empty? (:valid-transitions info))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest empty-reason-test
  (testing "Transition works with empty or nil reason"
    (let [g (make-graph-with-fsm :init)]
      (is (:ok (fsm/transition! g :theorem-audit "")))
      (is (:ok (fsm/transition! g :theorem-audit nil))))))

(deftest transition-updates-timestamps-test
  (testing "Transition updates phase-entered-at timestamp"
    (let [g (make-graph-with-fsm :init)
          result (fsm/transition! g :theorem-audit "test")
          new-time (get-in result [:ok :fsm :phase-entered-at])]
      (is (some? new-time))
      (is (not= "2024-01-01T12:00:00Z" new-time)))))
