(ns alethfeld.fsm.schema-test
  "Tests for FSM state and transition schema definitions.

   FSM has 11 states with 2 terminal states (:complete, :escalated).
   Transitions are validated against the transition matrix."
  (:require [clojure.test :refer [deftest testing is are]]
            [malli.core :as m]
            [alethfeld.fsm.schema :as fsm]))

;; =============================================================================
;; State Enum Tests
;; =============================================================================

(deftest workflow-phase-enum-test
  (testing "All 11 workflow phases are valid"
    (are [phase] (m/validate fsm/WorkflowPhase phase)
      :init
      :theorem-audit
      :strategy
      :skeleton
      :skeleton-review
      :decomposition
      :expand-verify-loop
      :reference-check
      :finalization
      :complete
      :escalated))

  (testing "Invalid phases are rejected"
    (are [phase] (not (m/validate fsm/WorkflowPhase phase))
      :invalid
      :planning
      :done
      nil
      "init"
      :Init)))

;; =============================================================================
;; Terminal State Tests
;; =============================================================================

(deftest terminal-states-test
  (testing "Terminal states are :complete and :escalated"
    (is (= #{:complete :escalated} fsm/terminal-states)))

  (testing "terminal? predicate works correctly"
    (is (fsm/terminal? :complete))
    (is (fsm/terminal? :escalated))
    (is (not (fsm/terminal? :init)))
    (is (not (fsm/terminal? :expand-verify-loop)))))

(deftest initial-state-test
  (testing "Initial state is :init"
    (is (= :init fsm/initial-state))))

;; =============================================================================
;; Transition Matrix Tests
;; =============================================================================

(deftest transition-matrix-completeness-test
  (testing "Every non-terminal state has at least one valid transition"
    (doseq [phase (m/children fsm/WorkflowPhase)]
      (when-not (fsm/terminal? phase)
        (is (seq (get fsm/transitions phase))
            (str "State " phase " should have at least one valid transition"))))))

(deftest transition-matrix-structure-test
  (testing "Transition matrix covers all non-terminal states"
    (let [non-terminal (remove fsm/terminal? (m/children fsm/WorkflowPhase))]
      (is (= (set non-terminal) (set (keys fsm/transitions)))))))

;; =============================================================================
;; Valid Transition Tests (per spec)
;; =============================================================================

(deftest init-transitions-test
  (testing ":init transitions"
    (is (= [:theorem-audit] (fsm/transitions :init)))
    (is (fsm/valid-transition? :init :theorem-audit))
    (is (not (fsm/valid-transition? :init :strategy)))
    (is (not (fsm/valid-transition? :init :complete)))))

(deftest theorem-audit-transitions-test
  (testing ":theorem-audit transitions"
    (is (= (set (fsm/transitions :theorem-audit)) #{:strategy :escalated}))
    (is (fsm/valid-transition? :theorem-audit :strategy))
    (is (fsm/valid-transition? :theorem-audit :escalated))
    (is (not (fsm/valid-transition? :theorem-audit :init)))
    (is (not (fsm/valid-transition? :theorem-audit :skeleton)))))

(deftest strategy-transitions-test
  (testing ":strategy transitions (including self-loop)"
    (is (= (set (fsm/transitions :strategy)) #{:strategy :skeleton :escalated}))
    (is (fsm/valid-transition? :strategy :strategy) "Self-loop allowed for retry")
    (is (fsm/valid-transition? :strategy :skeleton))
    (is (fsm/valid-transition? :strategy :escalated))
    (is (not (fsm/valid-transition? :strategy :theorem-audit)))))

(deftest skeleton-transitions-test
  (testing ":skeleton transitions"
    (is (= [:skeleton-review] (fsm/transitions :skeleton)))
    (is (fsm/valid-transition? :skeleton :skeleton-review))
    (is (not (fsm/valid-transition? :skeleton :decomposition)))))

(deftest skeleton-review-transitions-test
  (testing ":skeleton-review transitions"
    (is (= (set (fsm/transitions :skeleton-review)) #{:decomposition :skeleton :escalated}))
    (is (fsm/valid-transition? :skeleton-review :decomposition))
    (is (fsm/valid-transition? :skeleton-review :skeleton) "Can return to skeleton for revision")
    (is (fsm/valid-transition? :skeleton-review :escalated))))

(deftest decomposition-transitions-test
  (testing ":decomposition transitions"
    (is (= [:expand-verify-loop] (fsm/transitions :decomposition)))
    (is (fsm/valid-transition? :decomposition :expand-verify-loop))
    (is (not (fsm/valid-transition? :decomposition :reference-check)))))

(deftest expand-verify-loop-transitions-test
  (testing ":expand-verify-loop transitions"
    (is (= (set (fsm/transitions :expand-verify-loop)) #{:decomposition :reference-check :escalated}))
    (is (fsm/valid-transition? :expand-verify-loop :decomposition) "Can return for more decomposition")
    (is (fsm/valid-transition? :expand-verify-loop :reference-check))
    (is (fsm/valid-transition? :expand-verify-loop :escalated))))

(deftest reference-check-transitions-test
  (testing ":reference-check transitions"
    (is (= (set (fsm/transitions :reference-check)) #{:expand-verify-loop :finalization}))
    (is (fsm/valid-transition? :reference-check :expand-verify-loop) "Can return on mismatch")
    (is (fsm/valid-transition? :reference-check :finalization))
    (is (not (fsm/valid-transition? :reference-check :complete)))))

(deftest finalization-transitions-test
  (testing ":finalization transitions"
    (is (= [:complete] (fsm/transitions :finalization)))
    (is (fsm/valid-transition? :finalization :complete))
    (is (not (fsm/valid-transition? :finalization :escalated)))))

(deftest terminal-transitions-test
  (testing "Terminal states have no transitions"
    (is (nil? (fsm/transitions :complete)))
    (is (nil? (fsm/transitions :escalated)))
    (is (not (fsm/valid-transition? :complete :init)))
    (is (not (fsm/valid-transition? :escalated :init)))))

;; =============================================================================
;; valid-transition? edge cases
;; =============================================================================

(deftest valid-transition-edge-cases-test
  (testing "Invalid states return false"
    (is (not (fsm/valid-transition? :invalid :init)))
    (is (not (fsm/valid-transition? :init :invalid)))
    (is (not (fsm/valid-transition? nil :init)))
    (is (not (fsm/valid-transition? :init nil)))))

;; =============================================================================
;; Utility Function Tests
;; =============================================================================

(deftest all-phases-test
  (testing "all-phases returns all 11 phases"
    (is (= 11 (count fsm/all-phases)))
    (is (set? fsm/all-phases))
    (is (contains? fsm/all-phases :init))
    (is (contains? fsm/all-phases :complete))))

(deftest non-terminal-phases-test
  (testing "non-terminal-phases excludes terminal states"
    (is (= 9 (count fsm/non-terminal-phases)))
    (is (not (contains? fsm/non-terminal-phases :complete)))
    (is (not (contains? fsm/non-terminal-phases :escalated)))
    (is (contains? fsm/non-terminal-phases :init))))

(deftest valid-targets-test
  (testing "valid-targets returns set of valid target states"
    (is (= #{:theorem-audit} (fsm/valid-targets :init)))
    (is (= #{:strategy :escalated} (fsm/valid-targets :theorem-audit)))
    (is (= #{} (fsm/valid-targets :complete)))
    (is (= #{} (fsm/valid-targets :invalid)))))

;; =============================================================================
;; Phase Order Tests (for display/iteration)
;; =============================================================================

(deftest phase-order-test
  (testing "Phases have a defined linear order for display"
    (is (vector? fsm/phase-order))
    (is (= 11 (count fsm/phase-order)))
    (is (= :init (first fsm/phase-order)))
    (is (= :escalated (last fsm/phase-order)))
    (is (= :complete (nth fsm/phase-order 9)))))
