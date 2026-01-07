(ns alethfeld.fsm.schema
  "FSM state and transition schema definitions for Alethfeld CLI.

   The workflow FSM has 11 states:
   - :init                 Initial state after graph creation
   - :theorem-audit        Adviser sanity-checks the theorem
   - :strategy             Evaluate proof approach
   - :skeleton             Create top-level proof structure
   - :skeleton-review      Adviser validates skeleton
   - :decomposition        Split into independent subproblems
   - :expand-verify-loop   Main loop: expand nodes, verify them
   - :reference-check      Verify external references
   - :finalization         Final validation before completion
   - :complete             Terminal: proof succeeded
   - :escalated            Terminal: proof requires human intervention

   Transitions are validated against a matrix that enforces:
   - Valid workflow progression
   - Allowed self-loops (e.g., :strategy -> :strategy for retry)
   - Backward transitions where appropriate (e.g., :reference-check -> :expand-verify-loop)
   - No transitions from terminal states"
  (:require [malli.core :as m]))

;; =============================================================================
;; Phase Order (canonical ordering for display/iteration)
;; =============================================================================

(def phase-order
  "Canonical ordering of all workflow phases.
   Used for display, iteration, and progress visualization."
  [:init
   :theorem-audit
   :strategy
   :skeleton
   :skeleton-review
   :decomposition
   :expand-verify-loop
   :reference-check
   :finalization
   :complete
   :escalated])

;; =============================================================================
;; State Enum Schema
;; =============================================================================

(def WorkflowPhase
  "All valid workflow phases (states) in the FSM.
   Terminal states: :complete, :escalated"
  [:enum {:error/message
          (str "Invalid workflow phase. Must be one of: "
               (clojure.string/join ", " (map name phase-order)))}
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
   :escalated])

;; =============================================================================
;; State Sets
;; =============================================================================

(def terminal-states
  "Set of terminal states (no transitions allowed from these)"
  #{:complete :escalated})

(def all-phases
  "Set of all valid phases"
  (set phase-order))

(def non-terminal-phases
  "Set of phases that are not terminal (have valid transitions)"
  (clojure.set/difference all-phases terminal-states))

(def initial-state
  "The initial state for all new graphs"
  :init)

;; =============================================================================
;; Transition Matrix
;; =============================================================================

(def transitions
  "Valid transitions from each non-terminal state.
   Maps state -> vector of valid target states.

   Transition rules from spec:
   - :init -> :theorem-audit (always)
   - :theorem-audit -> :strategy (proceed/verify-first) | :escalated (refuse/suspicious)
   - :strategy -> :strategy (flawed, retry) | :skeleton (promising/risky) | :escalated (doomed/limit)
   - :skeleton -> :skeleton-review (depth-1 nodes exist)
   - :skeleton-review -> :decomposition (promising/risky) | :skeleton (flawed, retry) | :escalated (doomed/limit)
   - :decomposition -> :expand-verify-loop (always after analysis)
   - :expand-verify-loop -> :decomposition (subgraphs available) | :reference-check (queues empty) | :escalated (limit)
   - :reference-check -> :expand-verify-loop (mismatch) | :finalization (all verified)
   - :finalization -> :complete (all checks pass)"
  {:init              [:theorem-audit]
   :theorem-audit     [:strategy :escalated]
   :strategy          [:strategy :skeleton :escalated]
   :skeleton          [:skeleton-review]
   :skeleton-review   [:decomposition :skeleton :escalated]
   :decomposition     [:expand-verify-loop]
   :expand-verify-loop [:decomposition :reference-check :escalated]
   :reference-check   [:expand-verify-loop :finalization]
   :finalization      [:complete]})

;; =============================================================================
;; Transition Predicates
;; =============================================================================

(defn terminal?
  "Returns true if phase is a terminal state"
  [phase]
  (contains? terminal-states phase))

(defn valid-transition?
  "Returns true if transitioning from `from` to `to` is valid.
   Returns false for:
   - Invalid/nil states
   - Transitions from terminal states
   - Transitions not in the transition matrix"
  [from to]
  (and (some? from)
       (some? to)
       (contains? all-phases from)
       (contains? all-phases to)
       (boolean (some #{to} (get transitions from)))))

(defn valid-targets
  "Returns set of valid target states from the given state.
   Returns empty set for terminal states or invalid states."
  [from]
  (if (and (some? from) (contains? all-phases from))
    (set (get transitions from []))
    #{}))
