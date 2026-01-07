(ns alethfeld.fsm.core
  "FSM core operations for managing workflow state.

   Provides:
   - get-phase: Extract current phase from graph
   - can-transition?: Check if transition is valid
   - transition!: Perform state transition with history
   - get-valid-transitions: List valid targets from current state
   - get-phase-info: Get comprehensive phase information

   Graphs without FSM state are treated as being in :init phase.
   All transitions are validated against the FSM transition matrix."
  (:require [alethfeld.fsm.schema :as fsm-schema]
            [alethfeld.config :as config]))

;; =============================================================================
;; Phase Accessors
;; =============================================================================

(defn get-phase
  "Get the current workflow phase from a graph.

   Returns the phase keyword from [:fsm :phase].
   If graph has no FSM state or is nil, returns :init."
  [graph]
  (or (get-in graph [:fsm :phase])
      fsm-schema/initial-state))

(defn get-valid-transitions
  "Get list of valid target phases from current state.

   Returns a vector of phase keywords that are valid targets
   from the graph's current phase. Returns empty vector for
   terminal states."
  [graph]
  (let [phase (get-phase graph)]
    (vec (or (get fsm-schema/transitions phase) []))))

;; =============================================================================
;; Transition Validation
;; =============================================================================

(defn can-transition?
  "Check if transition from current phase to target is valid.

   Arguments:
   - graph: The proof graph
   - target: The target phase keyword

   Returns true if:
   - Current phase has valid transitions to target
   - Target is a valid phase keyword

   Returns false for:
   - Invalid target phases
   - Terminal states (no outbound transitions)
   - Transitions not in the matrix"
  [graph target]
  (and (some? target)
       (contains? fsm-schema/all-phases target)
       (fsm-schema/valid-transition? (get-phase graph) target)))

;; =============================================================================
;; State Transition
;; =============================================================================

(defn- make-history-entry
  "Create a history entry for a transition."
  [from-phase to-phase reason]
  {:from from-phase
   :to to-phase
   :at (config/current-iso8601)
   :reason (or reason "")})

(defn- initialize-fsm-state
  "Create initial FSM state map for a graph."
  [phase previous-phase timestamp]
  {:phase phase
   :phase-entered-at timestamp
   :previous-phase previous-phase
   :history []})

(defn transition!
  "Perform a state transition on the graph.

   Arguments:
   - graph: The proof graph
   - target: Target phase keyword
   - reason: Optional string explaining the transition

   Returns:
   - {:ok updated-graph} on success with:
     - Updated :fsm :phase
     - Updated :fsm :previous-phase
     - Updated :fsm :phase-entered-at
     - Appended history entry
     - Incremented :version
   - {:error [...]} on failure with error details

   Errors:
   - :invalid-phase - Target is not a valid phase keyword
   - :invalid-transition - Transition not allowed by matrix"
  [graph target reason]
  (let [current-phase (get-phase graph)]
    (cond
      ;; Check target is valid phase
      (not (contains? fsm-schema/all-phases target))
      {:error [{:type :invalid-phase
                :phase target
                :message (str "Invalid target phase: " target
                              ". Valid phases are: " (pr-str fsm-schema/all-phases))}]}

      ;; Check transition is allowed
      (not (fsm-schema/valid-transition? current-phase target))
      {:error [{:type :invalid-transition
                :from current-phase
                :to target
                :valid-targets (get fsm-schema/transitions current-phase [])
                :message (str "Cannot transition from " current-phase " to " target
                              ". Valid targets: " (pr-str (get fsm-schema/transitions current-phase [])))}]}

      ;; Perform transition
      :else
      (let [now (config/current-iso8601)
            history-entry (make-history-entry current-phase target reason)
            current-fsm (get graph :fsm)
            current-history (or (:history current-fsm) [])

            new-fsm (if current-fsm
                      ;; Update existing FSM state
                      (assoc current-fsm
                             :phase target
                             :previous-phase current-phase
                             :phase-entered-at now
                             :history (conj current-history history-entry))
                      ;; Initialize FSM state for legacy graphs
                      (assoc (initialize-fsm-state target current-phase now)
                             :history [history-entry]))

            updated-graph (-> graph
                              (assoc :fsm new-fsm)
                              (update :version inc))]
        {:ok updated-graph}))))

;; =============================================================================
;; Phase Information
;; =============================================================================

(defn get-phase-info
  "Get comprehensive information about the current phase.

   Returns a map with:
   - :phase - Current phase keyword
   - :previous-phase - Previous phase (nil if none)
   - :terminal? - Boolean, true if current phase is terminal
   - :valid-transitions - Vector of valid target phases
   - :phase-entered-at - ISO8601 timestamp (nil if no FSM state)
   - :history - Vector of transition history entries"
  [graph]
  (let [fsm-state (get graph :fsm)
        phase (get-phase graph)]
    {:phase phase
     :previous-phase (:previous-phase fsm-state)
     :terminal? (fsm-schema/terminal? phase)
     :valid-transitions (get-valid-transitions graph)
     :phase-entered-at (:phase-entered-at fsm-state)
     :history (or (:history fsm-state) [])}))
