(ns alethfeld.job
  "Job selection and role derivation functions."
  (:require [alethfeld.schema :as s]))

;; -----------------------------------------------------------------------------
;; Taint → Role Mapping
;; -----------------------------------------------------------------------------

(def ^:private taint->role
  "Maps taint flags to the role that handles them."
  {:needs-decomposition   :proposer
   :needs-proposal-review :advisor
   :needs-refinement      :prover
   :needs-verification    :verifier
   :needs-refs            :ref-checker
   :needs-counterexample  :counterexample})

;; Note: :needs-votes is not mapped to a role - it's a status indicator
;; that quorum hasn't been reached yet.

(def ^:private role-priority
  "Priority order for roles when selecting primary role.
   Lower number = higher priority."
  {:advisor        0  ; Review proposals first
   :proposer       1  ; Then decompose
   :prover         2  ; Then refine
   :verifier       3  ; Then verify
   :ref-checker    4  ; Then check refs
   :counterexample 5}) ; Adversarial check last

;; -----------------------------------------------------------------------------
;; Role Derivation
;; -----------------------------------------------------------------------------

(defn mote->roles
  "Derive the set of roles that can work on this mote based on its taint flags.

   Returns a set of roles, or empty set if no work is needed."
  [mote]
  (let [taints (:taint mote)]
    (into #{} (keep taint->role taints))))

(defn mote->role
  "Derive the primary role for this mote based on taint flags.

   When multiple taints are present, returns the highest-priority role
   (advisor > proposer > prover > verifier > ref-checker > counterexample).

   Returns nil if no role-mapped taints are present."
  [mote]
  (let [roles (mote->roles mote)]
    (when (seq roles)
      (first (sort-by role-priority roles)))))

;; -----------------------------------------------------------------------------
;; Workability Check
;; -----------------------------------------------------------------------------

(def ^:private terminal-statuses
  "Statuses that indicate a mote is no longer workable."
  #{:verified :rejected :refuted})

(defn workable?
  "Check if a mote needs work.

   A mote is workable if:
   - Its status is not terminal (verified, rejected, refuted)
   - It is not currently claimed
   - It has at least one taint flag that maps to a role

   Note: Does not check claim expiration (that requires config)."
  [mote]
  (boolean
   (and (not (terminal-statuses (:status mote)))
        (nil? (:claimed-by mote))
        (seq (mote->roles mote)))))

;; -----------------------------------------------------------------------------
;; Priority/Difficulty Helpers
;; -----------------------------------------------------------------------------

(def ^:private priority-rank
  "Numeric rank for priorities (lower = more urgent)."
  {:p0 0 :p1 1 :p2 2 :p3 3 :p4 4})

(defn- priority<=
  "Check if priority a is <= priority b (a is same or more urgent)."
  [a b]
  (<= (priority-rank a) (priority-rank b)))

(defn- in-difficulty-range?
  "Check if difficulty is within range.
   Range can be:
   - Single int: exact match
   - [min max] tuple: inclusive range"
  [difficulty range-spec]
  (if (vector? range-spec)
    (let [[min-d max-d] range-spec]
      (<= min-d difficulty max-d))
    (= difficulty range-spec)))

(defn- in-priority-range?
  "Check if priority is within range.
   Range can be:
   - Single priority: exact match
   - [min max] tuple: inclusive range (p0 is 'smaller' than p4)

   Example: [:p1 :p3] matches :p1, :p2, :p3"
  [priority range-spec]
  (if (vector? range-spec)
    (let [[min-p max-p] range-spec]
      (and (priority<= min-p priority)
           (priority<= priority max-p)))
    (= priority range-spec)))

;; -----------------------------------------------------------------------------
;; Filter Matching
;; -----------------------------------------------------------------------------

(defn matches-filter?
  "Check if a mote matches the given ReadyOptions filter.

   Options:
   - :role - Mote must have this role in its taint-derived roles
   - :difficulty - Mote difficulty must match (exact or range)
   - :priority - Mote priority must match (exact or range)

   Other options (:agent, :max, :no-claim, :format) are handled by
   the job selection layer, not here.

   Returns true if mote matches all specified criteria."
  [mote options]
  (let [{:keys [role difficulty priority]} options]
    (and
     ;; Role filter: mote must have this role available
     (if role
       (contains? (mote->roles mote) role)
       true)
     ;; Difficulty filter
     (if difficulty
       (in-difficulty-range? (:difficulty mote) difficulty)
       true)
     ;; Priority filter
     (if priority
       (in-priority-range? (:priority mote) priority)
       true))))
