(ns alethfeld.job
  "Job selection and role derivation functions."
  (:require [alethfeld.schema :as s]
            [alethfeld.mote :as mote]))

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
   - It is not currently claimed (or claim has expired if timeout provided)
   - It has at least one taint flag that maps to a role

   Arguments:
   - mote: The mote to check

   Options:
   - :claim-timeout - Minutes after which claims expire (default: nil, no expiration)"
  [mote & {:keys [claim-timeout]}]
  (boolean
   (and (not (terminal-statuses (:status mote)))
        (or (nil? (:claimed-by mote))
            (and claim-timeout (mote/claim-expired? mote claim-timeout)))
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

;; -----------------------------------------------------------------------------
;; Job Sorting
;; -----------------------------------------------------------------------------

(defn priority->rank
  "Convert priority keyword to numeric rank for sorting.
   Lower rank = higher urgency (p0 → 0, p4 → 4)."
  [priority]
  (priority-rank priority))

(defn job-comparator
  "Comparator for sorting motes by priority (p0 first), then difficulty (lower first).
   Returns negative if a should come before b, positive if after, 0 if equal."
  [mote-a mote-b]
  (let [pri-cmp (compare (priority->rank (:priority mote-a))
                         (priority->rank (:priority mote-b)))]
    (if (zero? pri-cmp)
      (compare (:difficulty mote-a) (:difficulty mote-b))
      pri-cmp)))

;; -----------------------------------------------------------------------------
;; Job Building
;; -----------------------------------------------------------------------------

(defn build-job
  "Build a Job record from a mote and context.

   Arguments:
   - mote: The mote to create a job for
   - motes: Map of mote-id → mote for looking up parent/siblings

   Options:
   - :role - Override role (otherwise derived from mote taints)
   - :prompt - Prompt string (defaults to placeholder, real prompts in Step 3.3)

   Returns a Job map conforming to schema/Job."
  [mote motes & {:keys [role prompt]}]
  (let [mote-id (:id mote)
        derived-role (or role (mote->role mote))
        parent-id (:parent mote)
        parent (when parent-id (get motes parent-id))
        ;; Siblings are other children of the same parent
        siblings (when parent
                   (->> (:children parent)
                        (remove #{mote-id})
                        (keep #(get motes %))
                        vec))]
    {:job-id (str "job-" (mote/generate-id))
     :mote-id mote-id
     :role derived-role
     :difficulty (:difficulty mote)
     :priority (:priority mote)
     :mote mote
     :parent parent
     :siblings (or siblings [])
     :prompt (or prompt (str "TODO: Prompt for " (name derived-role) " role"))}))

;; -----------------------------------------------------------------------------
;; Job Selection
;; -----------------------------------------------------------------------------

(defn select-jobs
  "Select jobs from a collection of motes based on filter options.

   Arguments:
   - motes: Map of mote-id → mote

   Options (ReadyOptions):
   - :role - Filter by role
   - :difficulty - Filter by difficulty (exact or [min max] range)
   - :priority - Filter by priority (exact or [min max] range)
   - :max - Maximum number of jobs to return (default: 1)
   - :claim-timeout - Minutes after which claims expire (enables reclaiming stale jobs)

   Selection algorithm:
   1. Filter to workable motes (non-terminal status, unclaimed/expired, has role taint)
   2. Apply role/difficulty/priority filters
   3. Sort by priority (p0 first), then difficulty (lower first)
   4. Take first N jobs
   5. Build Job records for each

   Returns a vector of Job maps."
  [motes & {:keys [role difficulty priority max claim-timeout]
            :or {max 1}
            :as options}]
  (let [filter-opts (select-keys options [:role :difficulty :priority])]
    (->> (vals motes)
         (filter #(workable? % :claim-timeout claim-timeout))
         (filter #(matches-filter? % filter-opts))
         (sort job-comparator)
         (take max)
         (mapv #(build-job % motes :role role))
         vec)))
