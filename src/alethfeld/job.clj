(ns alethfeld.job
  "Job selection and role derivation functions."
  (:require [alethfeld.schema :as s]
            [alethfeld.mote :as mote]))

;; -----------------------------------------------------------------------------
;; Claim Timeout Configuration
;; -----------------------------------------------------------------------------

(def ^:dynamic *default-timeout-hours*
  "Default timeout for claim expiration in hours.
   Can be rebound for testing or configuration."
  24)

;; -----------------------------------------------------------------------------
;; Claim Expiration Functions
;; -----------------------------------------------------------------------------

(defn claim-expired?
  "Check if a mote's claim has expired based on timeout hours.

   Arguments:
   - claim: A mote or any map with :claimed-at and :claimed-by

   Options:
   - :timeout-hours - Hours after which claims expire (default: 24)
   - :now - Optional java.time.Instant for current time (for testing)

   Returns true if:
   - The claim has a :claimed-at timestamp older than timeout-hours

   Returns false if:
   - The claim is not present (no :claimed-by)
   - The claim has no :claimed-at timestamp
   - The claim is within the timeout window"
  [claim & {:keys [timeout-hours now] :or {timeout-hours *default-timeout-hours*}}]
  (let [timeout-minutes (* timeout-hours 60)]
    (if now
      (mote/claim-expired? claim timeout-minutes :now now)
      (mote/claim-expired? claim timeout-minutes))))

(defn filter-expired-claims
  "Filter a collection of motes to find those with expired claims.

   Arguments:
   - motes: A collection of motes (or map of id->mote)

   Options:
   - :timeout-hours - Hours after which claims expire (default: 24)
   - :now - Optional java.time.Instant for current time (for testing)

   Returns a sequence of motes that have expired claims.
   These are motes that were claimed but the claim has timed out,
   making them available for re-claiming by other agents."
  [motes & {:keys [timeout-hours now] :or {timeout-hours *default-timeout-hours*}}]
  (let [mote-seq (if (map? motes) (vals motes) motes)]
    (filter (fn [mote]
              (and (:claimed-by mote)
                   (if now
                     (claim-expired? mote :timeout-hours timeout-hours :now now)
                     (claim-expired? mote :timeout-hours timeout-hours))))
            mote-seq)))

(defn filter-active-claims
  "Filter a collection of motes to find those with active (non-expired) claims.

   Arguments:
   - motes: A collection of motes (or map of id->mote)

   Options:
   - :timeout-hours - Hours after which claims expire (default: 24)
   - :now - Optional java.time.Instant for current time (for testing)

   Returns a sequence of motes that have active claims.
   These are motes currently being worked on by an agent."
  [motes & {:keys [timeout-hours now] :or {timeout-hours *default-timeout-hours*}}]
  (let [mote-seq (if (map? motes) (vals motes) motes)]
    (filter (fn [mote]
              (and (:claimed-by mote)
                   (not (if now
                          (claim-expired? mote :timeout-hours timeout-hours :now now)
                          (claim-expired? mote :timeout-hours timeout-hours)))))
            mote-seq)))

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
  {:verifier       0  ; Verify FIRST (gatekeeper)
   :proposer       1  ; Decompose (only after verifier demands)
   :advisor        2  ; Review proposals
   :prover         3  ; Refine details
   :ref-checker    4  ; Check refs
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
   (verifier > proposer > advisor > prover > ref-checker > counterexample).

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
   - :claim-timeout - Minutes after which claims expire (default: nil, no expiration)
   - :claim-timeout-hours - Hours after which claims expire (takes precedence over :claim-timeout)
   - :now - Optional java.time.Instant for current time (for testing)"
  [mote & {:keys [claim-timeout claim-timeout-hours now]}]
  (let [timeout-minutes (or (when claim-timeout-hours (* claim-timeout-hours 60))
                            claim-timeout)]
    (boolean
     (and (not (terminal-statuses (:status mote)))
          (or (nil? (:claimed-by mote))
              (and timeout-minutes
                   (if now
                     (mote/claim-expired? mote timeout-minutes :now now)
                     (mote/claim-expired? mote timeout-minutes))))
          (seq (mote->roles mote))))))

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

(def ^:private unknown-priority-rank
  "Rank assigned to nil or invalid priorities. High value sorts them last."
  999)

(defn priority->rank
  "Convert priority keyword to numeric rank for sorting.
   Lower rank = higher urgency (p0 → 0, p4 → 4).
   Returns 999 for nil or invalid priorities (sorts them last)."
  [priority]
  (get priority-rank priority unknown-priority-rank))

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
   - :claim-timeout-hours - Hours after which claims expire (takes precedence over :claim-timeout)
   - :now - Optional java.time.Instant for current time (for testing)

   Selection algorithm:
   1. Filter to workable motes (non-terminal status, unclaimed/expired, has role taint)
   2. Apply role/difficulty/priority filters
   3. Sort by priority (p0 first), then difficulty (lower first)
   4. Take first N jobs
   5. Build Job records for each

   Returns a vector of Job maps."
  [motes & {:keys [role difficulty priority max claim-timeout claim-timeout-hours now]
            :or {max 1}}]
  (->> (vals motes)
       (filter #(workable? % :claim-timeout claim-timeout
                             :claim-timeout-hours claim-timeout-hours
                             :now now))
       (filter #(matches-filter? % {:role role :difficulty difficulty :priority priority}))
       (sort job-comparator)
       (take max)
       (mapv #(build-job % motes :role role))
       vec))
