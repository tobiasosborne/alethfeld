(ns alethfeld.verify
  "Verification workflow for validating mote correctness.

   The workflow:
   1. Verifiers examine a mote and cast votes with `cast-vote!`
   2. When quorum is reached, status transitions:
      - :verified if all votes are :for
      - :refuted if all votes are :against
      - :contested if votes are mixed
   3. Taints are updated based on outcome"
  (:require [alethfeld.mote :as mote]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [alethfeld.id :as id]))

;; -----------------------------------------------------------------------------
;; Quorum Logic (Pure Functions)
;; -----------------------------------------------------------------------------

(defn count-verification-votes
  "Count for and against votes on a mote.
   Returns {:for n :against m}."
  [mote]
  (let [votes (:votes mote [])]
    {:for (count (filter #(= :for (:vote %)) votes))
     :against (count (filter #(= :against (:vote %)) votes))}))

(defn check-verification-quorum
  "Check if a mote has reached verification quorum.

   Arguments:
   - mote: The mote map
   - quorum: Number of votes needed

   Returns:
   - :verified if for votes >= quorum AND no against votes
   - :refuted if against votes >= quorum AND no for votes
   - :contested if both for AND against votes exist AND total >= quorum
   - :pending if total votes < quorum"
  [mote quorum]
  (let [{:keys [for against]} (count-verification-votes mote)
        total (+ for against)]
    (cond
      ;; Not enough votes yet
      (< total quorum) :pending
      ;; Unanimous for
      (and (>= for quorum) (zero? against)) :verified
      ;; Unanimous against
      (and (>= against quorum) (zero? for)) :refuted
      ;; Mixed votes with enough total
      (>= total quorum) :contested
      ;; Default pending
      :else :pending)))

(defn has-voted?
  "Check if an agent has already voted on this mote."
  [mote agent]
  (some #(= agent (:agent %)) (:votes mote)))

(defn unverified-dependencies
  "Return list of dependency refs that are not yet :verified.
   Returns empty vector if all dependencies are verified or if no dependencies exist."
  [repo-path mote]
  (let [deps (:depends-on mote [])]
    (vec
     (for [{:keys [ref]} deps
           :let [dep-mote (store/load-mote repo-path ref)]
           :when (or (nil? dep-mote)
                     (not= :verified (:status dep-mote)))]
       ref))))

;; -----------------------------------------------------------------------------
;; Vote Casting
;; -----------------------------------------------------------------------------

(defn- get-vote-quorum
  "Get verification vote quorum from config, defaulting to 2."
  [repo-path]
  (let [config (store/load-config repo-path)]
    (or (:vote-quorum config) 2)))

(defn- update-status-and-taint
  "Update mote status and taints based on quorum result.

   Returns updated mote."
  [mote quorum-status]
  (case quorum-status
    :verified (-> mote
                  (mote/set-status :verified)
                  (mote/remove-taint :needs-verification)
                  (mote/remove-taint :needs-votes))

    :refuted (-> mote
                 (mote/set-status :refuted)
                 (mote/remove-taint :needs-verification)
                 (mote/remove-taint :needs-votes))

    :contested (-> mote
                   (mote/set-status :contested)
                   (mote/remove-taint :needs-verification)
                   (mote/add-taint :needs-votes))

    ;; :pending - just update needs-votes
    (mote/add-taint mote :needs-votes)))

(defn cast-vote!
  "Cast a verification vote on a mote.

   Arguments:
   - repo-path: Path to the repository
   - mote-id: ID of the mote to vote on
   - agent: Name of the voting agent
   - vote-type: :for or :against

   Options:
   - :reason - Optional reason string

   When quorum is reached:
   - :verified if unanimous for votes
   - :refuted if unanimous against votes
   - :contested if mixed votes

   Returns:
   - :result - Map with :vote-cast, :quorum-status, :status-changed
   - :commit - Commit info

   Throws if:
   - Mote not found
   - Mote status is not :fixed (can only verify fixed motes)
   - Agent has already voted
   - Agent is a contributor (self-vote prevention)
   - Mote has unverified dependencies"
  [repo-path mote-id agent vote-type & {:keys [reason]}]
  (tx/with-validation
    repo-path
    (str "af: vote " mote-id " " (name vote-type))
    (fn [repo]
      (let [current-mote (store/load-mote repo mote-id)
            quorum (get-vote-quorum repo)]
        ;; Validate mote exists
        (when-not current-mote
          (throw (ex-info "Mote not found"
                          {:type :not-found
                           :mote-id mote-id})))
        ;; Validate status allows voting
        (when-not (= :fixed (:status current-mote))
          (throw (ex-info "Can only vote on fixed motes"
                          {:type :invalid-status
                           :mote-id mote-id
                           :status (:status current-mote)})))
        ;; Check for duplicate vote
        (when (has-voted? current-mote agent)
          (throw (ex-info "Agent has already voted"
                          {:type :already-voted
                           :mote-id mote-id
                           :agent agent})))
        ;; Check for self-vote (contributor cannot vote)
        (when-not (session/can-vote? current-mote agent)
          (throw (ex-info "Contributors cannot vote on their own work"
                          {:type :self-vote
                           :mote-id mote-id
                           :agent agent
                           :contributors (session/get-contributors current-mote)})))
        ;; Check dependencies are verified
        (let [unverified-deps (unverified-dependencies repo current-mote)]
          (when (seq unverified-deps)
            (throw (ex-info "Cannot verify mote with unverified dependencies"
                            {:type :unverified-dependencies
                             :mote-id mote-id
                             :unverified-deps unverified-deps}))))
        ;; Cast the vote
        (let [vote (mote/make-vote agent vote-type :reason reason)
              voted-mote (mote/add-vote current-mote vote)
              quorum-status (check-verification-quorum voted-mote quorum)
              final-mote (update-status-and-taint voted-mote quorum-status)
              status-changed (not= (:status current-mote) (:status final-mote))]
          (store/save-mote! repo final-mote)
          {:vote-cast vote
           :quorum-status quorum-status
           :status-changed status-changed
           :new-status (:status final-mote)})))))

;; -----------------------------------------------------------------------------
;; Query Functions
;; -----------------------------------------------------------------------------

(defn verification-status
  "Get the current verification status of a mote.

   Returns map with:
   - :status - Current mote status
   - :quorum - Required quorum
   - :quorum-status - :pending, :verified, :refuted, or :contested
   - :votes-for - Number of for votes
   - :votes-against - Number of against votes
   - :votes-needed - Number of votes still needed (if pending)"
  [repo-path mote-id]
  (let [current-mote (store/load-mote repo-path mote-id)
        quorum (get-vote-quorum repo-path)]
    (if current-mote
      (let [{:keys [for against]} (count-verification-votes current-mote)
            total (+ for against)
            status (check-verification-quorum current-mote quorum)]
        {:status (:status current-mote)
         :quorum quorum
         :quorum-status status
         :votes-for for
         :votes-against against
         :votes-needed (max 0 (- quorum total))})
      {:status nil
       :quorum quorum
       :quorum-status nil
       :votes-for 0
       :votes-against 0
       :votes-needed quorum})))

(defn needs-verification?
  "Check if a mote needs verification.
   A mote needs verification if:
   - Status is :fixed
   - Has :needs-verification taint"
  [mote]
  (and (= :fixed (:status mote))
       (contains? (:taint mote) :needs-verification)))

;; -----------------------------------------------------------------------------
;; Auto-Propagation
;; -----------------------------------------------------------------------------

(defn all-siblings-verified?
  "Check if all siblings of a mote are verified.

   Arguments:
   - motes: Map of mote-id -> mote
   - mote-id: The mote to check siblings for

   Returns true if:
   - The mote has a parent (not a root)
   - All siblings (other children of the same parent) are :verified"
  [motes mote-id]
  (when-let [parent-id (id/parent-id mote-id)]
    (when-let [parent (get motes parent-id)]
      (let [sibling-ids (remove #{mote-id} (:children parent))
            siblings (keep #(get motes %) sibling-ids)]
        ;; All siblings must be verified
        (every? #(= :verified (:status %)) siblings)))))

(defn can-propagate-to-parent?
  "Check if verification can propagate to a parent mote.

   Returns true if:
   - Parent exists
   - Parent is :fixed status (ready for verification)
   - All children of parent are :verified
   - Agent can vote on parent (not a contributor)"
  [motes parent-id agent]
  (when-let [parent (get motes parent-id)]
    (and (= :fixed (:status parent))
         (let [child-ids (:children parent)
               children (keep #(get motes %) child-ids)]
           (every? #(= :verified (:status %)) children))
         (session/can-vote? parent agent)
         (not (has-voted? parent agent)))))

(defn propagate-verification!
  "Propagate verification votes up the tree.

   After a mote becomes verified, checks if all its siblings are also verified.
   If so, and the agent can vote on the parent, casts a :for vote on the parent.
   Recursively continues up the tree.

   Arguments:
   - repo-path: Path to the repository
   - mote-id: The mote that was just verified
   - agent: The agent casting votes
   - reason: Optional reason for propagated votes

   Returns a vector of parent IDs that were voted on."
  [repo-path mote-id agent & {:keys [reason]}]
  (loop [current-id mote-id
         propagated []]
    (let [parent-id (id/parent-id current-id)]
      (if (nil? parent-id)
        ;; Reached root, done propagating
        propagated
        ;; Check if we can propagate to parent
        (let [motes (store/load-all-motes repo-path)]
          (if (can-propagate-to-parent? motes parent-id agent)
            ;; Cast vote on parent
            (let [result (cast-vote! repo-path parent-id agent :for
                                     :reason (or reason "Auto-propagated from children"))]
              (if (= :verified (:quorum-status (:result result)))
                ;; Parent verified, continue propagating
                (recur parent-id (conj propagated parent-id))
                ;; Parent not yet verified (needs more votes), stop
                (conj propagated parent-id)))
            ;; Cannot propagate (parent not ready, agent is contributor, or already voted)
            propagated))))))
