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
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]))

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
   - Agent has already voted"
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
