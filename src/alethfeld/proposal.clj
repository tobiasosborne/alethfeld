(ns alethfeld.proposal
  "Proposal workflow for managing mote decomposition.

   A proposal represents a proposed decomposition of a parent mote into children.
   The workflow:
   1. Proposer creates a proposal with `create-proposal!`
   2. Advisors vote with `approve-proposal!` or `reject-proposal!`
   3. When quorum is reached, children are either promoted or archived"
  (:require [alethfeld.id :as id]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [alethfeld.verify :as verify]))

;; -----------------------------------------------------------------------------
;; Quorum Logic (Pure Functions)
;; -----------------------------------------------------------------------------

(defn count-votes
  "Count approve and reject votes in a proposal.
   Returns {:approve n :reject m}."
  [proposal]
  (verify/count-votes-by-type proposal :approve :reject))

(defn check-proposal-quorum
  "Check if a proposal has reached quorum.

   Arguments:
   - proposal: The proposal map
   - quorum: Number of votes needed

   Returns:
   - :approved if approve votes >= quorum
   - :rejected if reject votes >= quorum
   - :pending if neither (no contested state for proposals)"
  [proposal quorum]
  (verify/check-quorum-generic
   (count-votes proposal)
   quorum
   {:positive-key :approve
    :negative-key :reject
    :positive-result :approved
    :negative-result :rejected
    :contested-result nil  ; proposals don't have contested state
    :pending-result :pending}))

(defn has-voted?
  "Check if an agent has already voted on a proposal."
  [proposal agent]
  (some #(= agent (:agent %)) (:votes proposal)))

;; -----------------------------------------------------------------------------
;; Proposal Creation
;; -----------------------------------------------------------------------------

(defn- create-child-mote
  "Create a single proposed child mote from a claim specification.
   Returns the child mote with :proposed status."
  [parent agent claim-spec child-id]
  (let [atomic? (:atomic claim-spec)
        taint #{:needs-verification}]
    (cond-> (mote/make-child-mote
             child-id
             (:claim claim-spec)
             agent
             parent
             :status :proposed
             :taint taint
             :difficulty (or (:difficulty claim-spec)
                             (:difficulty parent)))
      atomic? (assoc :atomic true))))

(defn- create-child-motes
  "Create proposed child motes from claim specifications.

   Arguments:
   - parent: The parent mote
   - claims: Vector of {:claim ... :difficulty ... :atomic ...} maps
   - agent: The proposing agent

   Returns vector of child motes with :proposed status.
   All proposed children get :needs-verification taint."
  [parent claims agent]
  (let [parent-id (:id parent)
        existing-children (:children parent [])
        existing-proposed (when-let [prop (:proposal parent)]
                           (:children prop))
        initial-children (vec (concat existing-children existing-proposed))]
    (:result
     (reduce (fn [{:keys [all-children result]} claim-spec]
               (let [child-id (id/next-child-id parent-id all-children)
                     child (create-child-mote parent agent claim-spec child-id)]
                 {:all-children (conj all-children child-id)
                  :result (conj result child)}))
             {:all-children initial-children
              :result []}
             claims))))

(defn create-proposal!
  "Create a proposal to decompose a parent mote into children.

   Arguments:
   - repo-path: Path to the repository
   - parent-id: ID of the parent mote
   - claims: Vector of {:claim ... :difficulty ...} maps
   - agent: Name of the proposing agent

   Creates proposed child motes and attaches a proposal to the parent.
   Sets parent taint to :needs-proposal-review.

   Returns:
   - :result - Map with :proposal and :children
   - :commit - Commit info

   Throws if:
   - Parent not found
   - Parent already has an active proposal"
  [repo-path parent-id claims agent]
  (tx/with-validation
    repo-path
    (str "af: propose " parent-id)
    (fn [repo]
      (let [parent (store/load-mote repo parent-id)]
        ;; Validate parent exists
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id parent-id})))
        ;; Check for existing proposal
        (when (:proposal parent)
          (throw (ex-info "Parent already has an active proposal"
                          {:type :proposal-exists
                           :mote-id parent-id
                           :proposal-id (get-in parent [:proposal :id])})))
        ;; Create children
        (let [children (create-child-motes parent claims agent)
              child-ids (mapv :id children)
              proposal (mote/make-proposal agent child-ids)
              updated-parent (-> parent
                                 (mote/set-proposal proposal)
                                 (mote/remove-taint :needs-decomposition)
                                 (mote/add-taint :needs-proposal-review))]
          ;; Save children
          (doseq [child children]
            (store/save-mote! repo child))
          ;; Save updated parent
          (store/save-mote! repo updated-parent)
          {:proposal proposal
           :children children})))))

;; -----------------------------------------------------------------------------
;; Proposal Voting
;; -----------------------------------------------------------------------------

(defn- get-quorum
  "Get proposal quorum from config, defaulting to 1."
  [repo-path]
  (let [config (store/load-config repo-path)]
    (or (:proposal-quorum config) 1)))

(defn- promote-children!
  "Promote proposed children to fixed status.
   Moves files from proposed/ to motes/.
   All promoted children get :needs-verification taint.
   Throws if any child cannot be loaded - this indicates data corruption."
  [repo-path parent child-ids]
  (doseq [child-id child-ids]
    (let [child (store/load-mote repo-path child-id)]
      (when-not child
        (throw (ex-info "Child mote not found during promotion"
                        {:type :child-not-found
                         :parent-id (:id parent)
                         :child-id child-id})))
      (let [atomic? (:atomic child)
            taint-to-add :needs-verification
            promoted (-> child
                         (mote/set-status :fixed)
                         (mote/add-taint taint-to-add))]
        ;; Delete from proposed/
        (store/delete-mote! repo-path child-id)
        ;; Save to motes/
        (store/save-mote! repo-path promoted)))))

(defn- archive-children!
  "Archive rejected children.
   Moves files from proposed/ to archive/.
   Throws if any child cannot be loaded - this indicates data corruption."
  [repo-path child-ids]
  (doseq [child-id child-ids]
    (let [child (store/load-mote repo-path child-id)]
      (when-not child
        (throw (ex-info "Child mote not found during archival"
                        {:type :child-not-found
                         :child-id child-id})))
      (let [rejected (mote/set-status child :rejected)]
        ;; Delete from proposed/
        (store/delete-mote! repo-path child-id)
        ;; Save to archive/
        (store/save-mote! repo-path rejected)))))

(defn approve-proposal!
  "Cast an approve vote on a proposal.

   Arguments:
   - repo-path: Path to the repository
   - parent-id: ID of the parent mote with the proposal
   - agent: Name of the voting agent

   Options:
   - :reason - Optional reason string

   If quorum is reached:
   - Children move from proposed/ to motes/ with :fixed status
   - Parent :children is populated
   - Parent proposal is cleared
   - Parent :needs-proposal-review taint is removed

   Returns:
   - :result - Map with :vote-cast, :quorum-status, :promoted-children
   - :commit - Commit info

   Throws if:
   - Parent not found
   - No active proposal
   - Agent has already voted"
  [repo-path parent-id agent & {:keys [reason]}]
  (tx/with-validation
    repo-path
    (str "af: approve " parent-id)
    (fn [repo]
      (let [parent (store/load-mote repo parent-id)
            quorum (get-quorum repo)]
        ;; Validate
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id parent-id})))
        (when-not (:proposal parent)
          (throw (ex-info "No active proposal"
                          {:type :no-proposal
                           :mote-id parent-id})))
        (when (has-voted? (:proposal parent) agent)
          (throw (ex-info "Agent has already voted"
                          {:type :already-voted
                           :mote-id parent-id
                           :agent agent})))
        ;; Cast vote
        (let [vote (mote/make-proposal-vote agent :approve :reason reason)
              updated-proposal (update (:proposal parent) :votes conj vote)
              quorum-status (check-proposal-quorum updated-proposal quorum)]
          (if (= :approved quorum-status)
            ;; Quorum reached - promote children
            (let [child-ids (:children updated-proposal)
                  final-proposal (assoc updated-proposal :status :approved)
                  final-parent (-> parent
                                   (assoc :children (vec (concat (:children parent) child-ids)))
                                   (mote/clear-proposal)
                                   (mote/remove-taint :needs-proposal-review)
                                   (mote/remove-taint :needs-decomposition))]
              (promote-children! repo parent child-ids)
              (store/save-mote! repo final-parent)
              {:vote-cast vote
               :quorum-status :approved
               :promoted-children child-ids})
            ;; Quorum not reached - just record vote
            (let [updated-parent (mote/set-proposal parent updated-proposal)]
              (store/save-mote! repo updated-parent)
              {:vote-cast vote
               :quorum-status :pending
               :promoted-children nil})))))))

(defn reject-proposal!
  "Cast a reject vote on a proposal.

   Arguments:
   - repo-path: Path to the repository
   - parent-id: ID of the parent mote with the proposal
   - agent: Name of the voting agent

   Options:
   - :reason - Optional reason string

   If quorum is reached:
   - Children move from proposed/ to archive/ with :rejected status
   - Parent proposal is cleared
   - Parent gets :needs-decomposition taint

   Returns:
   - :result - Map with :vote-cast, :quorum-status, :archived-children
   - :commit - Commit info

   Throws if:
   - Parent not found
   - No active proposal
   - Agent has already voted"
  [repo-path parent-id agent & {:keys [reason]}]
  (tx/with-validation
    repo-path
    (str "af: reject " parent-id)
    (fn [repo]
      (let [parent (store/load-mote repo parent-id)
            quorum (get-quorum repo)]
        ;; Validate
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id parent-id})))
        (when-not (:proposal parent)
          (throw (ex-info "No active proposal"
                          {:type :no-proposal
                           :mote-id parent-id})))
        (when (has-voted? (:proposal parent) agent)
          (throw (ex-info "Agent has already voted"
                          {:type :already-voted
                           :mote-id parent-id
                           :agent agent})))
        ;; Cast vote
        (let [vote (mote/make-proposal-vote agent :reject :reason reason)
              updated-proposal (update (:proposal parent) :votes conj vote)
              quorum-status (check-proposal-quorum updated-proposal quorum)]
          (if (= :rejected quorum-status)
            ;; Quorum reached - archive children
            (let [child-ids (:children updated-proposal)
                  final-parent (-> parent
                                   (mote/clear-proposal)
                                   (mote/remove-taint :needs-proposal-review)
                                   (mote/add-taint :needs-decomposition))]
              (archive-children! repo child-ids)
              (store/save-mote! repo final-parent)
              {:vote-cast vote
               :quorum-status :rejected
               :archived-children child-ids})
            ;; Quorum not reached - just record vote
            (let [updated-parent (mote/set-proposal parent updated-proposal)]
              (store/save-mote! repo updated-parent)
              {:vote-cast vote
               :quorum-status :pending
               :archived-children nil})))))))

;; -----------------------------------------------------------------------------
;; Proposal Withdrawal
;; -----------------------------------------------------------------------------

(defn withdraw-proposal!
  "Withdraw a proposal by the original proposer.

   Arguments:
   - repo-path: Path to the repository
   - parent-id: ID of the parent mote with the proposal
   - agent: Name of the withdrawing agent (must be the proposer)

   A proposal can only be withdrawn if:
   - The parent has an active proposal
   - The proposal status is :pending
   - The agent is the original proposer

   On withdrawal:
   - Children move from proposed/ to archive/ with :withdrawn status
   - Parent proposal is cleared
   - Parent gets :needs-decomposition taint

   Returns:
   - :result - Map with :withdrawn-children
   - :commit - Commit info

   Throws if:
   - Parent not found
   - No active proposal
   - Proposal not pending (already approved or rejected)
   - Agent is not the proposer"
  [repo-path parent-id agent]
  (tx/with-validation
    repo-path
    (str "af: withdraw " parent-id)
    (fn [repo]
      (let [parent (store/load-mote repo parent-id)]
        ;; Validate
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id parent-id})))
        (when-not (:proposal parent)
          (throw (ex-info "No active proposal"
                          {:type :no-proposal
                           :mote-id parent-id})))
        (let [proposal (:proposal parent)
              proposer (:proposed-by proposal)]
          ;; Check proposal is pending
          (when-not (= :pending (:status proposal))
            (throw (ex-info "Proposal is not pending"
                            {:type :invalid-status
                             :mote-id parent-id
                             :proposal-status (:status proposal)
                             :expected :pending})))
          ;; Check agent is the proposer
          (when-not (= agent proposer)
            (throw (ex-info "Only the proposer can withdraw a proposal"
                            {:type :action-not-allowed
                             :mote-id parent-id
                             :agent agent
                             :proposer proposer})))
          ;; Archive children
          (let [child-ids (:children proposal)
                final-parent (-> parent
                                 (mote/clear-proposal)
                                 (mote/remove-taint :needs-proposal-review)
                                 (mote/add-taint :needs-decomposition))]
            (archive-children! repo child-ids)
            (store/save-mote! repo final-parent)
            {:withdrawn-children child-ids}))))))

;; -----------------------------------------------------------------------------
;; Query Functions
;; -----------------------------------------------------------------------------

(defn proposal-status
  "Get the current status of a proposal on a mote.

   Returns map with:
   - :has-proposal - Whether an active proposal exists
   - :proposal - The proposal (if any)
   - :quorum - Required quorum
   - :quorum-status - :pending, :approved, or :rejected
   - :votes-needed - Number of votes still needed"
  [repo-path parent-id]
  (let [parent (store/load-mote repo-path parent-id)
        quorum (get-quorum repo-path)]
    (if-let [proposal (:proposal parent)]
      (let [{:keys [approve reject]} (count-votes proposal)
            status (check-proposal-quorum proposal quorum)]
        {:has-proposal true
         :proposal proposal
         :quorum quorum
         :quorum-status status
         :votes-for approve
         :votes-against reject
         :votes-needed (max 0 (- quorum (max approve reject)))})
      {:has-proposal false
       :proposal nil
       :quorum quorum
       :quorum-status nil
       :votes-needed nil})))
