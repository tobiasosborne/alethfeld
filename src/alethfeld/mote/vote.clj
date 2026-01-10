(ns alethfeld.mote.vote
  "Vote and proposal constructors."
  (:require [alethfeld.mote.util :as util]))

;; -----------------------------------------------------------------------------
;; Vote Constructors
;; -----------------------------------------------------------------------------

(defn make-vote
  "Create a verification vote.

   Arguments:
   - agent: Agent name (string)
   - vote: :for or :against

   Options:
   - :reason - Optional reason string
   - :timestamp - Defaults to now"
  [agent vote & {:keys [reason timestamp]}]
  (cond-> {:agent agent
           :vote vote
           :timestamp (or timestamp (util/now))}
    reason (assoc :reason reason)))

(defn make-proposal-vote
  "Create a proposal vote (approve/reject).

   Arguments:
   - agent: Agent name (string)
   - vote: :approve or :reject

   Options:
   - :reason - Optional reason string
   - :timestamp - Defaults to now"
  [agent vote & {:keys [reason timestamp]}]
  (cond-> {:agent agent
           :vote vote
           :timestamp (or timestamp (util/now))}
    reason (assoc :reason reason)))

;; -----------------------------------------------------------------------------
;; Proposal Constructor
;; -----------------------------------------------------------------------------

(defn make-proposal
  "Create a decomposition proposal.

   Arguments:
   - proposed-by: Agent name (string)
   - children: Vector of child mote IDs

   Options:
   - :id - Proposal ID, defaults to generated
   - :proposed-at - Defaults to now
   - :votes - Defaults to []
   - :status - Defaults to :pending"
  [proposed-by children & {:keys [id proposed-at votes status]}]
  {:id (or id (str "prop-" (util/generate-id)))
   :proposed-by proposed-by
   :proposed-at (or proposed-at (util/now))
   :children (vec children)
   :votes (or votes [])
   :status (or status :pending)})
