(ns alethfeld.mote
  "Mote constructor and manipulation functions."
  (:require [alethfeld.schema :as s]))

;; -----------------------------------------------------------------------------
;; ID Generation
;; -----------------------------------------------------------------------------

(defn generate-id
  "Generate a unique ID suffix for proposals/jobs."
  []
  (let [ts (java.time.LocalDateTime/now)
        fmt (java.time.format.DateTimeFormatter/ofPattern "yyyyMMdd-HHmmss")
        random-suffix (format "%04x" (rand-int 65536))]
    (str (.format ts fmt) "-" random-suffix)))

;; -----------------------------------------------------------------------------
;; Timestamp Helpers
;; -----------------------------------------------------------------------------

(defn now
  "Get current instant."
  []
  (java.util.Date.))

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
           :timestamp (or timestamp (now))}
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
           :timestamp (or timestamp (now))}
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
  {:id (or id (str "prop-" (generate-id)))
   :proposed-by proposed-by
   :proposed-at (or proposed-at (now))
   :children (vec children)
   :votes (or votes [])
   :status (or status :pending)})

;; -----------------------------------------------------------------------------
;; Mote Constructors
;; -----------------------------------------------------------------------------

(defn make-mote
  "Create a mote with explicit values. Low-level constructor.

   Required:
   - id: Mote ID (string)
   - claim: The mathematical statement (string)
   - created-by: Agent name (string)

   Options:
   - :status - Defaults to :fixed
   - :taint - Defaults to #{:needs-decomposition}
   - :priority - Defaults to :p2
   - :difficulty - Defaults to 3
   - :parent - Parent mote ID (nil for roots)
   - :children - Vector of child IDs, defaults to []
   - :proposal - Active proposal, defaults to nil
   - :assumptions - Vector of assumptions, defaults to []
   - :definitions - Vector of definitions, defaults to []
   - :votes - Vector of votes, defaults to []
   - :claimed-by - Agent name, defaults to nil
   - :claimed-at - Timestamp, defaults to nil
   - :created-at - Timestamp, defaults to now
   - :updated-at - Timestamp, defaults to now
   - :meta - Additional metadata map"
  [id claim created-by & {:keys [status taint priority difficulty
                                  parent children proposal
                                  assumptions definitions votes
                                  claimed-by claimed-at
                                  created-at updated-at meta]}]
  (let [ts (or created-at (now))]
    (cond-> {:id id
             :claim claim
             :status (or status :fixed)
             :taint (or taint #{:needs-decomposition})
             :priority (or priority :p2)
             :difficulty (or difficulty 3)
             :children (or children [])
             :assumptions (or assumptions [])
             :definitions (or definitions [])
             :votes (or votes [])
             :created-by created-by
             :created-at ts
             :updated-at (or updated-at ts)}
      parent (assoc :parent parent)
      proposal (assoc :proposal proposal)
      claimed-by (assoc :claimed-by claimed-by)
      claimed-at (assoc :claimed-at claimed-at)
      meta (assoc :meta meta))))

(defn make-root-mote
  "Create a root mote (no parent).

   Arguments:
   - id: Mote ID (typically a single number like \"1\", \"2\")
   - claim: The mathematical statement
   - created-by: Agent name

   Options:
   - :priority - Defaults to :p2
   - :difficulty - Defaults to 3
   - Other options passed through to make-mote"
  [id claim created-by & {:keys [priority difficulty] :as opts}]
  (apply make-mote id claim created-by
         (mapcat identity (dissoc opts :parent))))

(defn make-child-mote
  "Create a child mote, inheriting priority/difficulty from parent.

   Arguments:
   - id: Mote ID (e.g., \"1.2.3\")
   - claim: The mathematical statement
   - created-by: Agent name
   - parent-mote: The parent mote map (to inherit from)

   Options:
   - :priority - Defaults to parent's priority
   - :difficulty - Defaults to parent's difficulty
   - Other options passed through to make-mote"
  [id claim created-by parent-mote & {:keys [priority difficulty] :as opts}]
  (apply make-mote id claim created-by
         :parent (:id parent-mote)
         :priority (or priority (:priority parent-mote) :p2)
         :difficulty (or difficulty (:difficulty parent-mote) 3)
         (mapcat identity (dissoc opts :parent :priority :difficulty))))

;; -----------------------------------------------------------------------------
;; Validation
;; -----------------------------------------------------------------------------

(defn valid-mote?
  "Check if mote is valid according to schema."
  [mote]
  (s/valid? s/Mote mote))

(defn valid-proposal?
  "Check if proposal is valid according to schema."
  [proposal]
  (s/valid? s/Proposal proposal))

(defn valid-vote?
  "Check if vote is valid according to schema."
  [vote]
  (s/valid? s/Vote vote))

(defn valid-proposal-vote?
  "Check if proposal vote is valid according to schema."
  [vote]
  (s/valid? s/ProposalVote vote))

;; -----------------------------------------------------------------------------
;; Mote Transformations (Pure Functions)
;; -----------------------------------------------------------------------------

(defn- touch
  "Update the :updated-at timestamp."
  [mote]
  (assoc mote :updated-at (now)))

(defn add-assumption
  "Add an assumption to a mote. Returns new mote."
  [mote assumption]
  (-> mote
      (update :assumptions conj assumption)
      touch))

(defn add-definition
  "Add a definition to a mote. Returns new mote."
  [mote definition]
  (-> mote
      (update :definitions conj definition)
      touch))

(defn add-vote
  "Add a verification vote to a mote. Returns new mote."
  [mote vote]
  (-> mote
      (update :votes conj vote)
      touch))

(defn add-taint
  "Add a taint flag to a mote. Returns new mote."
  [mote taint]
  (-> mote
      (update :taint conj taint)
      touch))

(defn remove-taint
  "Remove a taint flag from a mote. Returns new mote."
  [mote taint]
  (-> mote
      (update :taint disj taint)
      touch))

(defn set-status
  "Set the status of a mote. Returns new mote."
  [mote status]
  (-> mote
      (assoc :status status)
      touch))

(defn set-claimed-by
  "Set the claimed-by field of a mote. Returns new mote."
  [mote agent]
  (-> mote
      (assoc :claimed-by agent)
      (assoc :claimed-at (now))
      touch))

(defn clear-claim
  "Clear the claim on a mote. Returns new mote."
  [mote]
  (-> mote
      (dissoc :claimed-by :claimed-at)
      touch))

(defn set-proposal
  "Set an active proposal on a mote. Returns new mote."
  [mote proposal]
  (-> mote
      (assoc :proposal proposal)
      touch))

(defn clear-proposal
  "Clear the proposal from a mote. Returns new mote."
  [mote]
  (-> mote
      (dissoc :proposal)
      touch))

(defn add-child
  "Add a child ID to a mote. Returns new mote."
  [mote child-id]
  (-> mote
      (update :children conj child-id)
      touch))

(defn set-priority
  "Set the priority of a mote. Returns new mote."
  [mote priority]
  (-> mote
      (assoc :priority priority)
      touch))

(defn set-difficulty
  "Set the difficulty of a mote. Returns new mote."
  [mote difficulty]
  (-> mote
      (assoc :difficulty difficulty)
      touch))

(defn set-claim
  "Update the claim text of a mote. Returns new mote."
  [mote claim-text]
  (-> mote
      (assoc :claim claim-text)
      touch))
