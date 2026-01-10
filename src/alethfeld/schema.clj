(ns alethfeld.schema
  "Malli schemas for Alethfeld data structures."
  (:require [malli.core :as m]))

;; -----------------------------------------------------------------------------
;; Primitive Types
;; -----------------------------------------------------------------------------

(def MoteId
  "Hierarchical Lamport-style ID (e.g., \"1.2.3\").
   Must be dot-separated positive integers."
  [:and
   [:string {:min 1}]
   [:fn {:error/message "Must be dot-separated integers (e.g., \"1.2.3\")"}
    #(boolean (re-matches #"\d+(\.\d+)*" %))]])

(def Status
  "Mote lifecycle status."
  [:enum :proposed :rejected :fixed :verified :refuted :contested])

(def Taint
  "Work indicator flags."
  [:enum
   :needs-decomposition :needs-proposal-review :needs-refinement
   :needs-verification :needs-refs :needs-votes :needs-counterexample])

(def Priority
  "Work urgency level."
  [:enum :p0 :p1 :p2 :p3 :p4])

(def Difficulty
  "Agent capability required (1-5)."
  [:int {:min 1 :max 5}])

(def Role
  "Agent role types."
  [:enum :proposer :advisor :prover :verifier :ref-checker :counterexample])

;; -----------------------------------------------------------------------------
;; References & Definitions
;; -----------------------------------------------------------------------------

(def InternalRef
  "Reference to another mote within the project."
  [:map
   [:type [:= :internal]]
   [:ref MoteId]
   [:note {:optional true} :string]])

(def ExternalRef
  "Reference to external resource (paper, book, etc.)."
  [:map
   [:type [:= :external]]
   [:ref :string]
   [:note {:optional true} :string]])

(def Assumption
  "Either an internal or external reference."
  [:or InternalRef ExternalRef])

(def Definition
  "Symbol definition within a mote."
  [:map
   [:symbol :string]
   [:meaning :string]])

(def Dependency
  "Dependency on another mote (mote X depends on mote Y)."
  [:map
   [:ref MoteId]
   [:reason {:optional true} :string]])

;; -----------------------------------------------------------------------------
;; Votes
;; -----------------------------------------------------------------------------

(def Vote
  "Verification vote on a mote."
  [:map
   [:agent :string]
   [:vote [:enum :for :against]]
   [:reason {:optional true} :string]
   [:timestamp inst?]])

(def ProposalVote
  "Vote on a decomposition proposal."
  [:map
   [:agent :string]
   [:vote [:enum :approve :reject]]
   [:reason {:optional true} :string]
   [:timestamp inst?]])

;; -----------------------------------------------------------------------------
;; Proposal
;; -----------------------------------------------------------------------------

(def Proposal
  "Tracks a proposed decomposition awaiting approval."
  [:map
   [:id :string]
   [:proposed-by :string]
   [:proposed-at inst?]
   [:children [:vector MoteId]]
   [:votes [:vector ProposalVote]]
   [:status [:enum :pending :approved :rejected]]])

;; -----------------------------------------------------------------------------
;; Contributors
;; -----------------------------------------------------------------------------

(def Contributors
  "Tracks all agents who contributed to a mote.
   Used for self-vote prevention - contributors cannot vote on their own work."
  [:map
   [:created-by :string]
   [:proposed-by {:optional true} :string]
   [:refined-by {:optional true} [:set :string]]
   [:refs-checked-by {:optional true} [:set :string]]])

;; -----------------------------------------------------------------------------
;; Mote
;; -----------------------------------------------------------------------------

(def Mote
  "The fundamental unit of proof structure."
  [:map
   [:id MoteId]
   [:claim :string]
   [:status Status]
   [:taint [:set Taint]]
   [:priority Priority]
   [:difficulty Difficulty]

   [:parent {:optional true} MoteId]
   [:children [:vector MoteId]]
   [:proposal {:optional true} Proposal]

   [:assumptions [:vector Assumption]]
   [:definitions [:vector Definition]]
   [:depends-on {:optional true} [:vector Dependency]]
   [:votes [:vector Vote]]

   [:claimed-by {:optional true} :string]
   [:claimed-at {:optional true} inst?]

   [:atomic {:optional true} :boolean]

   [:created-by :string]
   [:created-at inst?]
   [:updated-at inst?]
   [:contributors {:optional true} Contributors]
   [:meta {:optional true} [:map-of :keyword :any]]])

;; -----------------------------------------------------------------------------
;; Job
;; -----------------------------------------------------------------------------

(def Job
  "Work assignment for an agent."
  [:map
   [:job-id :string]
   [:mote-id MoteId]
   [:role Role]
   [:difficulty Difficulty]
   [:priority Priority]
   [:mote Mote]
   [:parent {:optional true} Mote]
   [:siblings [:vector Mote]]
   [:prompt :string]])

;; -----------------------------------------------------------------------------
;; Ready Options
;; -----------------------------------------------------------------------------

(def DifficultyRange
  "Single difficulty or min-max range."
  [:or
   Difficulty
   [:tuple Difficulty Difficulty]])

(def PriorityRange
  "Single priority or min-max range."
  [:or
   Priority
   [:tuple Priority Priority]])

(def ReadyOptions
  "Options for querying available jobs."
  [:map
   [:agent {:optional true} :string]
   [:role {:optional true} Role]
   [:difficulty {:optional true} DifficultyRange]
   [:priority {:optional true} PriorityRange]
   [:max {:optional true} [:int {:min 1}]]
   [:no-claim {:optional true} :boolean]
   [:format {:optional true} [:enum :edn :json]]])

;; -----------------------------------------------------------------------------
;; Config
;; -----------------------------------------------------------------------------

(def Config
  "Project configuration stored in config.edn."
  [:map
   [:project-name :string]
   [:version :string]
   [:default-difficulty Difficulty]
   [:proposal-quorum {:optional true} [:int {:min 1}]]
   [:vote-quorum {:optional true} [:int {:min 1}]]
   [:claim-timeout-minutes {:optional true} [:int {:min 1}]]
   [:session-timeout-minutes {:optional true} [:int {:min 1}]]])

;; -----------------------------------------------------------------------------
;; Session
;; -----------------------------------------------------------------------------

(def SessionId
  "Dual-UUID session identifier for 256 bits of entropy."
  [:and
   [:string {:min 73 :max 73}]  ; Two UUIDs (36 chars each) + hyphen = 73
   [:fn {:error/message "Must be dual-UUID format (e.g., \"uuid-uuid\")"}
    #(boolean (re-matches #"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}" %))]])

(def Session
  "A role-bound work session on a mote."
  [:map
   [:session-id SessionId]
   [:mote-id MoteId]
   [:role Role]
   [:agent :string]
   [:started-at inst?]
   [:expires-at inst?]
   [:pid {:optional true} :int]
   [:actions [:vector :keyword]]])

;; -----------------------------------------------------------------------------
;; Validation Helpers
;; -----------------------------------------------------------------------------

(defn valid?
  "Check if value matches schema."
  [schema value]
  (m/validate schema value))

(defn explain
  "Explain why value doesn't match schema, or nil if valid."
  [schema value]
  (m/explain schema value))

;; -----------------------------------------------------------------------------
;; State Machine Transitions
;; -----------------------------------------------------------------------------

(def valid-status-transitions
  "Map of valid status transitions.
   Each key is a source status, value is a set of valid target statuses.

   State machine:
   - :needs-decomposition -> :needs-proposal-review (when proposal created)
   - :needs-proposal-review -> :needs-decomposition (when proposal rejected)
   - :needs-proposal-review -> :needs-verification (when proposal approved)
   - :needs-verification -> :verified (unanimous for)
   - :needs-verification -> :refuted (unanimous against)
   - :needs-verification -> :contested (mixed votes)"
  {:needs-decomposition   #{:needs-proposal-review}
   :needs-proposal-review #{:needs-decomposition :needs-verification}
   :needs-verification    #{:verified :refuted :contested}
   :verified              #{}
   :refuted               #{}
   :contested             #{}
   :rejected              #{}})

(def MoteStatus
  "Extended mote lifecycle status including workflow states."
  [:enum
   :needs-decomposition
   :needs-proposal-review
   :needs-verification
   :verified
   :refuted
   :contested
   :rejected])

(defn valid-status-transition?
  "Check if transitioning from `from-status` to `to-status` is allowed.
   Returns true if the transition is valid, false otherwise.

   Terminal states (:verified, :refuted, :contested, :rejected) have no valid
   outgoing transitions."
  [from-status to-status]
  (let [valid-targets (get valid-status-transitions from-status)]
    (boolean (and valid-targets (contains? valid-targets to-status)))))

(defn status-transition-error
  "Returns an error message if the transition is invalid, nil otherwise."
  [from-status to-status]
  (let [valid-targets (get valid-status-transitions from-status)]
    (cond
      (nil? valid-targets)
      (str "Unknown source status: " from-status)

      (empty? valid-targets)
      (str "Terminal status " from-status " cannot transition to any other status")

      (not (contains? valid-targets to-status))
      (str "Invalid transition from " from-status " to " to-status
           ". Valid targets are: " (pr-str valid-targets))

      :else nil)))

(def ValidStatusTransition
  "Schema for a valid status transition pair [from-status to-status].
   Validates that both statuses are valid MoteStatus values and that
   the transition between them is allowed."
  [:and
   [:tuple MoteStatus MoteStatus]
   [:fn {:error/message "Invalid status transition"}
    (fn [[from to]] (valid-status-transition? from to))]])
