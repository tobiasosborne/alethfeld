(ns validate-graph.schema
  "Malli schemas for Alethfeld semantic proof graphs.
   Based on orchestrator-prompt-v4.md specification."
  (:require [malli.core :as m]
            [malli.error :as me]
            [validate-graph.config :as config]))

;; =============================================================================
;; Primitive Schemas
;; =============================================================================

(def NodeId
  "Node IDs are keywords with format :<depth>-<uuid-prefix> or special like :theorem"
  :keyword)

(def ContentHash
  "SHA256 hash prefix (configurable length hex string)"
  [:re {:error/message (str "Content hash must be " config/content-hash-length " lowercase hex characters")}
   config/content-hash-pattern])

(def ISO8601
  "ISO 8601 datetime string"
  [:re {:error/message "Must be ISO 8601 format: YYYY-MM-DDTHH:MM:SS"}
   #"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}"])

(def LaTeXString
  "LaTeX mathematical statement (non-empty string)"
  [:string {:min 1 :error/message "Statement must be a non-empty string"}])

;; =============================================================================
;; Enum Schemas
;; =============================================================================

(def NodeType
  "All valid node types"
  [:enum {:error/message "Invalid node type. Must be one of: assumption, local-assume, local-discharge, definition, claim, lemma-ref, external-ref, qed"}
   :assumption        ; global hypothesis (from theorem statement)
   :local-assume      ; scoped assumption introduction
   :local-discharge   ; discharges a local-assume
   :definition        ; definition introduction
   :claim             ; proof step
   :lemma-ref         ; reference to extracted/proven lemma
   :external-ref      ; reference to external result
   :qed])             ; concludes a subproof

(def Justification
  "All valid justification rules"
  [:enum
   :assumption
   :local-assumption
   :discharge
   :definition-expansion
   :substitution
   :modus-ponens
   :universal-elim
   :universal-intro
   :existential-intro
   :existential-elim
   :equality-rewrite
   :algebraic-rewrite
   :case-split
   :induction-base
   :induction-step
   :contradiction
   :conjunction-intro
   :conjunction-elim
   :disjunction-intro
   :disjunction-elim
   :implication-intro
   :lemma-application
   :external-application
   :admitted
   :qed])

(def NodeStatus
  "Verification status of a node"
  [:enum {:error/message "Invalid status. Must be: proposed, verified, admitted, or rejected"}
   :proposed :verified :admitted :rejected])

(def TaintStatus
  "Taint propagation status"
  [:enum {:error/message "Invalid taint. Must be: clean, tainted, or self-admitted"}
   :clean :tainted :self-admitted])

(def ProofMode
  "Proof mode determines strictness level"
  [:enum {:error/message "Invalid proof mode. Must be: strict-mathematics, formal-physics, or algebraic-derivation"}
   :strict-mathematics :formal-physics :algebraic-derivation])

(def CreatedBy
  "Who created this node"
  [:enum :prover :orchestrator :extraction])

(def SymbolScope
  "Where a symbol is valid"
  [:or
   [:enum :global :lemma]
   :keyword])  ; could be :<lemma-id>

(def ExternalVerificationStatus
  "Status of external reference verification"
  [:enum :pending :verified :mismatch :not-found :metadata-only])

(def LemmaStatus
  "Status of an extracted lemma"
  [:enum :pending :proven :tainted])

;; =============================================================================
;; Composite Schemas
;; =============================================================================

(def Provenance
  "Provenance information for a node"
  [:map
   [:created-at ISO8601]
   [:created-by CreatedBy]
   [:round :int]
   [:revision-of {:optional true} [:maybe NodeId]]])

(def Node
  "A node in the semantic proof graph"
  [:map
   [:id NodeId]
   [:type NodeType]
   [:statement LaTeXString]
   [:content-hash ContentHash]
   [:dependencies [:set NodeId]]
   [:scope [:set NodeId]]
   [:justification Justification]
   [:status NodeStatus]
   [:taint TaintStatus]
   [:depth [:int {:min 0}]]
   [:parent {:optional true} [:maybe NodeId]]
   [:display-order :int]
   [:provenance Provenance]
   ;; Optional fields based on node type
   [:introduces {:optional true} :string]           ; for :local-assume
   [:discharges {:optional true} NodeId]            ; for :local-discharge
   [:lemma-id {:optional true} :string]             ; for :lemma-ref
   [:external-id {:optional true} :string]          ; for :external-ref
   [:assumption-label {:optional true} :keyword]])  ; for :assumption (e.g., :A1)

(def Symbol
  "A symbol declaration"
  [:map
   [:id :keyword]
   [:name :string]
   [:type :string]
   [:tex :string]
   [:constraints {:optional true} :string]
   [:scope SymbolScope]
   [:introduced-at NodeId]])

(def BibData
  "Bibliographic data for external references"
  [:map
   [:authors [:vector :string]]
   [:title :string]
   [:year :int]
   [:journal {:optional true} :string]])

(def ExternalRef
  "An external reference (literature citation)"
  [:map
   [:id :string]
   [:doi {:optional true} [:maybe :string]]
   [:arxiv {:optional true} [:maybe :string]]
   [:url {:optional true} [:maybe :string]]
   [:claimed-statement :string]
   [:verified-statement {:optional true} [:maybe :string]]
   [:verification-status ExternalVerificationStatus]
   [:bibdata {:optional true} [:maybe BibData]]
   [:notes {:optional true} [:maybe :string]]])

(def Lemma
  "An extracted lemma"
  [:map
   [:id :string]
   [:name :string]
   [:statement LaTeXString]
   [:content-hash ContentHash]
   [:root-node NodeId]
   [:status LemmaStatus]
   [:taint TaintStatus]
   [:extracted-nodes [:set NodeId]]
   [:proof-graph-id {:optional true} [:maybe :string]]])

(def Obligation
  "A proof obligation (from admitted steps)"
  [:map
   [:node-id NodeId]
   [:claim :string]
   [:context [:map
              [:assumptions [:vector :any]]
              [:scope [:vector :any]]]]])

(def ContextBudget
  "Context window budget tracking"
  [:map
   [:max-tokens :int]
   [:current-estimate :int]])

(def IterationCounts
  "Iteration counters for various phases"
  [:map
   [:verification [:map-of NodeId :int]]
   [:expansion [:map-of NodeId :int]]
   [:strategy :int]])

(def Metadata
  "Graph metadata"
  [:map
   [:created-at ISO8601]
   [:last-modified ISO8601]
   [:proof-mode ProofMode]
   [:iteration-counts IterationCounts]
   [:context-budget ContextBudget]])

(def Theorem
  "The theorem being proved"
  [:map
   [:id [:= :theorem]]
   [:statement LaTeXString]
   [:content-hash ContentHash]])

(def SemanticGraph
  "The complete semantic proof graph"
  [:map
   [:graph-id :string]
   [:version [:int {:min 1}]]
   [:theorem Theorem]
   [:nodes [:map-of NodeId Node]]
   [:symbols [:map-of :keyword Symbol]]
   [:external-refs [:map-of :string ExternalRef]]
   [:lemmas [:map-of :string Lemma]]
   [:obligations [:vector Obligation]]
   [:archived-nodes [:map-of NodeId Node]]
   [:metadata Metadata]])

;; =============================================================================
;; Validation Functions
;; =============================================================================

(defn validate-schema
  "Validate a graph against the schema. Returns {:valid true} or {:valid false :errors [...]}."
  [graph]
  (if (m/validate SemanticGraph graph)
    {:valid true}
    {:valid false
     :errors (me/humanize (m/explain SemanticGraph graph))}))

(defn explain-schema
  "Get detailed explanation of schema violations."
  [graph]
  (m/explain SemanticGraph graph))
