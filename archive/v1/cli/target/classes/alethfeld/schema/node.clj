(ns alethfeld.schema.node
  "Node schemas for Alethfeld semantic proof graphs.
   Defines the structure of proof nodes including full and partial representations."
  (:require [alethfeld.schema.primitives :as prim]
            [alethfeld.schema.enums :as enums]))

;; =============================================================================
;; Provenance
;; =============================================================================

(def Provenance
  "Provenance information for a node"
  [:map
   [:created-at prim/ISO8601]
   [:created-by enums/CreatedBy]
   [:round :int]
   [:revision-of {:optional true} [:maybe prim/NodeId]]])

;; =============================================================================
;; Node Schemas
;; =============================================================================

(def Node
  "A node in the semantic proof graph"
  [:map
   [:id prim/NodeId]
   [:type enums/NodeType]
   [:statement prim/LaTeXString]
   [:content-hash prim/ContentHash]
   [:dependencies [:set prim/NodeId]]
   [:scope [:set prim/NodeId]]
   [:justification enums/Justification]
   [:status enums/NodeStatus]
   [:taint enums/TaintStatus]
   [:depth [:int {:min 0}]]
   [:parent {:optional true} [:maybe prim/NodeId]]
   [:display-order :int]
   [:provenance Provenance]
   ;; Optional fields based on node type
   [:introduces {:optional true} :string]           ; for :local-assume
   [:discharges {:optional true} prim/NodeId]       ; for :local-discharge
   [:lemma-id {:optional true} :string]             ; for :lemma-ref
   [:external-id {:optional true} :string]          ; for :external-ref
   [:assumption-label {:optional true} :keyword]])  ; for :assumption (e.g., :A1)

(def NodePartial
  "Partial node schema for add-node input (fewer required fields).
   :content-hash, :taint, :status will be computed."
  [:map
   [:id prim/NodeId]
   [:type enums/NodeType]
   [:statement prim/LaTeXString]
   [:dependencies [:set prim/NodeId]]
   [:scope [:set prim/NodeId]]
   [:justification enums/Justification]
   [:depth [:int {:min 0}]]
   [:parent {:optional true} [:maybe prim/NodeId]]
   [:display-order :int]
   ;; Optional computed/defaulted fields
   [:content-hash {:optional true} prim/ContentHash]
   [:status {:optional true} enums/NodeStatus]
   [:taint {:optional true} enums/TaintStatus]
   [:provenance {:optional true} Provenance]
   ;; Optional type-specific fields
   [:introduces {:optional true} :string]
   [:discharges {:optional true} prim/NodeId]
   [:lemma-id {:optional true} :string]
   [:external-id {:optional true} :string]
   [:assumption-label {:optional true} :keyword]])
