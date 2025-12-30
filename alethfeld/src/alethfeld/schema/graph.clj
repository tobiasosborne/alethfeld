(ns alethfeld.schema.graph
  "Graph-level schemas for Alethfeld semantic proof graphs.
   Defines the complete graph structure and its components."
  (:require [alethfeld.schema.primitives :as prim]
            [alethfeld.schema.enums :as enums]
            [alethfeld.schema.node :as node]))

;; =============================================================================
;; Symbol Table
;; =============================================================================

(def Symbol
  "A symbol declaration"
  [:map
   [:id :keyword]
   [:name :string]
   [:type :string]
   [:tex :string]
   [:constraints {:optional true} :string]
   [:scope enums/SymbolScope]
   [:introduced-at prim/NodeId]])

;; =============================================================================
;; External References
;; =============================================================================

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
   [:verification-status enums/ExternalVerificationStatus]
   [:bibdata {:optional true} [:maybe BibData]]
   [:notes {:optional true} [:maybe :string]]])

;; =============================================================================
;; Lemmas
;; =============================================================================

(def Lemma
  "An extracted lemma"
  [:map
   [:id :string]
   [:name :string]
   [:statement prim/LaTeXString]
   [:content-hash prim/ContentHash]
   [:root-node prim/NodeId]
   [:status enums/LemmaStatus]
   [:taint enums/TaintStatus]
   [:extracted-nodes [:set prim/NodeId]]
   [:proof-graph-id {:optional true} [:maybe :string]]])

;; =============================================================================
;; Obligations
;; =============================================================================

(def Obligation
  "A proof obligation (from admitted steps)"
  [:map
   [:node-id prim/NodeId]
   [:claim :string]
   [:context [:map
              [:assumptions [:vector :any]]
              [:scope [:vector :any]]]]])

;; =============================================================================
;; Metadata
;; =============================================================================

(def ContextBudget
  "Context window budget tracking"
  [:map
   [:max-tokens :int]
   [:current-estimate :int]])

(def IterationCounts
  "Iteration counters for various phases"
  [:map
   [:verification [:map-of prim/NodeId :int]]
   [:expansion [:map-of prim/NodeId :int]]
   [:strategy :int]])

(def Metadata
  "Graph metadata"
  [:map
   [:created-at prim/ISO8601]
   [:last-modified prim/ISO8601]
   [:proof-mode enums/ProofMode]
   [:iteration-counts IterationCounts]
   [:context-budget ContextBudget]])

;; =============================================================================
;; Theorem & Complete Graph
;; =============================================================================

(def Theorem
  "The theorem being proved"
  [:map
   [:id [:= :theorem]]
   [:statement prim/LaTeXString]
   [:content-hash prim/ContentHash]])

(def SemanticGraph
  "The complete semantic proof graph"
  [:map
   [:graph-id :string]
   [:version [:int {:min 1}]]
   [:theorem Theorem]
   [:nodes [:map-of prim/NodeId node/Node]]
   [:symbols [:map-of :keyword Symbol]]
   [:external-refs [:map-of :string ExternalRef]]
   [:lemmas [:map-of :string Lemma]]
   [:obligations [:vector Obligation]]
   [:archived-nodes [:map-of prim/NodeId node/Node]]
   [:metadata Metadata]])
