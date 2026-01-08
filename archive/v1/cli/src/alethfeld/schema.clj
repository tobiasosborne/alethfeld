(ns alethfeld.schema
  "Malli schemas for Alethfeld semantic proof graphs.

   This namespace provides the public API for schema validation.
   Schemas are organized into domain-specific submodules:

   - alethfeld.schema.primitives  - Basic types (NodeId, ContentHash, ISO8601, LaTeXString)
   - alethfeld.schema.enums       - Enum types (NodeType, Justification, NodeStatus, etc.)
   - alethfeld.schema.node        - Node schemas (Node, NodePartial, Provenance)
   - alethfeld.schema.graph       - Graph schemas (SemanticGraph, Symbol, ExternalRef, Lemma, etc.)
   - alethfeld.schema.verification - Verification log schemas"
  (:require [malli.core :as m]
            [malli.error :as me]
            ;; Import all schema submodules
            [alethfeld.schema.primitives :as primitives]
            [alethfeld.schema.enums :as enums]
            [alethfeld.schema.node :as node]
            [alethfeld.schema.graph :as graph]
            [alethfeld.schema.verification :as verification]))

;; =============================================================================
;; Re-exported Primitive Schemas
;; =============================================================================

(def NodeId primitives/NodeId)
(def ContentHash primitives/ContentHash)
(def ISO8601 primitives/ISO8601)
(def LaTeXString primitives/LaTeXString)

;; =============================================================================
;; Re-exported Enum Schemas
;; =============================================================================

(def NodeType enums/NodeType)
(def Justification enums/Justification)
(def NodeStatus enums/NodeStatus)
(def TaintStatus enums/TaintStatus)
(def ProofMode enums/ProofMode)
(def CreatedBy enums/CreatedBy)
(def SymbolScope enums/SymbolScope)
(def ExternalVerificationStatus enums/ExternalVerificationStatus)
(def LemmaStatus enums/LemmaStatus)
(def RigorLevel enums/RigorLevel)
(def QuantifierStatus enums/QuantifierStatus)
(def GapStatus enums/GapStatus)
(def TypeStatus enums/TypeStatus)
(def VerificationVerdict enums/VerificationVerdict)

;; =============================================================================
;; Re-exported Node Schemas
;; =============================================================================

(def Provenance node/Provenance)
(def Node node/Node)
(def NodePartial node/NodePartial)

;; =============================================================================
;; Re-exported Graph Schemas
;; =============================================================================

(def Symbol graph/Symbol)
(def BibData graph/BibData)
(def ExternalRef graph/ExternalRef)
(def Lemma graph/Lemma)
(def Obligation graph/Obligation)
(def ContextBudget graph/ContextBudget)
(def IterationCounts graph/IterationCounts)
(def Metadata graph/Metadata)
(def Theorem graph/Theorem)
(def SemanticGraph graph/SemanticGraph)

;; =============================================================================
;; Re-exported Verification Schemas
;; =============================================================================

(def RigorCheck verification/RigorCheck)
(def VerificationResult verification/VerificationResult)
(def VerificationSession verification/VerificationSession)
(def ExternalReferenceLog verification/ExternalReferenceLog)
(def VerificationSummary verification/VerificationSummary)
(def FinalVerdict verification/FinalVerdict)
(def VerificationLog verification/VerificationLog)

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

(defn validate-node
  "Validate a node against the Node schema."
  [node]
  (if (m/validate Node node)
    {:valid true}
    {:valid false
     :errors (me/humanize (m/explain Node node))}))

(defn validate-partial-node
  "Validate a partial node (for add-node input)."
  [node]
  (if (m/validate NodePartial node)
    {:valid true}
    {:valid false
     :errors (me/humanize (m/explain NodePartial node))}))

(defn validate-verification-log
  "Validate a verification log against the VerificationLog schema."
  [log]
  (if (m/validate VerificationLog log)
    {:valid true}
    {:valid false
     :errors (me/humanize (m/explain VerificationLog log))}))

(defn explain-schema
  "Get detailed explanation of schema violations."
  [graph]
  (m/explain SemanticGraph graph))
