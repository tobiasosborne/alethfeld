(ns alethfeld.schema.verification
  "Verification log schemas for Alethfeld semantic proof graphs.
   Defines the structure of verification results and logs."
  (:require [alethfeld.schema.primitives :as prim]
            [alethfeld.schema.enums :as enums]))

;; =============================================================================
;; Rigor Check Schemas
;; =============================================================================

(def RigorCheck
  "Result of rigor check for a verification step"
  [:map
   [:quantifiers enums/QuantifierStatus]
   [:types enums/TypeStatus]
   [:gaps enums/GapStatus]])

;; =============================================================================
;; Verification Result Schemas
;; =============================================================================

(def VerificationResult
  "Result of verifying a single node"
  [:map
   [:node-id prim/NodeId]
   [:verdict enums/VerificationVerdict]
   [:reason :string]
   [:rigor-check {:optional true} RigorCheck]])

(def VerificationSession
  "Metadata about the verification session"
  [:map
   [:graph-id :string]
   [:verifier-mode {:optional true} enums/ProofMode]
   [:rigor-level {:optional true} enums/RigorLevel]
   [:timestamp {:optional true} :string]])

;; =============================================================================
;; External Reference Log
;; =============================================================================

(def ExternalReferenceLog
  "External reference as logged in verification"
  [:map
   [:id :keyword]
   [:doi {:optional true} :string]
   [:arxiv {:optional true} :string]
   [:verification-status enums/ExternalVerificationStatus]
   [:found-statement {:optional true} :string]
   [:bibdata {:optional true} [:map
                               [:authors [:vector :string]]
                               [:title :string]
                               [:journal {:optional true} :string]
                               [:year :int]
                               [:volume {:optional true} :int]
                               [:pages {:optional true} :string]]]
   [:notes {:optional true} :string]])

;; =============================================================================
;; Summary & Verdict
;; =============================================================================

(def VerificationSummary
  "Summary of verification results"
  [:map
   [:total-nodes :int]
   [:verified :int]
   [:rejected :int]
   [:admitted :int]
   [:taint-status enums/TaintStatus]
   [:verification-rounds {:optional true} :int]
   [:challenges-issued {:optional true} :int]
   [:revisions-required {:optional true} :int]])

(def FinalVerdict
  "Final verdict of verification"
  [:map
   [:status [:enum :proven :rejected :admitted :incomplete]]
   [:taint enums/TaintStatus]
   [:confidence {:optional true} [:enum :high :medium :low]]
   [:notes {:optional true} :string]])

;; =============================================================================
;; Complete Verification Log
;; =============================================================================

(def VerificationLog
  "Complete verification log for a proof"
  [:map
   [:verification-session VerificationSession]
   [:verification-results [:vector VerificationResult]]
   [:summary VerificationSummary]
   [:external-references {:optional true} [:vector ExternalReferenceLog]]
   [:obligations {:optional true} [:vector :any]]
   [:final-verdict FinalVerdict]])
