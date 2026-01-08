(ns alethfeld.schema.enums
  "Enumeration schemas for Alethfeld semantic proof graphs.
   Defines all valid enum values for node types, statuses, and modes.")

;; =============================================================================
;; Node Type Enums
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

;; =============================================================================
;; Status Enums
;; =============================================================================

(def NodeStatus
  "Verification status of a node"
  [:enum {:error/message "Invalid status. Must be: proposed, verified, admitted, or rejected"}
   :proposed :verified :admitted :rejected])

(def TaintStatus
  "Taint propagation status"
  [:enum {:error/message "Invalid taint. Must be: clean, tainted, or self-admitted"}
   :clean :tainted :self-admitted])

(def ExternalVerificationStatus
  "Status of external reference verification"
  [:enum :pending :verified :mismatch :not-found :metadata-only])

(def LemmaStatus
  "Status of an extracted lemma"
  [:enum :pending :proven :tainted])

;; =============================================================================
;; Mode Enums
;; =============================================================================

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

;; =============================================================================
;; Verification Log Enums
;; =============================================================================

(def RigorLevel
  "Rigor level for verification"
  [:enum :strictest :strict :moderate :lenient])

(def QuantifierStatus
  "Status of quantifier handling in a step"
  [:enum :explicit :implicit-universal :universal-implicit :universal :implicit :na])

(def GapStatus
  "Whether gaps were identified"
  [:enum :none :minor :significant])

(def TypeStatus
  "Type consistency check result"
  [:enum :consistent :inconsistent :na])

(def VerificationVerdict
  "Verdict for a single node verification"
  [:enum :accept :reject :challenge :admit])
