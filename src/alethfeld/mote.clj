(ns alethfeld.mote
  "Mote constructor and manipulation functions.

   Re-exports all public APIs from submodules for backward compatibility.
   Existing code using [alethfeld.mote :as mote] will continue to work
   unchanged after internal module reorganization."
  (:require [alethfeld.mote.util :as util]
            [alethfeld.mote.vote :as vote]
            [alethfeld.mote.core :as core]
            [alethfeld.mote.validate :as validate]
            [alethfeld.mote.mutation :as mutation]))

;; =============================================================================
;; Re-exports from alethfeld.mote.util
;; =============================================================================

(def generate-id
  "Generate a unique ID suffix for proposals/jobs."
  util/generate-id)

(def ^:dynamic *clock*
  "Clock function for getting current time. Rebindable for testing."
  util/*clock*)

(def now
  "Returns current time. Uses *clock* which can be rebound in tests."
  util/now)

(def claim-expired?
  "Check if a mote's claim has expired."
  util/claim-expired?)

;; =============================================================================
;; Re-exports from alethfeld.mote.vote
;; =============================================================================

(def make-vote
  "Create a verification vote."
  vote/make-vote)

(def make-proposal-vote
  "Create a proposal vote (approve/reject)."
  vote/make-proposal-vote)

(def make-proposal
  "Create a decomposition proposal."
  vote/make-proposal)

;; =============================================================================
;; Re-exports from alethfeld.mote.core
;; =============================================================================

(def make-mote
  "Create a mote with explicit values. Low-level constructor."
  core/make-mote)

(def make-root-mote
  "Create a root mote (no parent)."
  core/make-root-mote)

(def make-child-mote
  "Create a child mote, inheriting priority/difficulty from parent."
  core/make-child-mote)

;; =============================================================================
;; Re-exports from alethfeld.mote.validate
;; =============================================================================

(def valid-mote?
  "Check if mote is valid according to schema."
  validate/valid-mote?)

(def valid-proposal?
  "Check if proposal is valid according to schema."
  validate/valid-proposal?)

(def valid-vote?
  "Check if vote is valid according to schema."
  validate/valid-vote?)

(def valid-proposal-vote?
  "Check if proposal vote is valid according to schema."
  validate/valid-proposal-vote?)

;; =============================================================================
;; Re-exports from alethfeld.mote.mutation
;; =============================================================================

(def add-assumption
  "Add an assumption to a mote. Returns new mote."
  mutation/add-assumption)

(def add-definition
  "Add a definition to a mote. Returns new mote."
  mutation/add-definition)

(def add-dep
  "Add a dependency to a mote. Returns new mote."
  mutation/add-dep)

(def add-vote
  "Add a verification vote to a mote. Returns new mote."
  mutation/add-vote)

(def add-taint
  "Add a taint flag to a mote. Returns new mote."
  mutation/add-taint)

(def remove-taint
  "Remove a taint flag from a mote. Returns new mote."
  mutation/remove-taint)

(def set-status
  "Set the status of a mote. Returns new mote."
  mutation/set-status)

(def set-claimed-by
  "Set the claimed-by field of a mote. Returns new mote."
  mutation/set-claimed-by)

(def clear-claim
  "Clear the claim on a mote. Returns new mote."
  mutation/clear-claim)

(def set-proposal
  "Set an active proposal on a mote. Returns new mote."
  mutation/set-proposal)

(def clear-proposal
  "Clear the proposal from a mote. Returns new mote."
  mutation/clear-proposal)

(def add-child
  "Add a child ID to a mote. Returns new mote."
  mutation/add-child)

(def set-priority
  "Set the priority of a mote. Returns new mote."
  mutation/set-priority)

(def set-difficulty
  "Set the difficulty of a mote. Returns new mote."
  mutation/set-difficulty)

(def set-claim
  "Update the claim text of a mote. Returns new mote."
  mutation/set-claim)
