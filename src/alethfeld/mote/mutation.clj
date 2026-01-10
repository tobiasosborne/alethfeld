(ns alethfeld.mote.mutation
  "Mote transformation functions."
  (:require [alethfeld.mote.util :as util]))

;; -----------------------------------------------------------------------------
;; Mote Transformations (Pure Functions)
;; -----------------------------------------------------------------------------

(defn- touch
  "Update the :updated-at timestamp."
  [mote]
  (assoc mote :updated-at (util/now)))

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

(defn add-dep
  "Add a dependency to a mote. Returns new mote."
  [mote dependency]
  (-> mote
      (update :depends-on (fnil conj []) dependency)
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
      (assoc :claimed-at (util/now))
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
