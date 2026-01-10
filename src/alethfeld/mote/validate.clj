(ns alethfeld.mote.validate
  "Validation functions for motes, proposals, and votes."
  (:require [alethfeld.schema :as s]))

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
