(ns alethfeld.cmd.show
  "Show command implementation."
  (:require [alethfeld.store :as store]
            [alethfeld.cmd.core :as core]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Formatting Helpers
;; -----------------------------------------------------------------------------

(defn- format-show-concise
  "Format concise mote display (default).

   Returns a human-readable summary string."
  [mote]
  (let [status (name (:status mote))
        taints (when (seq (:taint mote))
                 (str " (" (str/join ", " (map name (:taint mote))) ")"))
        claim (:claim mote)]
    (str (:id mote) " [" status "]" taints "\n"
         claim)))

(defn- format-show-verbose
  "Format verbose mote display (with --verbose flag).

   Returns a detailed human-readable string."
  [mote]
  (let [sep (apply str (repeat 40 "-"))]
    (str sep "\n"
         "Mote: " (:id mote) "\n"
         sep "\n"
         "Status: " (name (:status mote)) "\n"
         "Claim: " (:claim mote) "\n"
         "Priority: " (name (:priority mote)) "\n"
         "Difficulty: " (:difficulty mote) "\n"
         (when (seq (:taint mote))
           (str "Taints: " (str/join ", " (map name (:taint mote))) "\n"))
         (when (:claimed-by mote)
           (str "Claimed by: " (:claimed-by mote) "\n"))
         (when (seq (:children mote))
           (str "Children: " (str/join ", " (:children mote)) "\n"))
         (when (:parent mote)
           (str "Parent: " (:parent mote) "\n"))
         (when-let [proposal (:proposal mote)]
           (str "\nProposal:\n"
                "  Proposer: " (:proposer proposal) "\n"
                "  Children: " (str/join ", " (:children proposal)) "\n"
                (when (seq (:votes proposal))
                  (str "  Votes: " (count (:votes proposal)) "\n"))))
         (when (seq (:votes mote))
           (str "\nVotes: " (count (:votes mote))
                " (for: " (count (filter #(= :for (:type %)) (:votes mote)))
                ", against: " (count (filter #(= :against (:type %)) (:votes mote))) ")\n"))
         (when (seq (:assumptions mote))
           (str "\nAssumptions: " (count (:assumptions mote)) "\n"))
         (when (seq (:definitions mote))
           (str "Definitions: " (count (:definitions mote)) "\n"))
         (when (seq (:depends-on mote))
           (str "Dependencies: " (str/join ", " (map :ref (:depends-on mote))) "\n"))
         "\nCreated: " (:created-at mote) " by " (:created-by mote))))

;; -----------------------------------------------------------------------------
;; Show Command
;; -----------------------------------------------------------------------------

(defn cmd-show
  "Display a mote's details.

   Arguments (in context):
   - :id - The mote ID to display

   Options:
   - :verbose - Show detailed output (default: concise)

   Returns the mote map, or throws if not found."
  [{:keys [id options]}]
  (let [repo-path "."
        verbose? (:verbose options)
        mote (store/load-mote repo-path id)]
    (if mote
      (let [output (if verbose?
                     (format-show-verbose mote)
                     (format-show-concise mote))]
        (assoc mote
               :output output
               :verbose? verbose?
               :next-actions [(core/tree-action id)
                              (core/ready-action)
                              (core/status-action)]))
      (throw (ex-info "Mote not found"
                      {:type :not-found
                       :mote-id id})))))
