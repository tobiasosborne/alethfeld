(ns alethfeld.cmd.show
  "Show command implementation."
  (:require [alethfeld.store :as store]
            [alethfeld.cmd.core :as core]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Quorum Display Helpers
;; -----------------------------------------------------------------------------

(defn- format-vote-quorum-progress
  "Format vote counts with quorum progress.

   Arguments:
   - for-votes: Number of votes for
   - against-votes: Number of votes against
   - quorum: Required quorum threshold

   Returns string like '1/2 for, 0 against (need 1 more for quorum)'"
  [for-votes against-votes quorum]
  (let [total-votes (+ for-votes against-votes)
        votes-needed (- quorum total-votes)
        base-str (str for-votes "/" quorum " for, " against-votes " against")]
    (if (pos? votes-needed)
      (str base-str " (need " votes-needed " more for quorum)")
      base-str)))

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

   Arguments:
   - mote: The mote to display
   - vote-quorum: The quorum threshold for votes (default 1)
   - proposal-quorum: The quorum threshold for proposal votes (default 1)

   Returns a detailed human-readable string."
  [mote vote-quorum proposal-quorum]
  (let [sep (apply str (repeat 40 "-"))
        for-votes (count (filter #(= :for (:type %)) (:votes mote)))
        against-votes (count (filter #(= :against (:type %)) (:votes mote)))]
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
           (let [proposal-for (count (filter #(= :approve (:vote %)) (:votes proposal)))
                 proposal-against (count (filter #(= :reject (:vote %)) (:votes proposal)))
                 proposal-total (+ proposal-for proposal-against)
                 proposal-needed (- proposal-quorum proposal-total)]
             (str "\nProposal:\n"
                  "  Proposer: " (:proposer proposal) "\n"
                  "  Children: " (str/join ", " (:children proposal)) "\n"
                  (when (seq (:votes proposal))
                    (str "  Votes: " proposal-for "/" proposal-quorum " approve, " proposal-against " reject"
                         (when (pos? proposal-needed)
                           (str " (need " proposal-needed " more for quorum)"))
                         "\n")))))
         (when (seq (:votes mote))
           (str "\nVotes: " (format-vote-quorum-progress for-votes against-votes vote-quorum) "\n"))
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
  [{:keys [id options repo-path] :or {repo-path "."}}]
  (let [verbose? (:verbose options)
        mote (store/load-mote repo-path id)]
    (if mote
      (let [config (store/load-config repo-path)
            vote-quorum (or (:vote-quorum config) 1)
            proposal-quorum (or (:proposal-quorum config) 1)
            output (if verbose?
                     (format-show-verbose mote vote-quorum proposal-quorum)
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
