(ns alethfeld.cmd.core
  "Shared helpers for CLI command implementations.

   This namespace provides:
   - Role detection helpers for smart hinting
   - Next-action builders for workflow guidance
   - Dry-run formatting utilities"
  (:require [alethfeld.store :as store]
            [alethfeld.id :as id]
            [alethfeld.session :as session]
            [alethfeld.verify :as verify]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Role Detection Helpers
;; -----------------------------------------------------------------------------

(def role-names
  "Set of known role names as strings (lowercase)."
  #{"proposer" "advisor" "prover" "verifier" "ref-checker" "counterexample"})

(defn name-looks-like-role?
  "Check if a name matches a known role name.
   Returns the matching role name if found, nil otherwise."
  [name]
  (when name
    (let [lower-name (str/lower-case (str name))]
      (when (contains? role-names lower-name)
        lower-name))))

(defn format-role-hint
  "Format a hint message when --name matches a role name."
  [name]
  (str "Note: \"" name "\" looks like a role name.\n"
       "Did you mean: af ready --name <your-name> --role " name "?\n\n"))

;; -----------------------------------------------------------------------------
;; Next Actions Helpers
;; -----------------------------------------------------------------------------

(defn make-action
  "Create a next-action map."
  [command description]
  {:command command :description description})

(defn done-action
  "Create the standard 'af done' action for a session."
  [session-id]
  (make-action (str "af done --session " session-id)
               "End session (work complete)"))

(defn show-action
  "Create an 'af show' action for a mote."
  [mote-id]
  (make-action (str "af show " mote-id)
               "View mote details"))

(defn tree-action
  "Create an 'af tree' action for a mote."
  [mote-id]
  (make-action (str "af tree " mote-id)
               "View proof structure"))

(defn status-action
  "Create an 'af status' action."
  []
  (make-action "af status" "View project overview"))

(defn ready-action
  "Create an 'af ready' action for starting work."
  []
  (make-action "af ready --agent <name>" "Get assigned a task"))

(defn vote-action
  "Create a vote action for a mote."
  [mote-id session-id direction]
  (let [flag (if (= direction :for) "--for" "--against")]
    (make-action (str "af vote " mote-id " " flag " --session " session-id " --reason \"...\"")
                 (if (= direction :for) "Vote claim is valid" "Vote claim is invalid"))))

(defn approve-action
  "Create an approve action for a proposal."
  [mote-id session-id]
  (make-action (str "af approve " mote-id " --session " session-id)
               "Approve the proposal"))

(defn reject-action
  "Create a reject action for a proposal."
  [mote-id session-id]
  (make-action (str "af reject " mote-id " --session " session-id)
               "Reject the proposal"))

(defn find-votable-siblings
  "Find siblings of a mote that need verification and the agent can vote on.

   Returns a vector of mote IDs."
  [repo-path mote-id agent]
  (when-let [parent-id (id/parent-id mote-id)]
    (when-let [parent (store/load-mote repo-path parent-id)]
      (let [sibling-ids (remove #{mote-id} (:children parent))
            motes (store/load-all-motes repo-path)]
        (->> sibling-ids
             (filter (fn [sib-id]
                       (when-let [sib (get motes sib-id)]
                         (and (verify/needs-verification? sib)
                              (session/can-vote? sib agent)
                              (not (verify/has-voted? sib agent))))))
             vec)))))

(defn generate-vote-next-actions
  "Generate intelligent next-actions after a vote based on current state.

   Logic from AGENT-UX-PLAN.md Section 3.2:
   - If quorum not reached: 'Waiting for N more votes'
   - If quorum reached and more siblings need voting: 'Continue: af vote 1.2'
   - If all siblings done or no siblings: 'af done'"
  [repo-path mote-id session-id agent quorum-status]
  (let [;; Check for votable siblings
        votable-siblings (find-votable-siblings repo-path mote-id agent)]
    (cond
      ;; Quorum not yet reached - suggest waiting or done
      (= :pending quorum-status)
      [(make-action "# Waiting for more votes" "Other verifiers need to vote")
       (done-action session-id)]

      ;; Quorum reached, but there are more siblings to vote on
      (seq votable-siblings)
      (let [next-sibling (first votable-siblings)]
        [(vote-action next-sibling session-id :for)
         (vote-action next-sibling session-id :against)
         (done-action session-id)])

      ;; All done - suggest ending session
      :else
      [(done-action session-id)])))

;; -----------------------------------------------------------------------------
;; Dry Run Helpers
;; -----------------------------------------------------------------------------

(defn format-dry-run-header
  "Format the dry-run header banner."
  []
  "DRY RUN - No changes made\n")

(defn format-dry-run-footer
  "Format the dry-run footer with execution hint."
  []
  "\nRun without --dry-run to execute.")

(defn format-would-create
  "Format a 'would create' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould create:\n"
         (str/join "\n"
                   (for [item items]
                     (if (map? item)
                       (str "  " (:id item) " [" (name (:status item :proposed)) "] " (:claim item))
                       (str "  " item)))))))

(defn format-would-update
  "Format a 'would update' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould update:\n"
         (str/join "\n"
                   (for [item items]
                     (if (map? item)
                       (str "  " (:id item) " -> " (:change item))
                       (str "  " item)))))))

(defn format-would-delete
  "Format a 'would delete' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould delete/archive:\n"
         (str/join "\n"
                   (for [item items]
                     (str "  " item))))))

(defn dry-run-result
  "Create a standard dry-run result map.

   Arguments:
   - output: The formatted dry-run output string
   - would-create: Vector of items that would be created
   - would-update: Vector of items that would be updated
   - would-delete: Vector of items that would be deleted

   Returns a map suitable for dry-run command results."
  [& {:keys [output would-create would-update would-delete next-actions]}]
  {:dry-run true
   :output (str (format-dry-run-header)
                output
                (format-dry-run-footer))
   :would-create (vec would-create)
   :would-update (vec would-update)
   :would-delete (vec would-delete)
   :next-actions (or next-actions [(status-action)])})
