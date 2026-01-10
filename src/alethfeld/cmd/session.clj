(ns alethfeld.cmd.session
  "Session management commands: claim, unclaim, done."
  (:require [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [alethfeld.mote :as mote]
            [alethfeld.session :as session]
            [alethfeld.cmd.core :as core]))

;; -----------------------------------------------------------------------------
;; Claim Command
;; -----------------------------------------------------------------------------

(defn cmd-claim!
  "Claim a mote for work with a role-based session.

   Arguments (in context):
   - :id - The mote ID to claim (required)

   Options:
   - :agent - Agent name (required)
   - :role - Role for this session (required)
           One of: proposer, advisor, prover, verifier, ref-checker, counterexample
   - :dry-run - Show what would happen without executing

   Errors if mote is already claimed by another agent.

   Returns the updated mote with :session-id."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [name role dry-run]} options
        agent name]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to claim"]})))

    (when-not agent
      (throw (ex-info "Agent name is required"
                      {:type :validation-failed
                       :errors ["Provide --name to claim the mote"]})))

    (when-not role
      (throw (ex-info "Role is required"
                      {:type :validation-failed
                       :errors ["Provide --role (proposer, advisor, prover, verifier, ref-checker, counterexample)"]})))

    ;; Validate role is valid
    (when-not (contains? session/role-actions role)
      (throw (ex-info "Invalid role"
                      {:type :validation-failed
                       :errors [(str "Invalid role: " role
                                     ". Must be one of: proposer, advisor, prover, verifier, ref-checker, counterexample")]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Check if already claimed by another agent
      (when-let [current-claimer (:claimed-by current-mote)]
        (when (not= current-claimer agent)
          (throw (ex-info "Mote already claimed"
                          {:type :already-claimed
                           :mote-id id
                           :claimed-by current-claimer}))))

      (if dry-run
        ;; Dry run - show what would happen
        (core/dry-run-result
         :output (str "Would claim mote " id " for agent \"" agent "\" as " (clojure.core/name role)
                      (core/format-would-create
                       [(str "session for " agent " on " id " as " (clojure.core/name role))])
                      (core/format-would-update
                       [{:id id :change (str "set claimed-by to \"" agent "\"")}]))
         :would-create [{:type :session :agent agent :mote-id id :role role}]
         :would-update [{:id id :change (str "claimed-by: " agent)}]
         :next-actions [(core/show-action id)
                        (core/ready-action)])

        ;; Execute
        (do
          ;; Ensure session directories exist
          (session/ensure-session-dirs! repo-path)

          ;; Create session with configurable timeout
          (let [config (store/load-config repo-path)
                session-timeout (or (:session-timeout-minutes config) 30)
                sess (session/create-session! repo-path id role agent
                                              :duration-minutes session-timeout)
                session-id (:session-id sess)
                updated-mote (mote/set-claimed-by current-mote agent)]
            (tx/atomic-write! repo-path
                              (str "Claim mote " id " for " agent " as " (clojure.core/name role))
                              [updated-mote])
            (assoc updated-mote
                   :session-id session-id
                   :next-actions (conj
                                  (case role
                                    :verifier [(core/vote-action id session-id :for)
                                               (core/vote-action id session-id :against)]
                                    :advisor [(core/approve-action id session-id)
                                              (core/reject-action id session-id)]
                                    :proposer [(core/make-action (str "af propose " id " --session " session-id " --claim \"...\"")
                                                            "Submit decomposition proposal")]
                                    :prover [(core/make-action (str "af add-ref " id " --session " session-id " --ref \"...\"")
                                                          "Add external reference")]
                                    :ref-checker [(core/make-action (str "af add-ref " id " --session " session-id " --ref \"...\"")
                                                               "Add/update references")]
                                    :counterexample [(core/vote-action id session-id :for)
                                                     (core/vote-action id session-id :against)]
                                    [])
                                  (core/done-action session-id)))))))))

;; -----------------------------------------------------------------------------
;; Unclaim Command
;; -----------------------------------------------------------------------------

(defn cmd-unclaim!
  "Release claim on a mote.

   Arguments (in context):
   - :id - The mote ID to unclaim (required)

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Note: Prefer using 'af done' which properly ends the session.
   This command releases the claim but does not end the session.

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to unclaim"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (lighter validation - any session holder can unclaim, skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      (if dry-run?
        ;; Dry run - show what would happen
        (core/dry-run-result
         :output (str "Would release claim on mote " id
                      (when (:claimed-by current-mote)
                        (str " (currently claimed by \"" (:claimed-by current-mote) "\")"))
                      (core/format-would-update
                       [{:id id :change "clear claimed-by"}]))
         :would-update [{:id id :change "clear claimed-by"}]
         :next-actions [(core/ready-action)
                        (core/status-action)])

        ;; Execute (session already validated by middleware with validate-only mode)
        (let [updated-mote (mote/clear-claim current-mote)]
          (tx/atomic-write! repo-path
                            (str "Unclaim mote " id)
                            [updated-mote])
          (assoc updated-mote
                 :next-actions [(core/ready-action)
                                (core/status-action)]))))))

;; -----------------------------------------------------------------------------
;; Done Command
;; -----------------------------------------------------------------------------

(defn cmd-done!
  "End a session and release the claimed mote.

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Ends the active session and releases the mote for other agents.
   The session is moved to the completed directory with stats recorded.

   Returns map with:
   - :session-id - The session that was ended
   - :mote-id - The mote that was released
   - :action-count - Number of actions performed in the session"
  [{:keys [options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with the session token"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load and validate session
    (let [sess (session/load-active-session repo-path session-id)]
      (when-not sess
        (throw (ex-info "Session not found or already ended"
                        {:type :session-not-found
                         :session-id session-id})))

      ;; Check session is not expired
      (when (session/session-expired? sess)
        (throw (ex-info "Session has expired"
                        {:type :session-expired
                         :session-id session-id
                         :expires-at (:expires-at sess)})))

      (let [mote-id (:mote-id sess)
            mote (store/load-mote repo-path mote-id)]

        ;; Mote should exist (integrity check)
        (when-not mote
          (throw (ex-info "Mote not found for session"
                          {:type :integrity-error
                           :session-id session-id
                           :mote-id mote-id})))

        (if dry-run?
          ;; Dry run - show what would happen
          (core/dry-run-result
           :output (str "Would end session " session-id
                        "\n\nSession info:"
                        "\n  Agent: " (:agent sess)
                        "\n  Mote: " mote-id
                        "\n  Role: " (name (:role sess))
                        "\n  Actions: " (:action-count sess 0)
                        (core/format-would-delete
                         [(str "session " session-id)])
                        (core/format-would-update
                         [{:id mote-id :change "clear claimed-by"}]))
           :would-delete [(str "session " session-id)]
           :would-update [{:id mote-id :change "clear claimed-by"}]
           :next-actions [(core/ready-action)
                          (core/status-action)])

          ;; Execute
          (let [ended-session (session/end-session! repo-path session-id :record-stats true)
                updated-mote (mote/clear-claim mote)]

            ;; Commit the changes
            (tx/atomic-write! repo-path
                              (str "Done: end session for " mote-id)
                              [updated-mote])

            {:session-id session-id
             :mote-id mote-id
             :action-count (:action-count ended-session)
             ;; CRITICAL: Agent termination message (alethfeld-atkc)
             :agent-should-terminate true
             :message "Session ended successfully."
             :terminate-message (str "\nYour work is complete. This agent should now terminate.\n\n"
                                     "To start new work, spawn a fresh agent:\n"
                                     "  af ready --agent <new-name>")
             :next-actions [(core/make-action "# Agent should terminate now" "Work complete - end this agent")
                            (core/make-action "af ready --agent <new-name>" "Start fresh agent for new work")]}))))))
