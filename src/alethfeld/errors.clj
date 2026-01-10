(ns alethfeld.errors
  "Human-readable error message formatting.

   This module provides:
   - Structured error type definitions
   - User-friendly error messages with actionable hints
   - Error formatting for both EDN and plain text output
   - Role suggestions using Levenshtein distance"
  (:require [clojure.string :as str]
            [alethfeld.util :as util]))

;; -----------------------------------------------------------------------------
;; Role Action Definitions
;; -----------------------------------------------------------------------------

(def role-allowed-actions
  "Map of roles to their allowed actions with example commands."
  {:proposer      {:actions [:propose :done :taint-add]
                   :examples ["af propose 1 --claim \"...\" --session xxx"
                              "af done --session xxx"]}
   :advisor       {:actions [:approve :reject :done :taint-add]
                   :examples ["af approve 1 --session xxx"
                              "af reject 1 --reason \"...\" --session xxx"
                              "af done --session xxx"]}
   :prover        {:actions [:add-ref :add-assumption :add-definition :refine :done :taint-add]
                   :examples ["af add-ref 1.2 --ref \"...\" --session xxx"
                              "af done --session xxx"]}
   :verifier      {:actions [:vote :vote-all :done :taint-add]
                   :examples ["af vote 1.2 --for --session xxx"
                              "af vote 1.2 --against --reason \"...\" --session xxx"
                              "af done --session xxx"]}
   :ref-checker   {:actions [:check-refs :done :taint-add]
                   :examples ["af check-refs 1.2 --session xxx"
                              "af done --session xxx"]}
   :counterexample {:actions [:counterexample :done :taint-add]
                    :examples ["af counterexample 1.2 --example \"...\" --session xxx"
                               "af done --session xxx"]}})

;; -----------------------------------------------------------------------------
;; Role Suggestion
;; -----------------------------------------------------------------------------

(defn suggest-role
  "Suggest a valid role based on Levenshtein distance.
   Returns the best matching role keyword, or nil if no close match.
   Only suggests if the edit distance is <= 4 (reasonable typo threshold).
   This allows for common misspellings like 'reviewer' -> 'verifier'."
  [invalid-role]
  (let [invalid-str (name invalid-role)
        role-distances (for [role (keys util/valid-roles)]
                         {:role role
                          :distance (util/levenshtein-distance invalid-str (name role))})
        best-match (first (sort-by :distance role-distances))]
    (when (and best-match (<= (:distance best-match) 4))
      (:role best-match))))

(defn format-valid-roles
  "Format the list of valid roles with descriptions for display."
  []
  (str/join "\n" (map (fn [[role desc]]
                        (format "  %-13s - %s" (name role) desc))
                      util/valid-roles)))

;; -----------------------------------------------------------------------------
;; Error Message Formatters
;; -----------------------------------------------------------------------------

(def error-formatters
  "Map of error type keywords to formatting functions.
   Each formatter takes ex-data map and returns human-readable message string."

  {;; -------------------------------------------------------------------------
   ;; Repository Errors
   ;; -------------------------------------------------------------------------

   :not-initialized
   (fn [_data]
     "Error: Not an Alethfeld repository.\n\nTo fix: Run 'af init' to initialize a new repository.")

   :already-initialized
   (fn [_data]
     "Error: Repository already initialized.\n\nThe .alethfeld/ directory already exists.")

   :not-git-repo
   (fn [_data]
     "Error: Not a git repository.\n\nTo fix: Run 'git init' first, then 'af init'.")

   ;; -------------------------------------------------------------------------
   ;; Mote Errors
   ;; -------------------------------------------------------------------------

   :not-found
   (fn [{:keys [mote-id]}]
     (str "Error: Mote not found: " mote-id "\n\n"
          "To fix: Run 'af check' to validate repository integrity,\n"
          "or use 'af show' on a known mote ID."))

   :validation-failed
   (fn [{:keys [errors field value]}]
     (str "Error: Validation failed\n"
          (if errors
            (str/join "\n" (map #(str "  - " %) errors))
            (when field
              (str "  - Invalid " (name field) ": " value)))))

   :invalid-status
   (fn [{:keys [status current-status valid-transitions]}]
     (str "Error: Invalid status transition.\n\n"
          "Current status: " (when current-status (name current-status)) "\n"
          "Requested status: " (when status (name status)) "\n"
          (when valid-transitions
            (str "Valid transitions: " (str/join ", " (map name valid-transitions))))))

   :integrity-error
   (fn [{:keys [mote-id session-mote-id]}]
     (str "Error: Data integrity violation.\n\n"
          "Session claims mote " session-mote-id " but mote " mote-id " not found.\n"
          "To fix: Run 'af check' to diagnose integrity issues."))

   ;; -------------------------------------------------------------------------
   ;; Claim Errors
   ;; -------------------------------------------------------------------------

   :already-claimed
   (fn [{:keys [mote-id claimed-by]}]
     (str "Error: Mote " mote-id " is already claimed by " claimed-by ".\n\n"
          "To fix: Use 'af unclaim " mote-id "' first, or choose a different mote.\n"
          "Run 'af ready' to find available work."))

   ;; -------------------------------------------------------------------------
   ;; Voting Errors
   ;; -------------------------------------------------------------------------

   :already-voted
   (fn [{:keys [agent mote-id]}]
     (str "Error: Agent '" agent "' has already voted"
          (when mote-id (str " on mote " mote-id))
          ".\n\n"
          "Each agent can only vote once per mote.\n"
          "A different agent must cast additional votes."))

   :self-vote
   (fn [{:keys [agent mote-id]}]
     (str "Error: Agent '" agent "' cannot vote on their own work.\n\n"
          "Mote " mote-id " was created or fixed by this agent.\n"
          "To fix: A different agent must verify this work to maintain integrity."))

   :unverified-dependencies
   (fn [{:keys [mote-id unverified-deps]}]
     (str "Error: Cannot verify mote " mote-id " - it has unverified dependencies.\n\n"
          "Unverified dependencies: " (str/join ", " unverified-deps) "\n"
          "To fix: Verify the dependencies first, then vote on this mote."))

   :quorum-not-reached
   (fn [{:keys [mote-id votes-needed votes-have]}]
     (str "Error: Quorum not reached for mote " mote-id ".\n\n"
          "Votes needed: " votes-needed "\n"
          "Votes received: " votes-have "\n"
          "To fix: Run 'af vote " mote-id " --for --session TOKEN' to add votes."))

   ;; -------------------------------------------------------------------------
   ;; Proposal Errors
   ;; -------------------------------------------------------------------------

   :no-proposal
   (fn [{:keys [parent-id]}]
     (str "Error: No active proposal"
          (when parent-id (str " on mote " parent-id))
          ".\n\n"
          "To fix: Use 'af propose <id> --claim \"...\"' to create a proposal first."))

   :proposal-exists
   (fn [{:keys [parent-id proposal-id]}]
     (str "Error: A proposal already exists"
          (when parent-id (str " on mote " parent-id))
          ".\n"
          (when proposal-id (str "Proposal ID: " proposal-id "\n"))
          "\nTo fix: Use 'af approve' or 'af reject' to resolve the current proposal first."))

   :atomicity-violation
   (fn [{:keys [parent-id children-statuses]}]
     (str "Error: Cannot create children for mote " parent-id ".\n\n"
          "Previous children exist with statuses:\n"
          (str/join "\n" (map (fn [[id status]] (str "  - " id ": " (name status)))
                               children-statuses))
          "\n\nTo fix: Archive or remove existing children before proposing new ones."))

   ;; -------------------------------------------------------------------------
   ;; Git Errors
   ;; -------------------------------------------------------------------------

   :git-error
   (fn [{:keys [stderr cmd]}]
     (str "Error: Git operation failed.\n"
          (when cmd (str "Command: " cmd "\n"))
          (when stderr (str "Details: " stderr))))

   :no-remote
   (fn [{:keys [remote]}]
     (str "Error: No remote configured.\n\n"
          "Remote '" (or remote "origin") "' is not configured.\n"
          "To fix: Run 'git remote add origin <url>' to configure a remote."))

   ;; -------------------------------------------------------------------------
   ;; Session Errors
   ;; -------------------------------------------------------------------------

   :invalid-session
   (fn [{:keys [session-id]}]
     (str "Error: Invalid or expired session.\n"
          (when session-id (str "Session ID: " session-id "\n"))
          "\nTo fix: Use 'af ready --name NAME' to claim a new job and get a session.\n"
          "\nTip: Use @current alias or export AF_SESSION=<token> to avoid typing long session IDs."))

   :session-expired
   (fn [{:keys [session-id expires-at]}]
     (str "Error: Session has expired.\n"
          (when session-id (str "Session ID: " session-id "\n"))
          (when expires-at (str "Expired at: " expires-at "\n"))
          "\nTo fix: Use 'af ready --name NAME' to claim a new job and get a session.\n"
          "\nTip: Use @current alias or export AF_SESSION=<token> to avoid typing long session IDs."))

   :session-mote-mismatch
   (fn [{:keys [session-mote-id requested-mote-id]}]
     (str "Error: Session is for a different mote.\n\n"
          "Session mote: " session-mote-id "\n"
          "Requested mote: " requested-mote-id "\n"
          "\nEach session is locked to a specific mote.\n"
          "To fix: Use 'af done --session TOKEN' to end current session,\n"
          "then claim the desired mote."))

   :action-not-allowed
   (fn [{:keys [role action allowed-actions agent proposer mote-id session-id]}]
     (if proposer
       ;; Withdrawal-specific error
       (str "Error: Only the proposer can withdraw a proposal.\n\n"
            "Your agent: " agent "\n"
            "Proposer: " proposer "\n"
            (when mote-id (str "Mote: " mote-id "\n"))
            "\nTo fix: Only the agent who created the proposal can withdraw it.")
       ;; Role-based error with helpful guidance (Section 2.3)
       (let [role-kw (when role (if (keyword? role) role (keyword role)))
             role-info (get role-allowed-actions role-kw)
             role-examples (:examples role-info)
             ;; Find which role CAN do this action
             required-role (first (for [[r info] role-allowed-actions
                                        :when (some #{action} (:actions info))]
                                    r))]
         (str "Cannot " (when action (name action)) ": your role is '" (when role (name role)) "'\n\n"
              (when required-role
                (str (str/capitalize (name action)) " requires role '" (name required-role) "'. "))
              "As a " (when role (name role)) ", you can:\n"
              (if role-examples
                (str/join "\n" (map #(str "  " %) role-examples))
                (when (seq allowed-actions)
                  (str "  Allowed actions: " (str/join ", " (map name allowed-actions)))))
              "\n\nTo get " (when required-role (str (name required-role) " ")) "work instead:\n"
              "  af done" (when session-id (str " --session " session-id)) "               -> End current session\n"
              "  af ready --agent <name>" (when required-role (str " --role " (name required-role))) " -> Get " (when required-role (str (name required-role) " ")) "work"))))

   :session-not-found
   (fn [{:keys [session-id]}]
     ;; Section 2.2: Session errors explain why + recovery steps
     (str "Session not found: " (if session-id
                                   (let [id-str (str session-id)]
                                     (if (> (count id-str) 12)
                                       (str (subs id-str 0 12) "...")
                                       id-str))
                                   "<unknown>") "\n\n"
          "This can happen if:\n"
          "  * The session expired (timeout: 30 minutes)\n"
          "  * The session was ended with 'af done'\n"
          "  * The session ID is incorrect\n\n"
          "To get a new session:\n"
          "  af ready --name <name>     -> Claim a job and get new session\n\n"
          "To check your active sessions:\n"
          "  af sessions                -> Lists active sessions\n\n"
          "Tip: Use @current alias or export AF_SESSION=<token> to avoid typing long session IDs."))

   ;; -------------------------------------------------------------------------
   ;; File/Parse Errors
   ;; -------------------------------------------------------------------------

   :parse-error
   (fn [{:keys [path cause]}]
     (str "Error: Failed to parse file.\n"
          (when path (str "File: " path "\n"))
          (when cause (str "Details: " cause "\n"))
          "\nThe file may be corrupted or contain invalid EDN.\n"
          "To fix: Check the file contents or restore from git history."))

   :invalid-config
   (fn [{:keys [path errors]}]
     (str "Error: Invalid configuration file.\n"
          (when path (str "File: " path "\n"))
          "\nValidation errors:\n"
          (if errors
            (str/join "\n" (map #(str "  - " %) errors))
            "  - Unknown validation error")
          "\n\nExpected config format:\n"
          "  {:project-name \"My Project\"      ; required string\n"
          "   :version \"0.1\"                  ; required string\n"
          "   :default-difficulty 3            ; required integer 1-5\n"
          "   :proposal-quorum 1               ; optional integer >= 1\n"
          "   :vote-quorum 1                   ; optional integer >= 1\n"
          "   :claim-timeout-minutes 30        ; optional integer >= 1\n"
          "   :session-timeout-minutes 60}     ; optional integer >= 1\n"
          "\nTo fix: Edit .alethfeld/config.edn to match the expected format."))

   ;; -------------------------------------------------------------------------
   ;; Role Errors
   ;; -------------------------------------------------------------------------

   :role-forbidden
   (fn [{:keys [role action allowed-roles]}]
     (str "Error: Role '" (when role (name role)) "' cannot perform '" (when action (name action)) "'.\n\n"
          (when (seq allowed-roles)
            (str "This action requires: " (str/join ", " (map name allowed-roles))))))

   ;; -------------------------------------------------------------------------
   ;; Invalid Role Error (2.1)
   ;; -------------------------------------------------------------------------

   :invalid-role
   (fn [{:keys [role]}]
     (let [role-name (if (keyword? role) (name role) (str role))
           suggestion (when role (suggest-role (if (keyword? role) role (keyword role))))]
       (str "Invalid role: \"" role-name "\"\n\n"
            "Valid roles:\n"
            (format-valid-roles)
            (when suggestion
              (str "\n\nDid you mean: " (name suggestion) "?"))
            "\n\nGet available work:\n"
            "  af ready --agent <name>    -> Shows what roles are needed")))})

;; -----------------------------------------------------------------------------
;; Error Formatting Functions
;; -----------------------------------------------------------------------------

(defn format-error
  "Format an exception into a human-readable error message.

   Arguments:
   - ex: Exception (should be ExceptionInfo with ex-data containing :type)

   Returns a string with the formatted error message and hints."
  [ex]
  (let [data (ex-data ex)
        error-type (:type data)
        formatter (get error-formatters error-type)]
    (if formatter
      (formatter data)
      ;; Default fallback for unrecognized error types
      (str "Error: " (ex-message ex)
           (when (seq (dissoc data :type))
             (str "\nDetails: " (pr-str (dissoc data :type))))))))

(defn error-type->exit-code
  "Map error type to appropriate exit code keyword.

   Arguments:
   - error-type: Keyword error type from ex-data

   Returns exit code keyword compatible with alethfeld.cli/exit-codes."
  [error-type]
  (case error-type
    ;; Not found errors (resource doesn't exist)
    (:not-found :session-not-found :no-proposal) :not-found

    ;; Validation errors (invalid input or state)
    (:validation-failed :invalid-status :invalid-role :invalid-config) :validation-error

    ;; Conflict errors (resource already exists/in-use or conflicting state)
    (:already-voted :already-claimed :proposal-exists :already-initialized :atomicity-violation) :conflict

    ;; Forbidden errors (authentication, authorization, policy violations)
    (:invalid-session :session-expired :session-mote-mismatch :action-not-allowed :self-vote :role-forbidden) :forbidden

    ;; Generic errors (environment, configuration, external failures, data corruption)
    (:not-initialized :not-git-repo :integrity-error :unverified-dependencies :quorum-not-reached
     :git-error :no-remote :parse-error) :error

    ;; Default fallback
    :error))

(defn throw-error
  "Throw a structured error with the given type and data.

   Arguments:
   - error-type: Keyword identifying the error type
   - message: Human-readable message (for logs/debugging)
   - data: Additional context data (will be merged with :type)

   Example:
   (throw-error :not-found \"Mote not found\" {:mote-id \"1.2.3\"})"
  [error-type message data]
  (throw (ex-info message (assoc data :type error-type))))
