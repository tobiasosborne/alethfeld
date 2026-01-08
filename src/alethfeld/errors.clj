(ns alethfeld.errors
  "Human-readable error message formatting.

   This module provides:
   - Structured error type definitions
   - User-friendly error messages with actionable hints
   - Error formatting for both EDN and plain text output"
  (:require [clojure.string :as str]))

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
          "\nTo fix: Use 'af claim <id> --agent NAME --role ROLE' to start a new session."))

   :session-expired
   (fn [{:keys [session-id expires-at]}]
     (str "Error: Session has expired.\n"
          (when session-id (str "Session ID: " session-id "\n"))
          (when expires-at (str "Expired at: " expires-at "\n"))
          "\nTo fix: Use 'af claim <id> --agent NAME --role ROLE' to start a new session."))

   :session-mote-mismatch
   (fn [{:keys [session-mote-id requested-mote-id]}]
     (str "Error: Session is for a different mote.\n\n"
          "Session mote: " session-mote-id "\n"
          "Requested mote: " requested-mote-id "\n"
          "\nEach session is locked to a specific mote.\n"
          "To fix: Use 'af done --session TOKEN' to end current session,\n"
          "then claim the desired mote."))

   :action-not-allowed
   (fn [{:keys [role action allowed-actions]}]
     (str "Error: Action not allowed for your role.\n\n"
          "Your role: " (when role (name role)) "\n"
          "Attempted action: " (when action (name action)) "\n"
          (when (seq allowed-actions)
            (str "Allowed actions: " (str/join ", " (map name allowed-actions))))))

   :session-not-found
   (fn [{:keys [session-id]}]
     (str "Error: Session not found or already ended.\n"
          (when session-id (str "Session ID: " session-id "\n"))
          "\nThe session may have expired or been ended with 'af done'."))

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

   ;; -------------------------------------------------------------------------
   ;; Role Errors
   ;; -------------------------------------------------------------------------

   :role-forbidden
   (fn [{:keys [role action allowed-roles]}]
     (str "Error: Role '" (when role (name role)) "' cannot perform '" (when action (name action)) "'.\n\n"
          (when (seq allowed-roles)
            (str "This action requires: " (str/join ", " (map name allowed-roles))))))})

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
    ;; Not found errors
    (:not-found :session-not-found) :not-found

    ;; Validation errors
    :validation-failed :validation-error

    ;; Conflict errors (resource already exists/in-use)
    (:already-voted :already-claimed :proposal-exists) :conflict

    ;; Default to generic error
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
