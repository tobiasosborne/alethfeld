(ns alethfeld.middleware
  "Middleware for session enforcement and command wrapping.

   Provides pull-based session enforcement that wraps handlers BEFORE dispatch,
   ensuring security checks happen centrally rather than in each handler.

   Key benefits:
   - Impossible to add handler that bypasses permissions
   - Single place to audit all permission checks
   - Handlers focus on business logic, not security"
  (:require [alethfeld.session :as session]))

;; -----------------------------------------------------------------------------
;; Session Enforcement Middleware
;; -----------------------------------------------------------------------------

(defn wrap-session-enforcement
  "Middleware that enforces session validity before calling a handler.

   This implements 'pull-based' enforcement: the middleware validates the session
   BEFORE the handler runs, rather than relying on each handler to call
   enforce-session! (push-based).

   Arguments:
   - handler: The handler function to wrap
   - action: The action keyword (e.g., :propose, :vote)

   Options:
   - :validate-only - If true, use validate-session! instead of enforce-session!
                      (no role permission check, just session validity)
   - :repo-path - Repository path (defaults to \".\")

   The wrapped handler receives the original context with an additional key:
   - :validated-session - The session map (if enforcement passed)

   Usage:
   ```clojure
   (def wrapped-propose
     (wrap-session-enforcement cmd-propose! :propose))
   ```

   Or with validate-only mode:
   ```clojure
   (def wrapped-unclaim
     (wrap-session-enforcement cmd-unclaim! :done :validate-only true))
   ```"
  [handler action & {:keys [validate-only repo-path]
                     :or {validate-only false}}]
  (fn [context]
    (let [{:keys [id options]} context
          session-id (:session options)
          ;; Use repo-path from context if not provided as option
          effective-repo-path (or repo-path (:repo-path context) ".")]
      ;; Check if we have required session info
      (cond
        ;; No session provided - let handler deal with it (may have its own error)
        (nil? session-id)
        (handler context)

        ;; No mote ID for commands that need one
        (nil? id)
        (handler context)

        ;; Enforce or validate session
        :else
        (let [session (if validate-only
                        (session/validate-session! effective-repo-path session-id id)
                        (session/enforce-session! effective-repo-path session-id action id))]
          ;; Pass validated session to handler
          (handler (assoc context :validated-session session)))))))

(defn enforce-for-command
  "Enforce session for a command, given command metadata.

   This is a higher-level function that uses cli/command-actions metadata
   to determine how to enforce the session.

   Arguments:
   - repo-path: Repository path
   - command: Command name string
   - id: Mote ID (may be nil for some commands)
   - options: Parsed options map

   Uses:
   - cli/get-command-action to resolve the action
   - cli/command-validate-only? to determine enforcement mode

   Returns the validated session, or throws on failure.

   Note: This is used for commands where middleware wrapping isn't practical
   (e.g., batch commands that iterate over multiple motes)."
  [repo-path command id options]
  ;; Import dynamically to avoid circular dependency
  (require 'alethfeld.cli)
  (let [get-action (resolve 'alethfeld.cli/get-command-action)
        validate-only? (resolve 'alethfeld.cli/command-validate-only?)
        action (get-action command options)]
    (when action
      (if (validate-only? command)
        (session/validate-session! repo-path (:session options) id)
        (session/enforce-session! repo-path (:session options) action id)))))

;; -----------------------------------------------------------------------------
;; Middleware Composition
;; -----------------------------------------------------------------------------

(defn wrap-all
  "Apply multiple middleware wrappers to a handler.

   Arguments:
   - handler: The base handler function
   - wrappers: Sequence of wrapper functions, applied inside-out

   Example:
   ```clojure
   (wrap-all my-handler
     [(partial wrap-session-enforcement :propose)
      wrap-logging
      wrap-timing])
   ```

   Returns a function that applies all wrappers."
  [handler wrappers]
  (reduce (fn [h wrapper] (wrapper h)) handler wrappers))
