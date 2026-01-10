(ns alethfeld.session.resolution
  "Session alias resolution (@current, @last) and auto-selection."
  (:require [alethfeld.session.core :as core])
  (:import [java.time Instant]))

;; -----------------------------------------------------------------------------
;; Session Alias Resolution (@current, @last)
;; -----------------------------------------------------------------------------

(defn resolve-session-alias
  "Resolve @current or @last session alias to an actual session ID.

   Supports the following aliases:
   - \"@current\" - The most recent active session for the agent
   - \"@last\" - Same as @current (alias for familiarity)

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID or alias string
   - agent: Agent identifier string

   Returns a map with:
   - :session-id - The resolved session ID (actual ID, not alias)
   - :resolved-from - The original alias if resolved (\"@current\" or \"@last\"), or nil

   Or returns an error map with:
   - :error - Error type (:no-active-session, :multiple-sessions, :no-agent-specified)
   - :message - Human-readable error message
   - :sessions - (for :multiple-sessions) List of available sessions

   Examples:
   - Alias with single session:
     {:session-id \"abc-123...\" :resolved-from \"@current\"}

   - Non-alias (regular session ID):
     {:session-id \"abc-123...\" :resolved-from nil}

   - No active sessions:
     {:error :no-active-session :message \"...\"}

   - Multiple active sessions (ambiguous):
     {:error :multiple-sessions :message \"...\" :sessions [...]}"
  [repo-path session-id agent]
  (let [is-alias? (contains? #{"@current" "@last"} session-id)]
    (cond
      ;; Not an alias - return as-is
      (not is-alias?)
      {:session-id session-id
       :resolved-from nil}

      ;; Alias but no agent specified - error
      (nil? agent)
      {:error :no-agent-specified
       :message (str "Cannot resolve " session-id " without --agent. "
                     "Specify --agent or use an explicit session ID.")}

      ;; Alias with agent - look up sessions
      :else
      (let [now (Instant/now)
            sessions (->> (core/load-sessions-for-agent repo-path agent)
                          (remove #(core/session-expired? % :now now))
                          ;; Sort by started-at descending (most recent first)
                          (sort-by #(.getTime (:started-at %)) >))]
        (case (count sessions)
          ;; 0 sessions - error
          0 {:error :no-active-session
             :message (str "No active sessions for agent '" agent "'. "
                           "Get a task with: af ready --agent " agent)}

          ;; 1 session - resolve successfully
          1 {:session-id (:session-id (first sessions))
             :resolved-from session-id}

          ;; 2+ sessions - ambiguous, require explicit choice
          {:error :multiple-sessions
           :message (str "Cannot resolve " session-id ": multiple active sessions for '"
                         agent "'. Please specify an explicit session ID:")
           :sessions (mapv (fn [s]
                             {:session-id (:session-id s)
                              :role (:role s)
                              :mote-id (:mote-id s)
                              :started-at (:started-at s)})
                           sessions)})))))

;; -----------------------------------------------------------------------------
;; Session Resolution (Auto-Use Single Session)
;; -----------------------------------------------------------------------------

(defn resolve-session
  "Resolve which session to use, with auto-selection for single-session agents.

   This implements Section 5.1 of the Agent UX Plan: if an agent has exactly
   one active session and no explicit session was provided, use it automatically.

   Arguments:
   - repo-path: Path to the repository root
   - opts: Map containing:
     - :session-id - Explicitly provided session ID (optional)
     - :agent - Agent identifier (required if session-id not provided)

   Returns a map with:
   - :session-id - The resolved session ID
   - :auto-resolved? - true if session was auto-selected (no explicit --session)
   - :message - Human-readable message explaining the resolution

   Or returns an error map with:
   - :error - Error type (:no-active-session, :multiple-sessions, :invalid-session)
   - :message - Human-readable error message
   - :sessions - (for :multiple-sessions) List of available sessions

   Examples:
   - Explicit session provided:
     {:session-id \"abc-123\" :auto-resolved? false :message nil}

   - Auto-resolved (agent has 1 session):
     {:session-id \"abc-123\" :auto-resolved? true
      :message \"Using session: abc-123 (your only active session)\"}

   - No session (agent has 0 sessions):
     {:error :no-active-session
      :message \"No active session. Get a task with: af ready --agent <name>\"}

   - Multiple sessions (agent has 2+ sessions):
     {:error :multiple-sessions
      :message \"Multiple active sessions found. Please specify --session:\"
      :sessions [{:session-id \"abc-123\" :role :verifier :mote-id \"1.2\"} ...]}"
  [repo-path {:keys [session-id agent]}]
  (cond
    ;; Case 1: Explicit session provided - use it
    session-id
    {:session-id session-id
     :auto-resolved? false
     :message nil}

    ;; Case 2: No session and no agent - error
    (nil? agent)
    {:error :no-agent-specified
     :message "No session or agent specified. Provide --session or --agent."}

    ;; Case 3: Look up sessions for agent
    :else
    (let [now (Instant/now)
          sessions (->> (core/load-sessions-for-agent repo-path agent)
                        (remove #(core/session-expired? % :now now)))]
      (case (count sessions)
        ;; 0 sessions - error
        0 {:error :no-active-session
           :message (str "No active session for agent '" agent "'. "
                         "Get a task with: af ready --agent " agent)}

        ;; 1 session - auto-resolve
        1 (let [session (first sessions)
                session-id (:session-id session)]
            {:session-id session-id
             :auto-resolved? true
             :message (str "Using session: " (subs session-id 0 (min core/session-id-display-length (count session-id)))
                           "... (your only active session)")})

        ;; 2+ sessions - require explicit choice
        {:error :multiple-sessions
         :message "Multiple active sessions found. Please specify --session:"
         :sessions (mapv (fn [s]
                           {:session-id (:session-id s)
                            :role (:role s)
                            :mote-id (:mote-id s)})
                         sessions)}))))
