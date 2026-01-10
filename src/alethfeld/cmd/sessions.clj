(ns alethfeld.cmd.sessions
  "Sessions command: list all active sessions with status."
  (:require [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.cmd.core :as core]
            [clojure.string :as str])
  (:import [java.time Instant Duration]))

;; -----------------------------------------------------------------------------
;; Time Formatting Helpers
;; -----------------------------------------------------------------------------

(defn- format-relative-time
  "Format a date as relative time (e.g., '5 min ago', '2 hours ago').

   Arguments:
   - date: A java.util.Date object
   - now: An Instant representing current time

   Returns a human-readable relative time string."
  [date now]
  (let [then (.toInstant date)
        duration (Duration/between then now)
        minutes (.toMinutes duration)
        hours (.toHours duration)]
    (cond
      (< minutes 1) "just now"
      (< minutes 60) (str minutes " min ago")
      (< hours 24) (str hours " hour" (when (> hours 1) "s") " ago")
      :else (let [days (.toDays duration)]
              (str days " day" (when (> days 1) "s") " ago")))))

(defn- truncate-session-id
  "Truncate a session ID to first 11 characters with ellipsis."
  [session-id]
  (if (> (count session-id) 11)
    (str (subs session-id 0 11) "...")
    session-id))

;; -----------------------------------------------------------------------------
;; Session Categorization
;; -----------------------------------------------------------------------------

(defn- categorize-sessions
  "Categorize sessions into active and stale.

   Arguments:
   - sessions: Vector of session maps
   - now: Current Instant for consistent time checks

   Returns a map with :active and :stale vectors."
  [sessions now]
  (reduce
   (fn [acc session]
     (if (session/session-stale? session :now now)
       (update acc :stale conj session)
       (update acc :active conj session)))
   {:active [] :stale []}
   sessions))

;; -----------------------------------------------------------------------------
;; Formatting Helpers
;; -----------------------------------------------------------------------------

(defn- format-session-line
  "Format a single session for display.

   Arguments:
   - session: Session map
   - now: Current Instant for relative time calculation
   - suffix: Optional suffix string (e.g., '(expired)')

   Returns a formatted string like:
   'abc-123... | claude-1 | advisor | mote 1.1 | 5 min ago'"
  [session now & [suffix]]
  (let [session-id (truncate-session-id (:session-id session))
        agent (:agent session)
        role (name (:role session))
        mote-id (:mote-id session)
        started-at (:started-at session)
        time-str (format-relative-time started-at now)]
    (str "  " session-id " | " agent " | " role " | mote " mote-id " | " time-str
         (when suffix (str " " suffix)))))

(defn- format-active-sessions
  "Format the active sessions section.

   Arguments:
   - sessions: Vector of active session maps
   - now: Current Instant

   Returns a formatted string."
  [sessions now]
  (if (empty? sessions)
    "Active sessions: (none)"
    (str "Active sessions:\n"
         (str/join "\n" (map #(format-session-line % now) sessions)))))

(defn- format-stale-sessions
  "Format the stale sessions section.

   Arguments:
   - sessions: Vector of stale session maps
   - now: Current Instant

   Returns a formatted string, or nil if no stale sessions."
  [sessions now]
  (when (seq sessions)
    (str "\nStale sessions (may need cleanup):\n"
         (str/join "\n"
                   (map (fn [s]
                          (let [expired? (session/session-expired? s :now now)]
                            (format-session-line s now (if expired? "(expired)" "(crashed?)"))))
                        sessions)))))

;; -----------------------------------------------------------------------------
;; Sessions Command
;; -----------------------------------------------------------------------------

(defn cmd-sessions
  "List all active sessions with their status.

   Shows:
   - Active sessions: valid, not expired
   - Stale sessions: expired or owning process died

   Options:
   - :details - Show additional session details (actions count, expires-at)

   Returns a map with:
   - :active-sessions - Vector of active session maps
   - :stale-sessions - Vector of stale session maps
   - :output - Formatted human-readable output
   - :next-actions - Suggested next commands"
  [{:keys [options]}]
  (let [repo-path "."
        verbose? (:details options)]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Use a single timestamp for all checks (avoid TOCTOU)
    (let [now (Instant/now)

          ;; Load all active sessions
          all-sessions (session/load-all-active-sessions repo-path)

          ;; Categorize into active vs stale
          {:keys [active stale]} (categorize-sessions all-sessions now)

          ;; Format output
          active-output (format-active-sessions active now)
          stale-output (format-stale-sessions stale now)

          output (str active-output
                      (when stale-output stale-output)
                      (when (and (empty? active) (empty? stale))
                        "\n\nNo active sessions. Agents can claim work with:\n  af ready --agent <name>"))

          ;; Build next-actions based on state
          base-actions [(core/make-action "af done --session <id>" "End a session")
                        (core/ready-action)
                        (core/status-action)]

          next-actions (if (seq stale)
                         ;; If stale sessions exist, suggest cleanup
                         (into [(core/make-action "af ready" "Clean up stale sessions (automatic)")]
                               base-actions)
                         base-actions)]

      {:active-sessions (vec active)
       :stale-sessions (vec stale)
       :total-count (count all-sessions)
       :active-count (count active)
       :stale-count (count stale)
       :output output
       :verbose? verbose?
       :next-actions next-actions})))
