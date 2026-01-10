(ns alethfeld.session.cleanup
  "Stale session detection and cleanup operations."
  (:require [alethfeld.session.core :as core]
            [babashka.process :as proc])
  (:import [java.time Instant]))

;; -----------------------------------------------------------------------------
;; Platform Detection
;; -----------------------------------------------------------------------------

(def ^:private windows?
  "True if running on Windows platform."
  (.startsWith (System/getProperty "os.name") "Windows"))

;; -----------------------------------------------------------------------------
;; Process Detection
;; -----------------------------------------------------------------------------

(defn- pid-alive-unix?
  "Check if a process is still running on Unix/Linux/macOS.

   Uses `kill -0` to check process existence without sending a signal.
   Returns:
   - true if process is alive
   - false if process is dead
   - :unknown if check failed (e.g., permission denied)"
  [pid]
  (try
    (let [result (proc/sh ["kill" "-0" (str pid)])]
      (zero? (:exit result)))
    (catch Exception _
      :unknown)))

(defn- pid-alive-windows?
  "Check if a process is still running on Windows.

   Uses `tasklist /FI \"PID eq <pid>\" /NH` to check process existence.
   Returns:
   - true if process is alive
   - false if process is dead
   - :unknown if check failed"
  [pid]
  (try
    (let [result (proc/sh ["tasklist" "/FI" (str "PID eq " pid) "/NH"])]
      (if (zero? (:exit result))
        ;; tasklist returns success but output contains "INFO: No tasks" if PID not found
        (not (re-find #"(?i)no tasks" (:out result)))
        :unknown))
    (catch Exception _
      :unknown)))

(defn pid-alive?
  "Check if a process is still running. Cross-platform.

   Arguments:
   - pid: Process ID (integer or string), or nil

   Returns a tri-state result:
   - true: Process is definitely alive
   - false: Process is definitely dead
   - :unknown: Unable to determine (e.g., permission denied, command failed)
   - nil: If pid argument was nil

   Platform behavior:
   - Unix/Linux/macOS: Uses `kill -0 <pid>` (doesn't send signal, just checks)
   - Windows: Uses `tasklist /FI \"PID eq <pid>\" /NH`

   The :unknown case happens when:
   - The check command itself fails to execute
   - Permission is denied to query the process
   - Platform-specific tools are unavailable

   Callers should handle :unknown conservatively - typically treating it
   as 'not confirmed dead' to avoid incorrectly cleaning up sessions."
  [pid]
  (when pid
    (if windows?
      (pid-alive-windows? pid)
      (pid-alive-unix? pid))))

;; -----------------------------------------------------------------------------
;; Stale Session Detection
;; -----------------------------------------------------------------------------

(defn session-stale?
  "Check if a session is stale (expired OR owning process died).

   A session is stale if:
   1. It has expired (past expires-at time), OR
   2. It has a PID recorded and that process is DEFINITELY dead (false from pid-alive?)

   Arguments:
   - session: Session map

   Options:
   - :now - Optional java.time.Instant for the current time (defaults to Instant/now).
            Useful for testing and ensuring consistent time comparisons.

   Returns true if session should be cleaned up.

   Note: If pid-alive? returns :unknown, we conservatively treat the session
   as NOT stale to avoid incorrectly cleaning up sessions when we can't
   determine process status (e.g., on platforms where the check fails)."
  [session & {:keys [now]}]
  (or (core/session-expired? session :now now)
      (when-let [pid (:pid session)]
        (false? (pid-alive? pid)))))

;; -----------------------------------------------------------------------------
;; Cleanup Operations
;; -----------------------------------------------------------------------------

(defn cleanup-expired-sessions!
  "Archive all expired active sessions.

   Arguments:
   - repo-path: Path to the repository root

   Returns vector of session IDs that were archived.

   Note: Uses a single timestamp for all expiration checks to avoid TOCTOU issues."
  [repo-path]
  (let [now (Instant/now)
        active-sessions (core/load-all-active-sessions repo-path)]
    (->> active-sessions
         (filter #(core/session-expired? % :now now))
         (mapv (fn [session]
                 (core/archive-session! repo-path (:session-id session))
                 (:session-id session))))))

(defn cleanup-stale-sessions!
  "Archive all stale sessions (expired OR crashed agent).

   A session is stale if:
   1. It has expired (past expires-at time), OR
   2. It has a PID recorded and that process is DEFINITELY dead (false from pid-alive?)

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of maps for each cleaned-up session:
   - :session-id - The session that was archived
   - :mote-id - The mote that needs its claim cleared
   - :reason - :expired or :crashed

   Note: The caller is responsible for clearing mote claims.
   This separation avoids circular dependencies between session and store.

   Note: If pid-alive? returns :unknown, we conservatively treat the session
   as NOT crashed to avoid incorrectly cleaning up sessions when we can't
   determine process status.

   Note: Uses a single timestamp for all expiration checks to avoid TOCTOU issues."
  [repo-path]
  (let [now (Instant/now)
        active-sessions (core/load-all-active-sessions repo-path)]
    (->> active-sessions
         (keep (fn [session]
                 (let [expired? (core/session-expired? session :now now)
                       crashed? (when-let [pid (:pid session)]
                                  (false? (pid-alive? pid)))]
                   (when (or expired? crashed?)
                     (core/archive-session! repo-path (:session-id session))
                     {:session-id (:session-id session)
                      :mote-id (:mote-id session)
                      :reason (if expired? :expired :crashed)}))))
         vec)))
