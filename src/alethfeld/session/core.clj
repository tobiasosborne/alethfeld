(ns alethfeld.session.core
  "Core session CRUD operations and lifecycle management."
  (:require [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.schema :as schema]
            [malli.core :as m])
  (:import [java.time Instant Duration]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const default-session-duration-minutes 30)

(def ^:const session-id-display-length
  "Number of characters to display when truncating session IDs for output.
   Session IDs are 73 characters (dual UUIDs); showing 11 chars is enough
   for human identification while keeping output clean."
  11)

;; -----------------------------------------------------------------------------
;; Session ID Generation
;; -----------------------------------------------------------------------------

(defn generate-session-id
  "Generate a cryptographically random session ID.

   Uses dual UUIDs (256 bits of entropy) for security.
   Format: uuid1-uuid2 (73 characters total)"
  []
  (str (java.util.UUID/randomUUID) "-" (java.util.UUID/randomUUID)))

(defn valid-session-id?
  "Check if a string is a valid session ID."
  [s]
  (m/validate schema/SessionId s))

;; -----------------------------------------------------------------------------
;; Path Helpers
;; -----------------------------------------------------------------------------

(defn- active-session-path
  "Get full path to an active session file."
  [repo-path session-id]
  (io/full-path repo-path (path/session-path session-id :active)))

(defn- completed-session-path
  "Get full path to a completed session file."
  [repo-path session-id]
  (io/full-path repo-path (path/session-path session-id :completed)))

;; -----------------------------------------------------------------------------
;; Session Creation
;; -----------------------------------------------------------------------------

(defn create-session
  "Create a new session map (does not persist).

   Arguments:
   - mote-id: The mote this session is for
   - role: The role for this session (:proposer, :advisor, etc.)
   - agent: Agent identifier string

   Options:
   - :duration-minutes - Session duration (default: 30)
   - :pid - Process ID for crash detection

   Returns a session map ready to be saved."
  [mote-id role agent & {:keys [duration-minutes pid]
                         :or {duration-minutes default-session-duration-minutes}}]
  (let [now (Instant/now)
        expires (.plus now (Duration/ofMinutes duration-minutes))]
    (cond-> {:session-id (generate-session-id)
             :mote-id mote-id
             :role role
             :agent agent
             :started-at (java.util.Date/from now)
             :expires-at (java.util.Date/from expires)
             :actions []}
      pid (assoc :pid pid))))

(defn create-session!
  "Create and persist a new session.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote this session is for
   - role: The role for this session
   - agent: Agent identifier string

   Options:
   - :duration-minutes - Session duration (default: 30)
   - :pid - Process ID for crash detection

   Returns the created session, or nil if validation fails."
  [repo-path mote-id role agent & {:keys [duration-minutes pid] :as opts}]
  (let [session (apply create-session mote-id role agent (mapcat identity opts))]
    (when (m/validate schema/Session session)
      (io/write-edn (active-session-path repo-path (:session-id session)) session)
      session)))

;; -----------------------------------------------------------------------------
;; Session Loading
;; -----------------------------------------------------------------------------

(defn load-session
  "Load a session by ID.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to load

   Searches active sessions first, then completed.
   Returns nil if not found or invalid."
  [repo-path session-id]
  (let [active-path (active-session-path repo-path session-id)
        completed-path (completed-session-path repo-path session-id)]
    (or (when-let [session (io/read-edn active-path)]
          (when (m/validate schema/Session session)
            session))
        (when-let [session (io/read-edn completed-path)]
          (when (m/validate schema/Session session)
            session)))))

(defn load-active-session
  "Load an active session by ID.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to load

   Only searches active sessions directory.
   Returns nil if not found, invalid, or completed."
  [repo-path session-id]
  (when-let [session (io/read-edn (active-session-path repo-path session-id))]
    (when (m/validate schema/Session session)
      session)))

(defn load-all-active-sessions
  "Load all active sessions.

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of session maps."
  [repo-path]
  (let [active-dir (io/full-path repo-path (path/active-sessions-path))
        files (io/list-edn-files active-dir)]
    (->> files
         (keep io/read-edn)
         (filter #(m/validate schema/Session %))
         vec)))

(defn load-sessions-for-mote
  "Load all active sessions for a specific mote.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to filter by

   Returns a vector of session maps."
  [repo-path mote-id]
  (->> (load-all-active-sessions repo-path)
       (filter #(= (:mote-id %) mote-id))
       vec))

(defn load-sessions-for-agent
  "Load all active sessions for a specific agent.

   Arguments:
   - repo-path: Path to the repository root
   - agent: The agent identifier to filter by

   Returns a vector of session maps."
  [repo-path agent]
  (->> (load-all-active-sessions repo-path)
       (filter #(= (:agent %) agent))
       vec))

;; -----------------------------------------------------------------------------
;; Session Status
;; -----------------------------------------------------------------------------

(declare session-expired?)

(defn session-active?
  "Check if a session exists and is active (not expired).

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to check

   Options:
   - :now - Optional java.time.Instant for the current time (defaults to Instant/now).
            Useful for testing and ensuring consistent time comparisons.

   Returns true if session exists in active directory and not expired.

   Note: This function is primarily used in tests. Production code should use
   load-active-session + session-expired? for explicit control over timestamp."
  [repo-path session-id & {:keys [now]}]
  (when-let [session (load-active-session repo-path session-id)]
    (not (session-expired? session :now now))))

(defn session-expired?
  "Check if an active session has expired.

   Arguments:
   - session: Session map

   Options:
   - :now - Optional java.time.Instant for the current time (defaults to Instant/now).
            Useful for testing and ensuring consistent time comparisons across
            multiple checks (avoiding TOCTOU vulnerabilities).

   Returns true if current time is past expires-at."
  [session & {:keys [now]}]
  (let [current-instant (or now (Instant/now))
        expires-at (:expires-at session)
        expires-instant (Instant/ofEpochMilli (.getTime expires-at))]
    (.isAfter current-instant expires-instant)))

;; -----------------------------------------------------------------------------
;; Session Updates
;; -----------------------------------------------------------------------------

(defn record-action!
  "Record an action in a session's audit trail.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID
   - action: Keyword representing the action (e.g., :propose, :vote)

   Returns the updated session, or nil if session not found/invalid."
  [repo-path session-id action]
  (when-let [session (load-active-session repo-path session-id)]
    (let [updated (update session :actions conj action)]
      (io/write-edn (active-session-path repo-path session-id) updated)
      updated)))

;; -----------------------------------------------------------------------------
;; Session Lifecycle
;; -----------------------------------------------------------------------------

(defn end-session!
  "End an active session (move to completed).

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to end

   Options:
   - :record-stats - If true, record completed-at and action-count

   Returns the session that was ended, or nil if not found."
  [repo-path session-id & {:keys [record-stats] :or {record-stats false}}]
  (when-let [session (load-active-session repo-path session-id)]
    (let [active-path (active-session-path repo-path session-id)
          completed-path (completed-session-path repo-path session-id)
          final-session (if record-stats
                          (assoc session
                                 :completed-at (java.util.Date.)
                                 :action-count (count (:actions session)))
                          session)]
      ;; Write updated session with stats, then move
      (when record-stats
        (io/write-edn active-path final-session))
      (io/move-file active-path completed-path)
      final-session)))

(defn archive-session!
  "Archive an expired or crashed session.

   Same as end-session! but indicates forced cleanup.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to archive

   Returns the session that was archived, or nil if not found."
  [repo-path session-id]
  (end-session! repo-path session-id))

(defn delete-session!
  "Delete a session (active or completed).

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to delete

   Returns true if deleted, false if not found."
  [repo-path session-id]
  (let [active-path (active-session-path repo-path session-id)
        completed-path (completed-session-path repo-path session-id)]
    (or (io/delete-file active-path)
        (io/delete-file completed-path))))

;; -----------------------------------------------------------------------------
;; Directory Initialization
;; -----------------------------------------------------------------------------

(defn ensure-session-dirs!
  "Ensure session directories exist.

   Arguments:
   - repo-path: Path to the repository root

   Creates .alethfeld/sessions/active/ and .alethfeld/sessions/completed/."
  [repo-path]
  (io/ensure-dir (io/full-path repo-path (path/active-sessions-path)))
  (io/ensure-dir (io/full-path repo-path (path/completed-sessions-path))))

;; -----------------------------------------------------------------------------
;; Validation
;; -----------------------------------------------------------------------------

(defn validate-session
  "Validate a session against the schema.

   Returns nil if valid, or explanation if invalid."
  [session]
  (m/explain schema/Session session))
