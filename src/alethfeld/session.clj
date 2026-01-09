(ns alethfeld.session
  "Session management for role-based mote operations.

   Sessions provide:
   - Role enforcement (only allowed actions per role)
   - Claim tracking (one session per mote)
   - Audit trail (actions recorded)
   - Expiration (default 30 minutes)

   Directory structure:
   - .alethfeld/sessions/active/<session-id>.edn
   - .alethfeld/sessions/completed/<session-id>.edn"
  (:require [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.schema :as schema]
            [babashka.process :as proc]
            [malli.core :as m])
  (:import [java.time Instant Duration]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const default-session-duration-minutes 30)

;; -----------------------------------------------------------------------------
;; Platform Detection
;; -----------------------------------------------------------------------------

(def ^:private windows?
  "True if running on Windows platform."
  (.startsWith (System/getProperty "os.name") "Windows"))

;; -----------------------------------------------------------------------------
;; Role-Action Matrix
;; -----------------------------------------------------------------------------

(def role-actions
  "Defines which actions each role is permitted to perform.

   Each role has a specific set of capabilities:
   - :proposer - Creates proposals and adds definitions/assumptions/refs
   - :advisor - Reviews proposals (approve/reject)
   - :prover - Similar to proposer but can also remove taints
   - :verifier - Votes on motes and can add taints
   - :ref-checker - Manages references and can remove taints
   - :counterexample - Votes and can update status (refutation)"
  {:proposer      #{:propose :add-definition :add-assumption :add-ref :done}
   :advisor       #{:approve :reject :done}
   :prover        #{:propose :add-definition :add-assumption :add-ref
                    :taint-remove :done}
   :verifier      #{:vote :taint-add :done}
   :ref-checker   #{:add-ref :taint-remove :done}
   :counterexample #{:vote :update-status :done}})

(def sessionless-commands
  "Commands that don't require an active session.

   These are read-only or administrative operations that any agent
   can perform without claiming a mote."
  #{:init :ready :show :tree :status :check :log :help :config})

(defn allowed?
  "Check if a role is permitted to perform an action.

   Arguments:
   - role: The session role (keyword)
   - action: The action to check (keyword)

   Returns true if the role can perform the action, false otherwise."
  [role action]
  (contains? (get role-actions role) action))

(defn requires-session?
  "Check if a command requires an active session.

   Arguments:
   - command: The command keyword (e.g., :propose, :show)

   Returns true if the command requires a session, false otherwise."
  [command]
  (not (contains? sessionless-commands command)))

(defn get-allowed-actions
  "Get the set of actions allowed for a role.

   Arguments:
   - role: The session role (keyword)

   Returns a set of allowed action keywords, or nil if role is invalid."
  [role]
  (get role-actions role))

(defn get-roles-for-action
  "Get all roles that can perform a given action.

   Arguments:
   - action: The action keyword

   Returns a set of roles that can perform the action."
  [action]
  (->> role-actions
       (filter (fn [[_role actions]] (contains? actions action)))
       (map first)
       set))

;; -----------------------------------------------------------------------------
;; Session Enforcement
;; -----------------------------------------------------------------------------

(declare load-active-session session-expired? record-action!)

(defn enforce-session!
  "Enforce session validity for an action on a mote.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session token
   - action: The action being performed (keyword)
   - mote-id: The mote being acted upon

   Validates:
   1. Session exists and is active
   2. Session is not expired
   3. Session is locked to the correct mote
   4. Role is permitted to perform the action

   On success, records the action in the session audit trail.
   Returns the session map.

   Throws ExceptionInfo on any validation failure."
  [repo-path session-id action mote-id]
  (let [session (load-active-session repo-path session-id)]
    (cond
      ;; Session doesn't exist or not active
      (nil? session)
      (throw (ex-info "Invalid session"
                      {:type :invalid-session
                       :session-id session-id}))

      ;; Session has expired
      (session-expired? session)
      (throw (ex-info "Session expired"
                      {:type :session-expired
                       :session-id session-id
                       :expires-at (:expires-at session)}))

      ;; Session is locked to a different mote
      (not= mote-id (:mote-id session))
      (throw (ex-info "Session locked to different mote"
                      {:type :session-mote-mismatch
                       :session-id session-id
                       :session-mote-id (:mote-id session)
                       :requested-mote-id mote-id}))

      ;; Role is not allowed to perform this action
      (not (allowed? (:role session) action))
      (throw (ex-info "Action not allowed for role"
                      {:type :action-not-allowed
                       :session-id session-id
                       :role (:role session)
                       :action action
                       :allowed-actions (get-allowed-actions (:role session))}))

      ;; All validations passed - record action and return session
      :else
      (do
        (record-action! repo-path session-id action)
        session))))

(defn validate-session!
  "Validate a session exists and is for the correct mote (no action check).

   This is a lighter-weight validation that just ensures:
   1. Session exists and is active
   2. Session is not expired
   3. Session is locked to the correct mote

   Unlike enforce-session!, this does NOT check role permissions.
   Use for operations that any session holder can perform.

   Returns the session map.
   Throws ExceptionInfo on validation failure."
  [repo-path session-id mote-id]
  (let [session (load-active-session repo-path session-id)]
    (cond
      (nil? session)
      (throw (ex-info "Invalid session"
                      {:type :invalid-session
                       :session-id session-id}))

      (session-expired? session)
      (throw (ex-info "Session expired"
                      {:type :session-expired
                       :session-id session-id
                       :expires-at (:expires-at session)}))

      (not= mote-id (:mote-id session))
      (throw (ex-info "Session locked to different mote"
                      {:type :session-mote-mismatch
                       :session-id session-id
                       :session-mote-id (:mote-id session)
                       :requested-mote-id mote-id}))

      :else
      session)))

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
;; Cleanup Operations
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
  (or (session-expired? session :now now)
      (when-let [pid (:pid session)]
        (false? (pid-alive? pid)))))

(defn cleanup-expired-sessions!
  "Archive all expired active sessions.

   Arguments:
   - repo-path: Path to the repository root

   Returns vector of session IDs that were archived.

   Note: Uses a single timestamp for all expiration checks to avoid TOCTOU issues."
  [repo-path]
  (let [now (Instant/now)
        active-sessions (load-all-active-sessions repo-path)]
    (->> active-sessions
         (filter #(session-expired? % :now now))
         (mapv (fn [session]
                 (archive-session! repo-path (:session-id session))
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
        active-sessions (load-all-active-sessions repo-path)]
    (->> active-sessions
         (keep (fn [session]
                 (let [expired? (session-expired? session :now now)
                       crashed? (when-let [pid (:pid session)]
                                  (false? (pid-alive? pid)))]
                   (when (or expired? crashed?)
                     (archive-session! repo-path (:session-id session))
                     {:session-id (:session-id session)
                      :mote-id (:mote-id session)
                      :reason (if expired? :expired :crashed)}))))
         vec)))

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

;; -----------------------------------------------------------------------------
;; Contributors & Self-Vote Prevention
;; -----------------------------------------------------------------------------

(defn can-vote?
  "Check if an agent can vote on a mote.

   An agent cannot vote if they contributed to the mote's creation or refinement.
   This prevents self-voting and ensures independent verification.

   Arguments:
   - mote: The mote map
   - agent: The agent identifier string

   Returns true if the agent can vote, false if they are a contributor."
  [mote agent]
  (let [{:keys [created-by proposed-by refined-by refs-checked-by]}
        (:contributors mote)]
    (and (not= agent created-by)
         (not= agent proposed-by)
         (not (contains? (or refined-by #{}) agent))
         (not (contains? (or refs-checked-by #{}) agent)))))

(defn add-contributor
  "Add an agent as a contributor in a specific role.

   Arguments:
   - mote: The mote map
   - agent: The agent identifier string
   - role: The contribution type (:proposed-by, :refined-by, :refs-checked-by)

   Returns the updated mote."
  [mote agent role]
  (let [contributors (or (:contributors mote) {:created-by (:created-by mote)})]
    (assoc mote :contributors
           (case role
             :proposed-by (assoc contributors :proposed-by agent)
             :refined-by (update contributors :refined-by
                                 (fnil conj #{}) agent)
             :refs-checked-by (update contributors :refs-checked-by
                                       (fnil conj #{}) agent)
             contributors))))

(defn get-contributors
  "Get set of all contributors to a mote.

   Arguments:
   - mote: The mote map

   Returns a set of agent identifiers who contributed."
  [mote]
  (let [{:keys [created-by proposed-by refined-by refs-checked-by]}
        (:contributors mote)]
    (cond-> #{created-by}
      proposed-by (conj proposed-by)
      refined-by (into refined-by)
      refs-checked-by (into refs-checked-by))))

;; -----------------------------------------------------------------------------
;; Job Reservations (Lightweight Pre-Claims)
;; -----------------------------------------------------------------------------

(def ^:const default-reservation-duration-seconds 60)

(defn- generate-reservation-token
  "Generate a short, memorable reservation token.
   Format: 6 alphanumeric characters."
  []
  (let [chars "abcdefghijklmnopqrstuvwxyz0123456789"
        rand-char #(nth chars (rand-int (count chars)))]
    (apply str (repeatedly 6 rand-char))))

(defn- reservation-file-path
  "Get full path to a reservation file."
  [repo-path token]
  (io/full-path repo-path (path/reservation-path token)))

(defn reservation-expired?
  "Check if a reservation has expired.

   Arguments:
   - reservation: The reservation map

   Options:
   - :now - Override current time (for testing)"
  [reservation & {:keys [now]}]
  (let [now (or now (Instant/now))
        expires-at (:expires-at reservation)]
    (when expires-at
      (.isAfter now (.toInstant expires-at)))))

(defn create-reservation!
  "Create a reservation for a mote/role combination.

   Reservations are lightweight pre-claims that:
   - Lock a mote for a specific role
   - Expire quickly (60 seconds by default)
   - Must be explicitly claimed to create a session

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote to reserve
   - role: The role for the reservation

   Options:
   - :duration-seconds - Reservation duration (default: 60)

   Returns the reservation map with :token for claiming."
  [repo-path mote-id role & {:keys [duration-seconds]
                              :or {duration-seconds default-reservation-duration-seconds}}]
  (let [token (generate-reservation-token)
        now (Instant/now)
        expires (.plusSeconds now duration-seconds)
        reservation {:token token
                     :mote-id mote-id
                     :role role
                     :created-at (java.util.Date/from now)
                     :expires-at (java.util.Date/from expires)}
        file-path (reservation-file-path repo-path token)]
    ;; Ensure reservations directory exists
    (io/ensure-dir (io/full-path repo-path (path/reservations-path)))
    (io/write-edn file-path reservation)
    reservation))

(defn load-reservation
  "Load a reservation by token.

   Returns the reservation map or nil if not found/expired."
  [repo-path token]
  (let [file-path (reservation-file-path repo-path token)]
    (when (io/file-exists? file-path)
      (let [reservation (io/read-edn file-path)]
        (when-not (reservation-expired? reservation)
          reservation)))))

(defn delete-reservation!
  "Delete a reservation (consumed or expired).

   Arguments:
   - repo-path: Path to the repository root
   - token: The reservation token"
  [repo-path token]
  (let [file-path (reservation-file-path repo-path token)]
    (when (io/file-exists? file-path)
      (io/delete-file file-path))))

(defn claim-reservation!
  "Claim a reservation and create a full session.

   Arguments:
   - repo-path: Path to the repository root
   - token: The reservation token
   - agent: Agent identifier string

   Options:
   - :duration-minutes - Session duration (default: 30)

   Returns the created session, or throws if reservation invalid/expired."
  [repo-path token agent & {:keys [duration-minutes] :as opts}]
  (if-let [reservation (load-reservation repo-path token)]
    (let [{:keys [mote-id role]} reservation
          session (apply create-session! repo-path mote-id role agent
                         (mapcat identity opts))]
      ;; Delete the reservation after successful claim
      (delete-reservation! repo-path token)
      session)
    (throw (ex-info "Invalid or expired reservation"
                    {:type :invalid-reservation
                     :token token}))))

(defn cleanup-expired-reservations!
  "Remove expired reservation files.

   Arguments:
   - repo-path: Path to the repository root

   Returns count of removed reservations."
  [repo-path]
  (let [res-dir (io/full-path repo-path (path/reservations-path))]
    (if (io/dir-exists? res-dir)
      (let [files (io/list-edn-files res-dir)
            now (Instant/now)]
        (->> files
             (filter (fn [f]
                       (let [reservation (io/read-edn f)]
                         (reservation-expired? reservation :now now))))
             (map (fn [f]
                    (io/delete-file f)
                    1))
             (reduce + 0)))
      0)))

(defn list-active-reservations
  "List all active (non-expired) reservations.

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of reservation maps."
  [repo-path]
  (let [res-dir (io/full-path repo-path (path/reservations-path))]
    (if (io/dir-exists? res-dir)
      (let [files (io/list-edn-files res-dir)
            now (Instant/now)]
        (->> files
             (map io/read-edn)
             (remove #(reservation-expired? % :now now))
             vec))
      [])))

(defn mote-has-reservation?
  "Check if a mote has an active reservation for a given role.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to check
   - role: The role to check for (optional - checks any role if nil)

   Returns true if a matching active reservation exists."
  [repo-path mote-id & [role]]
  (let [reservations (list-active-reservations repo-path)]
    (some (fn [res]
            (and (= mote-id (:mote-id res))
                 (or (nil? role) (= role (:role res)))))
          reservations)))

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
          sessions (->> (load-sessions-for-agent repo-path agent)
                        (remove #(session-expired? % :now now)))]
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
             :message (str "Using session: " (subs session-id 0 (min 11 (count session-id)))
                           "... (your only active session)")})

        ;; 2+ sessions - require explicit choice
        {:error :multiple-sessions
         :message "Multiple active sessions found. Please specify --session:"
         :sessions (mapv (fn [s]
                           {:session-id (:session-id s)
                            :role (:role s)
                            :mote-id (:mote-id s)})
                         sessions)}))))
