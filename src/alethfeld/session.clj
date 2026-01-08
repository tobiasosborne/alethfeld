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
            [malli.core :as m])
  (:import [java.time Instant Duration]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const default-session-duration-minutes 30)

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

(defn- full-path
  "Prepend repo-path to a relative path."
  [repo-path relative-path]
  (str repo-path "/" relative-path))

(defn- active-session-path
  "Get full path to an active session file."
  [repo-path session-id]
  (full-path repo-path (path/session-path session-id :active)))

(defn- completed-session-path
  "Get full path to a completed session file."
  [repo-path session-id]
  (full-path repo-path (path/session-path session-id :completed)))

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
  (let [active-dir (full-path repo-path (path/active-sessions-path))
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

;; -----------------------------------------------------------------------------
;; Session Status
;; -----------------------------------------------------------------------------

(defn session-active?
  "Check if a session exists and is active (not expired).

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session ID to check

   Returns true if session exists in active directory and not expired."
  [repo-path session-id]
  (when-let [session (load-active-session repo-path session-id)]
    (let [now (java.util.Date.)
          expires (:expires-at session)]
      (.before now expires))))

(defn session-expired?
  "Check if an active session has expired.

   Arguments:
   - session: Session map

   Returns true if current time is past expires-at."
  [session]
  (let [now (java.util.Date.)
        expires (:expires-at session)]
    (.after now expires)))

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

(defn cleanup-expired-sessions!
  "Archive all expired active sessions.

   Arguments:
   - repo-path: Path to the repository root

   Returns vector of session IDs that were archived."
  [repo-path]
  (let [active-sessions (load-all-active-sessions repo-path)]
    (->> active-sessions
         (filter session-expired?)
         (mapv (fn [session]
                 (archive-session! repo-path (:session-id session))
                 (:session-id session))))))

;; -----------------------------------------------------------------------------
;; Directory Initialization
;; -----------------------------------------------------------------------------

(defn ensure-session-dirs!
  "Ensure session directories exist.

   Arguments:
   - repo-path: Path to the repository root

   Creates .alethfeld/sessions/active/ and .alethfeld/sessions/completed/."
  [repo-path]
  (io/ensure-dir (full-path repo-path (path/active-sessions-path)))
  (io/ensure-dir (full-path repo-path (path/completed-sessions-path))))

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
