(ns alethfeld.cmd
  "CLI command implementations.

   Each command function follows the pattern:
   - Takes a context map with :id, :args, :options
   - Returns data to be formatted and output
   - Throws ExceptionInfo for errors"
  (:require [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.tx :as tx]
            [alethfeld.cli :as cli]
            [alethfeld.mote :as mote]
            [alethfeld.id :as id]
            [alethfeld.path :as path]
            [alethfeld.dag :as dag]
            [alethfeld.job :as job]
            [alethfeld.prompt :as prompt]
            [alethfeld.proposal :as proposal]
            [alethfeld.session :as session]
            [alethfeld.verify :as verify]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Init Command
;; -----------------------------------------------------------------------------

(defn cmd-init!
  "Initialize an Alethfeld repository.

   Creates .alethfeld/ directory structure with:
   - config.edn (project configuration)
   - motes/ directory
   - proposed/ directory
   - archive/ directory
   - sessions/active/ directory
   - sessions/completed/ directory

   Also initializes git and commits the initial structure.

   Options:
   - :name - Project name (default: 'Alethfeld Project')

   Returns the config that was created."
  [{:keys [options]}]
  (let [repo-path "."
        project-name (:name options "Alethfeld Project")]
    ;; Check if already initialized
    (when (store/repo-exists? repo-path)
      (throw (ex-info "Repository already initialized"
                      {:type :already-initialized
                       :path repo-path})))
    ;; Initialize git first (so we can commit the init)
    (git/git-init! repo-path)
    ;; Configure git user if needed
    (when-not (git/git-config repo-path "user.name")
      (git/git-config! repo-path "user.name" "alethfeld"))
    (when-not (git/git-config repo-path "user.email")
      (git/git-config! repo-path "user.email" "alethfeld@local"))
    ;; Initialize repository structure
    (let [config (store/init-repo! repo-path :project-name project-name)]
      ;; Initialize session directories
      (session/ensure-session-dirs! repo-path)
      ;; Commit the initial structure
      (git/git-add-all! repo-path)
      (git/git-commit! repo-path (str "Initialize Alethfeld: " project-name))
      {:message (str "Initialized Alethfeld repository: " project-name)
       :config config})))

;; -----------------------------------------------------------------------------
;; Show Command
;; -----------------------------------------------------------------------------

(defn cmd-show
  "Display a mote's details.

   Arguments (in context):
   - :id - The mote ID to display

   Returns the mote map, or throws if not found."
  [{:keys [id]}]
  (let [repo-path "."
        mote (store/load-mote repo-path id)]
    (if mote
      mote
      (throw (ex-info "Mote not found"
                      {:type :not-found
                       :mote-id id})))))

;; -----------------------------------------------------------------------------
;; Create Command
;; -----------------------------------------------------------------------------

(defn- next-root-id
  "Get the next available root mote ID.
   Scans existing motes and returns the next integer as a string."
  [repo-path]
  (let [motes (store/load-all-motes repo-path)
        root-ids (->> (keys motes)
                      (filter #(= 1 (id/id-depth %)))
                      (map #(parse-long %))
                      (filter some?))]
    (str (if (empty? root-ids)
           1
           (inc (apply max root-ids))))))

(defn cmd-create!
  "Create a new mote.

   Arguments (in context):
   - :id - Parent mote ID (required unless --root)

   Options:
   - :claim - The claim text (required)
   - :root - Create root mote (no parent)
   - :difficulty - Difficulty 1-5 (optional, inherits from parent or defaults to 3)
   - :priority - Priority :p0-:p4 (optional, inherits from parent or defaults to :p2)
   - :agent - Agent name (default: 'cli-user')

   For root motes:
   - Generates next available root ID (1, 2, 3, ...)

   For child motes:
   - Parent must exist
   - Generates next child ID based on parent's existing children
   - Inherits priority/difficulty from parent if not specified

   Returns the created mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim root difficulty priority agent]} options
        agent (or agent "cli-user")]

    ;; Validation
    (when-not claim
      (throw (ex-info "Claim is required"
                      {:type :validation-failed
                       :errors ["--claim is required"]})))

    (when (and root id)
      (throw (ex-info "Cannot specify both --root and parent ID"
                      {:type :validation-failed
                       :errors ["Use either --root or provide a parent ID, not both"]})))

    (when (and (not root) (not id))
      (throw (ex-info "Parent ID required for non-root motes"
                      {:type :validation-failed
                       :errors ["Provide parent ID or use --root for root motes"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (if root
      ;; Create root mote
      (let [new-id (next-root-id repo-path)
            new-mote (mote/make-root-mote new-id claim agent
                                          :difficulty (or difficulty 3)
                                          :priority (or priority :p2))
            _ (tx/atomic-write! repo-path
                                (str "Create root mote " new-id)
                                [new-mote])]
        new-mote)

      ;; Create child mote
      (let [parent (store/load-mote repo-path id)]
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id id})))

        (let [existing-children (:children parent)
              new-id (id/next-child-id id existing-children)
              new-mote (mote/make-child-mote new-id claim agent parent
                                             :difficulty (or difficulty (:difficulty parent))
                                             :priority (or priority (:priority parent)))
              updated-parent (mote/add-child parent new-id)
              _ (tx/atomic-write! repo-path
                                  (str "Create child mote " new-id)
                                  [new-mote updated-parent])]
          new-mote)))))

;; -----------------------------------------------------------------------------
;; Stale Session Cleanup Helper
;; -----------------------------------------------------------------------------

(defn- cleanup-stale-sessions-and-claims!
  "Clean up stale sessions and release associated mote claims.

   Called at the start of cmd-ready to recover from crashed agents.

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of cleaned-up session info (or empty vector if none)."
  [repo-path]
  (let [cleaned-up (session/cleanup-stale-sessions! repo-path)]
    (when (seq cleaned-up)
      ;; Clear mote claims for each cleaned-up session
      (let [mote-ids (distinct (map :mote-id cleaned-up))
            motes-to-update (keep (fn [mote-id]
                                    (when-let [m (store/load-mote repo-path mote-id)]
                                      (when (:claimed-by m)
                                        (mote/clear-claim m))))
                                  mote-ids)]
        (when (seq motes-to-update)
          (tx/atomic-write! repo-path
                            (str "Cleanup stale sessions: "
                                 (str/join ", " (map :mote-id cleaned-up)))
                            (vec motes-to-update)))))
    cleaned-up))

;; -----------------------------------------------------------------------------
;; Ready Command
;; -----------------------------------------------------------------------------

(defn- parse-difficulty-spec
  "Parse difficulty spec string into a value for job/matches-filter?.

   Formats:
   - \"3\" -> 3 (exact match)
   - \"2-4\" -> [2 4] (range)

   Returns nil if invalid."
  [spec]
  (when spec
    (if (str/includes? spec "-")
      (let [[min-s max-s] (str/split spec #"-")]
        (try
          [(Integer/parseInt min-s) (Integer/parseInt max-s)]
          (catch Exception _ nil)))
      (try
        (Integer/parseInt spec)
        (catch Exception _ nil)))))

(defn- parse-priority-spec
  "Parse priority spec string into a value for job/matches-filter?.

   Formats:
   - \"p2\" -> :p2 (exact match)
   - \"p1-p3\" -> [:p1 :p3] (range)

   Returns nil if invalid."
  [spec]
  (when spec
    (let [spec (str/lower-case spec)]
      (if (str/includes? spec "-")
        (let [[min-s max-s] (str/split spec #"-")]
          (when (and (re-matches #"p[0-4]" min-s)
                     (re-matches #"p[0-4]" max-s))
            [(keyword min-s) (keyword max-s)]))
        (when (re-matches #"p[0-4]" spec)
          (keyword spec))))))

(defn- resolve-children
  "Resolve child IDs to full mote maps for prompt rendering."
  [mote motes]
  (let [proposal (:proposal mote)
        child-ids (if proposal
                    (:children proposal)
                    (:children mote))]
    (->> child-ids
         (keep #(get motes %))
         vec)))

(defn cmd-ready
  "Get next job(s) for an agent.

   Options:
   - :agent - Agent name (auto-claims jobs unless --no-claim)
   - :role - Filter by role (:proposer, :advisor, :prover, :verifier, :ref-checker, :counterexample)
   - :difficulty - Difficulty filter (\"N\" for exact, \"N-M\" for range)
   - :priority - Priority filter (\"pN\" for exact, \"pN-pM\" for range)
   - :max - Maximum jobs to return (default: 1)
   - :no-claim - Don't auto-claim jobs

   Returns a vector of Job maps, each containing:
   - :job-id, :mote-id, :role, :difficulty, :priority
   - :mote, :parent, :siblings
   - :prompt (rendered prompt for the role)

   Note: Automatically cleans up stale sessions (expired or crashed)
   before selecting jobs."
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [agent role difficulty priority max no-claim]} options
        max-jobs (or max 1)]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Clean up stale sessions (expired or crashed agents)
    (cleanup-stale-sessions-and-claims! repo-path)

    ;; Parse difficulty/priority specs
    (let [difficulty-filter (parse-difficulty-spec difficulty)
          priority-filter (parse-priority-spec priority)

          ;; Load config and motes
          config (store/load-config repo-path)
          claim-timeout (:claim-timeout-minutes config)
          motes (store/load-all-motes repo-path)

          ;; Select jobs (with claim timeout enforcement)
          jobs (job/select-jobs motes
                                :role role
                                :difficulty difficulty-filter
                                :priority priority-filter
                                :max max-jobs
                                :claim-timeout claim-timeout)

          ;; Enrich jobs with prompts
          jobs-with-prompts (mapv (fn [j]
                                    (let [resolved-children (resolve-children (:mote j) motes)
                                          rendered-prompt (prompt/render-prompt j :resolved-children resolved-children)]
                                      (assoc j :prompt rendered-prompt)))
                                  jobs)]

      ;; Auto-claim if agent provided and not --no-claim
      (if (and agent (not no-claim) (seq jobs-with-prompts))
        (let [;; Ensure session directories exist
              _ (session/ensure-session-dirs! repo-path)
              ;; Update motes with claims and create sessions
              claimed-jobs (mapv (fn [j]
                                   (let [;; Create session for this job
                                         job-role (:role j)
                                         sess (session/create-session! repo-path
                                                                       (:mote-id j)
                                                                       job-role
                                                                       agent)
                                         ;; Update mote with claim
                                         updated-mote (mote/set-claimed-by (:mote j) agent)
                                         ;; Re-render prompt with session context
                                         resolved-children (resolve-children (:mote j) motes)
                                         session-prompt (prompt/render-prompt j
                                                                              :resolved-children resolved-children
                                                                              :session sess)]
                                     (assoc j
                                            :mote updated-mote
                                            :claimed-by agent
                                            :session-id (:session-id sess)
                                            :session sess
                                            :prompt session-prompt)))
                                 jobs-with-prompts)
              ;; Extract updated motes for atomic write
              updated-motes (mapv :mote claimed-jobs)
              ;; Commit all claims atomically via transaction layer
              commit-msg (str "Claim jobs for " agent ": "
                              (str/join ", " (map :mote-id claimed-jobs)))]
          (tx/atomic-write! repo-path commit-msg updated-motes :validate false)
          claimed-jobs)

        ;; Return without claiming
        jobs-with-prompts))))

;; -----------------------------------------------------------------------------
;; Propose Command
;; -----------------------------------------------------------------------------

(defn- parse-claims
  "Parse claims from command-line args.

   Each claim is a string. Can optionally include difficulty with @ notation:
   'My claim @3' -> {:claim 'My claim' :difficulty 3}
   'My claim' -> {:claim 'My claim'}

   Returns vector of {:claim ... :difficulty ...} maps."
  [args]
  (mapv (fn [arg]
          (if-let [[_ claim difficulty] (re-matches #"(.+?)\s*@(\d+)\s*$" arg)]
            {:claim (str/trim claim)
             :difficulty (Integer/parseInt difficulty)}
            {:claim arg}))
        args))

(defn cmd-propose!
  "Create a proposal to decompose a mote into children.

   Arguments (in context):
   - :id - The parent mote ID (required)
   - :args - Child claims (required, at least one)
             Each claim can optionally include difficulty with @ notation:
             'My claim @3' sets difficulty to 3

   Options:
   - :session - Session token (required)
   - :agent - Agent name (defaults to session agent)

   Creates proposed children with :proposed status and attaches
   a proposal to the parent. Sets parent taint to :needs-proposal-review.

   Returns map with:
   - :proposal - The created proposal
   - :children - Vector of created child motes"
  [{:keys [id args options]}]
  (let [repo-path "."
        session-id (:session options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID"]})))

    (when (empty? args)
      (throw (ex-info "At least one claim is required"
                      {:type :validation-failed
                       :errors ["Provide at least one claim as argument"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [sess (session/enforce-session! repo-path session-id :propose id)
          agent (or (:agent options) (:agent sess))
          claims (parse-claims args)
          result (proposal/create-proposal! repo-path id claims agent)]
      (:result result))))

;; -----------------------------------------------------------------------------
;; Approve Command
;; -----------------------------------------------------------------------------

(defn cmd-approve!
  "Vote to approve a proposal on a mote.

   Arguments (in context):
   - :id - The mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :agent - Agent name (defaults to session agent)
   - :reason - Reason for approval (optional)

   If quorum is reached:
   - Children move from proposed/ to motes/ with :fixed status
   - Parent :children is populated
   - Parent proposal is cleared

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :approved or :pending
   - :promoted-children - Child IDs if approved"
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        reason (:reason options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [sess (session/enforce-session! repo-path session-id :approve id)
          agent (or (:agent options) (:agent sess))
          result (proposal/approve-proposal! repo-path id agent :reason reason)]
      (:result result))))

;; -----------------------------------------------------------------------------
;; Reject Command
;; -----------------------------------------------------------------------------

(defn cmd-reject!
  "Vote to reject a proposal on a mote.

   Arguments (in context):
   - :id - The mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :agent - Agent name (defaults to session agent)
   - :reason - Reason for rejection (optional)

   If quorum is reached:
   - Children move from proposed/ to archive/ with :rejected status
   - Parent proposal is cleared
   - Parent gets :needs-decomposition taint

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :rejected or :pending
   - :archived-children - Child IDs if rejected"
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        reason (:reason options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [sess (session/enforce-session! repo-path session-id :reject id)
          agent (or (:agent options) (:agent sess))
          result (proposal/reject-proposal! repo-path id agent :reason reason)]
      (:result result))))

;; -----------------------------------------------------------------------------
;; Update Command
;; -----------------------------------------------------------------------------

(def ^:private valid-priorities
  "Valid priority values."
  #{:p0 :p1 :p2 :p3 :p4})

(defn- parse-priority
  "Parse priority string to keyword. Returns nil if invalid."
  [s]
  (when s
    (let [kw (keyword (str/lower-case s))]
      (when (valid-priorities kw)
        kw))))

(defn cmd-update!
  "Update mote fields.

   Arguments (in context):
   - :id - The mote ID to update (required)

   Options:
   - :claim - New claim text
   - :priority - New priority (p0-p4)
   - :difficulty - New difficulty (1-5)
   - :agent - Agent name (default: 'cli-user')

   At least one of claim/priority/difficulty must be provided.

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim priority difficulty agent]} options
        agent (or agent "cli-user")]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to update"]})))

    (when (and (nil? claim) (nil? priority) (nil? difficulty))
      (throw (ex-info "No update fields provided"
                      {:type :validation-failed
                       :errors ["Provide at least one of --claim, --priority, or --difficulty"]})))

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

      ;; Parse and validate priority
      (let [parsed-priority (when priority (parse-priority priority))]
        (when (and priority (nil? parsed-priority))
          (throw (ex-info "Invalid priority"
                          {:type :validation-failed
                           :errors [(str "Priority must be p0-p4, got: " priority)]})))

        ;; Validate difficulty
        (when (and difficulty (or (< difficulty 1) (> difficulty 5)))
          (throw (ex-info "Invalid difficulty"
                          {:type :validation-failed
                           :errors [(str "Difficulty must be 1-5, got: " difficulty)]})))

        ;; Apply updates
        (let [updated-mote (cond-> current-mote
                            claim (mote/set-claim claim)
                            parsed-priority (mote/set-priority parsed-priority)
                            difficulty (mote/set-difficulty difficulty))]
          (tx/atomic-write! repo-path
                            (str "Update mote " id)
                            [updated-mote])
          updated-mote)))))

;; -----------------------------------------------------------------------------
;; Vote Command
;; -----------------------------------------------------------------------------

(defn cmd-vote!
  "Cast a verification vote on a mote.

   Arguments (in context):
   - :id - The mote ID to vote on (required)

   Options:
   - :session - Session token (required)
   - :for - Vote in favor of verification
   - :against - Vote against verification
   - :reason - Reason for vote (optional)
   - :agent - Agent name (defaults to session agent)

   Exactly one of --for or --against must be provided.

   When quorum is reached:
   - :verified if unanimous for votes
   - :refuted if unanimous against votes
   - :contested if mixed votes

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :pending, :verified, :refuted, or :contested
   - :status-changed - Whether the mote status changed
   - :new-status - The new mote status"
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [for against reason session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to vote on"]})))

    (when (and for against)
      (throw (ex-info "Cannot vote both for and against"
                      {:type :validation-failed
                       :errors ["Provide either --for or --against, not both"]})))

    (when (and (not for) (not against))
      (throw (ex-info "Vote direction required"
                      {:type :validation-failed
                       :errors ["Provide --for or --against"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [sess (session/enforce-session! repo-path session :vote id)
          agent (or (:agent options) (:agent sess))
          vote-type (if for :for :against)
          result (verify/cast-vote! repo-path id agent vote-type :reason reason)]
      (:result result))))

;; -----------------------------------------------------------------------------
;; Taint Command
;; -----------------------------------------------------------------------------

(def ^:private valid-taints
  "Valid taint values."
  #{:needs-decomposition :needs-proposal-review :needs-refinement
    :needs-verification :needs-refs :needs-votes :needs-counterexample})

(defn- parse-taint
  "Parse taint string to keyword. Returns nil if invalid."
  [s]
  (when s
    (let [kw (keyword (str/replace (str/lower-case s) #"^:" ""))]
      (when (valid-taints kw)
        kw))))

(defn cmd-taint!
  "Add or remove taints from a mote.

   Arguments (in context):
   - :id - The mote ID to modify (required)

   Options:
   - :session - Session token (required)
   - :add - Taint to add (can be specified multiple times)
   - :remove - Taint to remove (can be specified multiple times)

   Valid taints:
   - needs-decomposition
   - needs-proposal-review
   - needs-refinement
   - needs-verification
   - needs-refs
   - needs-votes
   - needs-counterexample

   At least one of --add or --remove must be provided.
   Adding taints requires :taint-add permission (verifier role).
   Removing taints requires :taint-remove permission (prover, ref-checker roles).

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [add remove session]} options
        ;; Support both single value and vector for add/remove
        adds (if (sequential? add) add (when add [add]))
        removes (if (sequential? remove) remove (when remove [remove]))]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to modify taints"]})))

    (when (and (empty? adds) (empty? removes))
      (throw (ex-info "No taint changes provided"
                      {:type :validation-failed
                       :errors ["Provide at least one --add or --remove"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Enforce session - check both actions if both operations requested
    (when (seq adds)
      (session/enforce-session! repo-path session :taint-add id))
    (when (seq removes)
      (session/enforce-session! repo-path session :taint-remove id))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Parse and validate taints
      (let [parsed-adds (map parse-taint adds)
            parsed-removes (map parse-taint removes)]
        (when-let [invalid (first (filter nil? (concat
                                                 (when (seq adds) parsed-adds)
                                                 (when (seq removes) parsed-removes))))]
          (let [invalid-values (concat
                                 (filter #(nil? (parse-taint %)) adds)
                                 (filter #(nil? (parse-taint %)) removes))]
            (throw (ex-info "Invalid taint"
                            {:type :validation-failed
                             :errors [(str "Invalid taint: " (first invalid-values)
                                           ". Valid taints: " (str/join ", " (map name valid-taints)))]}))))

        ;; Apply taint changes
        (let [updated-mote (as-> current-mote m
                            (reduce mote/add-taint m (filter some? parsed-adds))
                            (reduce mote/remove-taint m (filter some? parsed-removes)))]
          (tx/atomic-write! repo-path
                            (str "Update taints on " id)
                            [updated-mote])
          updated-mote)))))

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

   Errors if mote is already claimed by another agent.

   Returns the updated mote with :session-id."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [agent role]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to claim"]})))

    (when-not agent
      (throw (ex-info "Agent name is required"
                      {:type :validation-failed
                       :errors ["Provide --agent to claim the mote"]})))

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
      (let [current-claimer (:claimed-by current-mote)]
        (when (and current-claimer (not= current-claimer agent))
          (throw (ex-info "Mote already claimed"
                          {:type :already-claimed
                           :mote-id id
                           :claimed-by current-claimer}))))

      ;; Ensure session directories exist
      (session/ensure-session-dirs! repo-path)

      ;; Create session
      (let [sess (session/create-session! repo-path id role agent)
            updated-mote (mote/set-claimed-by current-mote agent)]
        (tx/atomic-write! repo-path
                          (str "Claim mote " id " for " agent " as " (name role))
                          [updated-mote])
        (assoc updated-mote :session-id (:session-id sess))))))

;; -----------------------------------------------------------------------------
;; Unclaim Command
;; -----------------------------------------------------------------------------

(defn cmd-unclaim!
  "Release claim on a mote.

   Arguments (in context):
   - :id - The mote ID to unclaim (required)

   Options:
   - :session - Session token (required)

   Note: Prefer using 'af done' which properly ends the session.
   This command releases the claim but does not end the session.

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)]

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

    ;; Session enforcement (lighter validation - any session holder can unclaim)
    (when-not session-id
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (session/validate-session! repo-path session-id id)

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Clear claim
      (let [updated-mote (mote/clear-claim current-mote)]
        (tx/atomic-write! repo-path
                          (str "Unclaim mote " id)
                          [updated-mote])
        updated-mote))))

;; -----------------------------------------------------------------------------
;; Done Command
;; -----------------------------------------------------------------------------

(defn cmd-done!
  "End a session and release the claimed mote.

   Options:
   - :session - Session token (required)

   Ends the active session and releases the mote for other agents.
   The session is moved to the completed directory with stats recorded.

   Returns map with:
   - :session-id - The session that was ended
   - :mote-id - The mote that was released
   - :action-count - Number of actions performed in the session"
  [{:keys [options]}]
  (let [repo-path "."
        session-id (:session options)]

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

        ;; End session with stats and clear mote claim
        (let [ended-session (session/end-session! repo-path session-id :record-stats true)
              updated-mote (mote/clear-claim mote)]

          ;; Commit the changes
          (tx/atomic-write! repo-path
                            (str "Done: end session for " mote-id)
                            [updated-mote])

          {:session-id session-id
           :mote-id mote-id
           :action-count (:action-count ended-session)})))))

;; -----------------------------------------------------------------------------
;; Add-Ref Command
;; -----------------------------------------------------------------------------

(defn cmd-add-ref!
  "Add an external reference to a mote.

   Arguments (in context):
   - :id - The mote ID to add reference to (required)

   Options:
   - :session - Session token (required)
   - :ref - The citation/reference text (required)
   - :note - Optional note explaining what the reference provides

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [ref note session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add reference to"]})))

    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the citation"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (session/enforce-session! repo-path session :add-ref id)

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Create external reference and add to mote
      (let [external-ref (cond-> {:type :external :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote external-ref)]
        (tx/atomic-write! repo-path
                          (str "Add external reference to " id)
                          [updated-mote])
        updated-mote))))

;; -----------------------------------------------------------------------------
;; Add-Assumption Command
;; -----------------------------------------------------------------------------

(defn cmd-add-assumption!
  "Add an internal assumption (reference to another mote) to a mote.

   Arguments (in context):
   - :id - The mote ID to add assumption to (required)

   Options:
   - :session - Session token (required)
   - :ref - The referenced mote ID (required)
   - :note - Optional note explaining why this assumption is needed

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [ref note session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add assumption to"]})))

    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the mote ID to reference"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (session/enforce-session! repo-path session :add-assumption id)

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Validate referenced mote exists
      (when-not (store/load-mote repo-path ref)
        (throw (ex-info "Referenced mote not found"
                        {:type :not-found
                         :mote-id ref})))

      ;; Create internal reference and add to mote
      (let [internal-ref (cond-> {:type :internal :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote internal-ref)]
        (tx/atomic-write! repo-path
                          (str "Add internal assumption to " id)
                          [updated-mote])
        updated-mote))))

;; -----------------------------------------------------------------------------
;; Add-Definition Command
;; -----------------------------------------------------------------------------

(defn cmd-add-definition!
  "Add a symbol definition to a mote.

   Arguments (in context):
   - :id - The mote ID to add definition to (required)

   Options:
   - :session - Session token (required)
   - :symbol - The symbol to define (required)
   - :meaning - The meaning/definition of the symbol (required)

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [symbol meaning session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add definition to"]})))

    (when-not symbol
      (throw (ex-info "Symbol is required"
                      {:type :validation-failed
                       :errors ["Provide --symbol to define"]})))

    (when-not meaning
      (throw (ex-info "Meaning is required"
                      {:type :validation-failed
                       :errors ["Provide --meaning for the symbol"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (session/enforce-session! repo-path session :add-definition id)

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Create definition and add to mote
      (let [definition {:symbol symbol :meaning meaning}
            updated-mote (mote/add-definition current-mote definition)]
        (tx/atomic-write! repo-path
                          (str "Add definition to " id)
                          [updated-mote])
        updated-mote))))

;; -----------------------------------------------------------------------------
;; Check Command
;; -----------------------------------------------------------------------------

(defn cmd-check
  "Validate entire DAG integrity.

   Validates:
   1. All parent refs exist
   2. All children refs exist and point back
   3. No cycles in assumption graph
   4. All internal assumption refs exist
   5. Schema validation on all motes

   Returns a result map:
   - :valid? - true if all validations passed
   - :mote-count - number of motes checked
   - :schema-errors - vector of schema validation errors (if any)
   - :dag-errors - vector of DAG validation errors (if any)"
  [_ctx]
  (let [repo-path "."]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load all motes (including proposed)
    (let [motes (store/load-all-motes repo-path :include-archived true)

          ;; Schema validation
          schema-errors (->> motes
                             (keep (fn [[mote-id mote]]
                                     (when-let [explanation (store/validate-mote mote)]
                                       {:mote-id mote-id
                                        :error explanation})))
                             vec)

          ;; DAG validation
          dag-result (dag/validate-mote-graph motes)
          dag-errors (:errors dag-result)

          ;; Combine results
          all-valid? (and (empty? schema-errors)
                          (:valid? dag-result))]

      {:valid? all-valid?
       :mote-count (count motes)
       :schema-errors (when (seq schema-errors) schema-errors)
       :dag-errors (when (seq dag-errors) dag-errors)})))

;; -----------------------------------------------------------------------------
;; Log Command
;; -----------------------------------------------------------------------------

(defn cmd-log
  "Show git history for a mote.

   Arguments (in context):
   - :id - The mote ID to show history for (required)

   Options:
   - :limit - Maximum number of commits to show (default: 50)

   Returns a vector of commit maps:
   - :sha - Commit SHA (short)
   - :message - Commit message"
  [{:keys [id options]}]
  (let [repo-path "."
        limit (or (:limit options) 50)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to show history for"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load mote to get its current status/path
    (let [mote (store/load-mote repo-path id)]
      (when-not mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Get file path for the mote
      (let [mote-file-path (path/mote-id->path id (:status mote))
            history (git/git-log repo-path :path mote-file-path :max-count limit)]
        (or history [])))))

;; -----------------------------------------------------------------------------
;; Sync Command
;; -----------------------------------------------------------------------------

(defn- iso-timestamp
  "Get current ISO 8601 timestamp."
  []
  (.format (java.time.OffsetDateTime/now)
           java.time.format.DateTimeFormatter/ISO_OFFSET_DATE_TIME))

(defn cmd-sync!
  "Synchronize local changes with remote.

   Equivalent to:
   1. git pull --rebase
   2. git add .alethfeld/
   3. git commit -m 'af sync <timestamp>' --allow-empty
   4. git push

   Options:
   - :no-push - Skip the push step (useful for offline work)

   Returns a result map:
   - :pulled - true if pull succeeded (or :skipped if no remote)
   - :committed - true if commit was made
   - :pushed - true if push succeeded (or :skipped if no remote or --no-push)
   - :commit-sha - SHA of the sync commit (if committed)

   Note: If no remote is configured, pull and push are skipped gracefully."
  [{:keys [options]}]
  (let [repo-path "."
        no-push (:no-push options)]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Check git is initialized
    (when-not (git/git-initialized? repo-path)
      (throw (ex-info "Not a git repository"
                      {:type :not-git-repo
                       :path repo-path})))

    (let [has-remote (git/git-has-remote? repo-path)

          ;; Step 1: Pull (if remote exists)
          pull-result (when has-remote
                        (try
                          (git/git-pull! repo-path)
                          (catch Exception e
                            (let [data (ex-data e)]
                              ;; Re-throw if it's not just "no remote"
                              (when-not (= :no-remote (:type data))
                                (throw e))
                              nil))))

          ;; Step 2: Stage all .alethfeld/ changes
          _ (git/git-add-all! repo-path)

          ;; Step 3: Commit with timestamp
          timestamp (iso-timestamp)
          commit-msg (str "af sync " timestamp)
          commit-result (git/git-commit! repo-path commit-msg :allow-empty true)

          ;; Step 4: Push (if remote exists and not --no-push)
          push-result (when (and has-remote (not no-push))
                        (try
                          (git/git-push! repo-path)
                          (catch Exception e
                            (let [data (ex-data e)]
                              ;; Re-throw if it's not just "no remote"
                              (when-not (= :no-remote (:type data))
                                (throw e))
                              nil))))]

      {:pulled (if pull-result true :skipped)
       :committed true
       :pushed (cond
                 no-push :skipped
                 (not has-remote) :skipped
                 push-result true
                 :else false)
       :commit-sha (:sha commit-result)})))

;; -----------------------------------------------------------------------------
;; Config Command
;; -----------------------------------------------------------------------------

(def ^:private config-keys
  "Valid configuration keys with their types and defaults."
  {:project-name {:type :string :default "Unnamed Proof"}
   :version {:type :string :default "0.1"}
   :default-difficulty {:type :int :min 1 :max 5 :default 3}
   :proposal-quorum {:type :int :min 1 :default 2}
   :vote-quorum {:type :int :min 1 :default 2}
   :claim-timeout-minutes {:type :int :min 1 :default 30}})

(defn- parse-config-value
  "Parse a string value to the appropriate type for a config key."
  [key-name value-str]
  (let [key-kw (keyword key-name)
        spec (get config-keys key-kw)]
    (when-not spec
      (throw (ex-info "Unknown config key"
                      {:type :validation-failed
                       :errors [(str "Unknown config key: " key-name
                                     ". Valid keys: " (str/join ", " (map name (keys config-keys))))]})))
    (case (:type spec)
      :string value-str
      :int (let [parsed (parse-long value-str)]
             (when-not parsed
               (throw (ex-info "Invalid integer value"
                               {:type :validation-failed
                                :errors [(str "Expected integer for " key-name ", got: " value-str)]})))
             (when (and (:min spec) (< parsed (:min spec)))
               (throw (ex-info "Value below minimum"
                               {:type :validation-failed
                                :errors [(str key-name " must be >= " (:min spec))]})))
             (when (and (:max spec) (> parsed (:max spec)))
               (throw (ex-info "Value above maximum"
                               {:type :validation-failed
                                :errors [(str key-name " must be <= " (:max spec))]})))
             parsed))))

(defn cmd-config
  "Manage project configuration.

   Subcommands:
   - list: Show all configuration
   - get <key>: Get a specific value
   - set <key> <value>: Set a value

   Valid keys:
   - project-name (string)
   - version (string)
   - default-difficulty (1-5)
   - proposal-quorum (integer >= 1)
   - vote-quorum (integer >= 1)
   - claim-timeout-minutes (integer >= 1)"
  [{:keys [id args]}]
  (let [repo-path "."
        subcommand id]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (case subcommand
      ;; List all config
      ("list" nil)
      (let [config (store/load-config repo-path)]
        {:config config
         :keys (keys config-keys)})

      ;; Get a specific key
      "get"
      (let [key-name (first args)]
        (when-not key-name
          (throw (ex-info "Config key required"
                          {:type :validation-failed
                           :errors ["Usage: af config get <key>"]})))
        (let [key-kw (keyword key-name)
              config (store/load-config repo-path)
              spec (get config-keys key-kw)]
          (when-not spec
            (throw (ex-info "Unknown config key"
                            {:type :validation-failed
                             :errors [(str "Unknown config key: " key-name
                                           ". Valid keys: " (str/join ", " (map name (keys config-keys))))]})))
          {:key key-kw
           :value (get config key-kw (:default spec))
           :default (:default spec)}))

      ;; Set a key
      "set"
      (let [key-name (first args)
            value-str (second args)]
        (when-not key-name
          (throw (ex-info "Config key required"
                          {:type :validation-failed
                           :errors ["Usage: af config set <key> <value>"]})))
        (when-not value-str
          (throw (ex-info "Config value required"
                          {:type :validation-failed
                           :errors ["Usage: af config set <key> <value>"]})))
        (let [key-kw (keyword key-name)
              parsed-value (parse-config-value key-name value-str)
              config (store/load-config repo-path)
              new-config (assoc config key-kw parsed-value)]
          (tx/atomic-write-config! repo-path
                                   (str "Set config: " key-name " = " parsed-value)
                                   new-config)
          {:key key-kw
           :value parsed-value
           :previous (get config key-kw)}))

      ;; Unknown subcommand
      (throw (ex-info "Unknown config subcommand"
                      {:type :validation-failed
                       :errors [(str "Unknown subcommand: " subcommand
                                     ". Use: list, get, set")]})))))

;; -----------------------------------------------------------------------------
;; Tree Command
;; -----------------------------------------------------------------------------

(defn- format-status
  "Format mote status as a bracketed indicator."
  [status]
  (str "[" (name status) "]"))

(defn- format-taints
  "Format mote taints as parenthesized indicators."
  [taints]
  (when (seq taints)
    (str " (" (str/join ", " (map name taints)) ")")))

(defn- truncate-claim
  "Truncate claim text to a maximum length."
  [claim max-len]
  (if (> (count claim) max-len)
    (str (subs claim 0 (- max-len 3)) "...")
    claim))

(defn- render-tree-node
  "Render a single tree node line.

   Arguments:
   - mote: The mote to render
   - prefix: The prefix string for indentation
   - connector: The connector string ('+--', '\\--', or empty)
   - max-claim-len: Maximum length for claim text

   Returns a string representing this node."
  [mote prefix connector max-claim-len]
  (let [mote-id (:id mote)
        status (format-status (:status mote))
        taints (format-taints (:taint mote))
        claim (truncate-claim (:claim mote) max-claim-len)]
    (str prefix connector mote-id " " status " " claim taints)))

(defn- render-tree
  "Recursively render a tree of motes.

   Arguments:
   - mote: The root mote to render
   - motes: Map of all motes for child lookup
   - prefix: Current indentation prefix
   - is-last: Whether this is the last child
   - current-depth: Current depth in the tree
   - max-depth: Maximum depth to render (nil for unlimited)
   - max-claim-len: Maximum length for claim text
   - is-root: Whether this is the root node (no connector)

   Returns a vector of strings (one per line)."
  ([mote motes prefix is-last current-depth max-depth max-claim-len]
   ;; Entry point - root node
   (render-tree mote motes prefix is-last current-depth max-depth max-claim-len true))

  ([mote motes prefix is-last current-depth max-depth max-claim-len is-root]
   (let [;; Determine connector for this node
         connector (if is-root "" (if is-last "\\-- " "+-- "))
         ;; Render this node
         node-line (render-tree-node mote prefix connector max-claim-len)
         ;; Get children
         children (:children mote)
         ;; Check if we should render children
         should-render-children? (and (seq children)
                                      (or (nil? max-depth)
                                          (< current-depth max-depth)))
         ;; Calculate prefix for children
         child-prefix (if is-root
                        ""
                        (str prefix (if is-last "    " "|   ")))]
     (if should-render-children?
       ;; Render this node and all children
       (let [child-motes (keep #(get motes %) children)
             child-count (count child-motes)
             child-lines (mapcat
                           (fn [idx child]
                             (render-tree child motes child-prefix
                                          (= idx (dec child-count))
                                          (inc current-depth)
                                          max-depth
                                          max-claim-len
                                          false))
                           (range)
                           child-motes)]
         (cons node-line child-lines))
       ;; Just this node
       [node-line]))))

(defn cmd-tree
  "Display a mote and its descendants as a tree.

   Arguments (in context):
   - :id - The mote ID to display (required)

   Options:
   - :depth - Maximum depth to display (default: unlimited)

   Returns a map with:
   - :lines - Vector of rendered tree lines
   - :mote-count - Number of motes displayed"
  [{:keys [id options]}]
  (let [repo-path "."
        max-depth (:depth options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to display tree for"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load the mote
    (let [mote (store/load-mote repo-path id)]
      (when-not mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Load all motes for child lookup
      (let [motes (store/load-all-motes repo-path)
            ;; Render the tree
            lines (render-tree mote motes "" true 0 max-depth 60)]
        {:lines (vec lines)
         :mote-count (count lines)}))))

;; -----------------------------------------------------------------------------
;; Status Command
;; -----------------------------------------------------------------------------

(defn cmd-status
  "Display project status summary.

   Returns a map with:
   - :project-name - Name of the project
   - :root-motes - Number of root motes
   - :total-motes - Total number of motes
   - :status-counts - Map of status -> count
   - :taint-counts - Map of taint -> count
   - :active-sessions - Number of active sessions
   - :ready-for-work - Number of workable motes"
  [_ctx]
  (let [repo-path "."]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (let [;; Load config for project name
          config (store/load-config repo-path)
          project-name (:project-name config "Unnamed Project")

          ;; Load all motes
          motes (store/load-all-motes repo-path)
          mote-list (vals motes)
          total-motes (count mote-list)

          ;; Count root motes (depth 1)
          root-motes (count (filter #(= 1 (id/id-depth (:id %))) mote-list))

          ;; Count by status
          status-counts (frequencies (map :status mote-list))

          ;; Count by taint
          taint-counts (->> mote-list
                            (mapcat :taint)
                            frequencies)

          ;; Load active sessions
          active-sessions (session/load-all-active-sessions repo-path)

          ;; Count workable motes (using job/workable?)
          claim-timeout (:claim-timeout-minutes config)
          workable-count (count (filter #(job/workable? % :claim-timeout claim-timeout) mote-list))]

      {:project-name project-name
       :root-motes root-motes
       :total-motes total-motes
       :status-counts status-counts
       :taint-counts taint-counts
       :active-sessions (count active-sessions)
       :ready-for-work workable-count})))

;; -----------------------------------------------------------------------------
;; Handler Registration
;; -----------------------------------------------------------------------------

(defn register-handlers!
  "Register all command handlers with the CLI."
  []
  (cli/register-handler! "init" cmd-init!)
  (cli/register-handler! "show" cmd-show)
  (cli/register-handler! "create" cmd-create!)
  (cli/register-handler! "ready" cmd-ready)
  (cli/register-handler! "propose" cmd-propose!)
  (cli/register-handler! "approve" cmd-approve!)
  (cli/register-handler! "reject" cmd-reject!)
  (cli/register-handler! "update" cmd-update!)
  (cli/register-handler! "vote" cmd-vote!)
  (cli/register-handler! "taint" cmd-taint!)
  (cli/register-handler! "claim" cmd-claim!)
  (cli/register-handler! "unclaim" cmd-unclaim!)
  (cli/register-handler! "done" cmd-done!)
  (cli/register-handler! "add-ref" cmd-add-ref!)
  (cli/register-handler! "add-assumption" cmd-add-assumption!)
  (cli/register-handler! "add-definition" cmd-add-definition!)
  (cli/register-handler! "check" cmd-check)
  (cli/register-handler! "log" cmd-log)
  (cli/register-handler! "sync" cmd-sync!)
  (cli/register-handler! "config" cmd-config)
  (cli/register-handler! "tree" cmd-tree)
  (cli/register-handler! "status" cmd-status))

;; Auto-register handlers when namespace is loaded
(register-handlers!)
