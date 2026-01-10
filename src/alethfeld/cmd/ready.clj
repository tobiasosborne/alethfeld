(ns alethfeld.cmd.ready
  "Ready command implementation for job discovery and claiming."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.job :as job]
            [alethfeld.mote :as mote]
            [alethfeld.prompt :as prompt]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Stale Session Cleanup Helper
;; -----------------------------------------------------------------------------

(defn- cleanup-stale-sessions-and-claims!
  "Clean up stale sessions, associated mote claims, and expired reservations.

   Called at the start of cmd-ready to recover from crashed agents
   and remove expired reservations.

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of cleaned-up session info (or empty vector if none).

   Uses batch loading to avoid N+1 queries when cleaning up multiple motes."
  [repo-path]
  ;; Issue 4.3: Clean up expired reservations first
  (session/cleanup-expired-reservations! repo-path)

  (let [cleaned-up (session/cleanup-stale-sessions! repo-path)]
    (when (seq cleaned-up)
      ;; Clear mote claims for each cleaned-up session
      ;; Use batch loading to avoid N+1 queries
      (let [mote-ids (distinct (map :mote-id cleaned-up))
            motes-map (store/load-motes repo-path mote-ids)
            motes-to-update (keep (fn [mote-id]
                                    (when-let [m (get motes-map mote-id)]
                                      (when (:claimed-by m)
                                        (mote/clear-claim m))))
                                  mote-ids)]
        (when (seq motes-to-update)
          (tx/atomic-write! repo-path
                            (str "Cleanup stale sessions: "
                                 (str/join ", " (map :mote-id cleaned-up)))
                            (vec motes-to-update)))))
    cleaned-up))

(defn- claim-job-atomic!
  "Atomically claim a mote for an agent with race condition protection.

   Uses tx/atomic-update! to re-check claim status inside the repository lock,
   preventing TOCTOU race conditions where two agents try to claim the same mote.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: ID of the mote to claim
   - agent: Agent identifier string
   - claim-timeout: Optional claim timeout in minutes

   Returns the result map from tx/atomic-update! containing :result with updated mote.

   Throws ExceptionInfo with :type :already-claimed if:
   - The mote is already claimed by a different agent
   - The claim has not expired"
  [repo-path mote-id agent claim-timeout]
  (tx/atomic-update!
   repo-path
   (str "Claim mote " mote-id " for " agent)
   mote-id
   (fn [current-mote]
     (let [current-claimer (:claimed-by current-mote)
           claim-expired? (and current-claimer
                               claim-timeout
                               (mote/claim-expired? current-mote claim-timeout))]
       (cond
         ;; No current claim or claim has expired - proceed with claim
         (or (nil? current-claimer) claim-expired?)
         (mote/set-claimed-by current-mote agent)

         ;; Same agent already has claim - idempotent success
         (= current-claimer agent)
         current-mote

         ;; Different agent has active claim - reject
         :else
         (throw (ex-info "Mote already claimed by another agent"
                         {:type :already-claimed
                          :mote-id mote-id
                          :claimed-by current-claimer
                          :requested-by agent})))))
   :validate false))

;; -----------------------------------------------------------------------------
;; Ready Command Parsing
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

;; -----------------------------------------------------------------------------
;; Ready Command Output Formatting
;; -----------------------------------------------------------------------------

(defn- pad-right
  "Pad string s to width n with spaces on the right."
  [s n]
  (let [s (str s)]
    (if (>= (count s) n)
      s
      (str s (apply str (repeat (- n (count s)) " "))))))

(defn- format-box-line
  "Create a horizontal box line of given width with corners."
  [width left-corner right-corner fill-char]
  (str left-corner (apply str (repeat (- width 2) fill-char)) right-corner))

(defn- format-box-content
  "Format a line of content within the box."
  [content width]
  (let [padding (- width 4 (count content))]
    (str "|  " content (apply str (repeat (max 0 padding) " ")) " |")))

(def ^:private box-width 80)

(defn- format-job-claimed-header
  "Format the prominent header when a job is claimed.

   Returns a vector of strings (lines) for the header box."
  [job]
  (let [mote-id (:mote-id job)
        role (name (:role job))
        session-id (or (:session-id job) "N/A")
        priority (name (:priority job))
        difficulty (:difficulty job)
        title (str "JOB CLAIMED: " role " on mote " mote-id)]
    [(format-box-line box-width "+" "+" "=")
     (format-box-content title box-width)
     (format-box-line box-width "+" "+" "-")
     (format-box-content (str "Session: " session-id) box-width)
     (format-box-content (str "Role: " role) box-width)
     (format-box-content (str "Priority: " priority " | Difficulty: " difficulty) box-width)
     (format-box-line box-width "+" "+" "=")]))

(defn- format-job-commands
  "Format the commands section for a claimed job.

   Returns a vector of strings (lines)."
  [job]
  (let [mote-id (:mote-id job)
        session-id (or (:session-id job) "SESSION")
        role (:role job)]
    (case role
      :verifier
      ["COMMANDS YOU CAN USE:"
       (str "  af vote " mote-id " --for --session " session-id " --reason \"...\"")
       (str "  af vote " mote-id " --against --session " session-id " --reason \"...\"")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      :advisor
      ["COMMANDS YOU CAN USE:"
       (str "  af approve " mote-id " --session " session-id " --reason \"...\"")
       (str "  af reject " mote-id " --session " session-id " --reason \"...\"")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      :proposer
      ["COMMANDS YOU CAN USE:"
       (str "  af propose " mote-id " --session " session-id " --claim \"substep 1\" --claim \"substep 2\"")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      :prover
      ["COMMANDS YOU CAN USE:"
       (str "  af add-ref " mote-id " --session " session-id " --ref \"citation\" --note \"...\"")
       (str "  af add-assumption " mote-id " --session " session-id " --ref <mote-id> --note \"...\"")
       (str "  af add-definition " mote-id " --session " session-id " --symbol \"x\" --meaning \"...\"")
       (str "  af taint " mote-id " --session " session-id " --remove needs-refinement")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      :ref-checker
      ["COMMANDS YOU CAN USE:"
       (str "  af add-ref " mote-id " --session " session-id " --ref \"corrected citation\" --note \"...\"")
       (str "  af taint " mote-id " --session " session-id " --remove needs-refs")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      :counterexample
      ["COMMANDS YOU CAN USE:"
       (str "  af vote " mote-id " --for --session " session-id " --reason \"No counterexample found\"")
       (str "  af vote " mote-id " --against --session " session-id " --reason \"Counterexample: ...\"")
       (str "  af taint " mote-id " --session " session-id " --remove needs-counterexample")
       ""
       "WHEN FINISHED:"
       (str "  af done --session " session-id)]

      ;; Default case
      ["WHEN FINISHED:"
       (str "  af done --session " session-id)])))

(defn- format-claimed-job-output
  "Format the complete output for a claimed job, including header, prompt, and commands.

   Returns a string with the full formatted output."
  [job]
  (let [header-lines (format-job-claimed-header job)
        prompt (:prompt job)
        command-lines (format-job-commands job)]
    (str/join "\n"
              (concat header-lines
                      [""]
                      [prompt]
                      [""]
                      command-lines))))

(defn- format-job-list-item
  "Format a single job for the list view.

   Arguments:
   - idx: 1-based index of the job
   - job: The job map

   Returns a formatted string for this job."
  [idx job]
  (let [mote-id (:mote-id job)
        role (name (:role job))
        priority (name (:priority job))
        difficulty (:difficulty job)
        claim (get-in job [:mote :claim] "")]
    (str "  " idx ". mote " mote-id " | role: " role " | " priority " | difficulty: " difficulty
         (when (seq claim)
           (str "\n     " (if (> (count claim) 60)
                           (str (subs claim 0 57) "...")
                           claim))))))

(defn- format-job-list
  "Format the list of available jobs for display.

   Arguments:
   - jobs: Vector of job maps

   Returns a string with the formatted job list."
  [jobs]
  (if (empty? jobs)
    (str "No jobs available.\n\n"
         "All motes are either:\n"
         "  - Already claimed by another agent\n"
         "  - In a terminal state (verified, rejected, refuted)\n"
         "  - Not in need of work (no taints)\n")
    (str "Available jobs:\n"
         (str/join "\n\n" (map-indexed (fn [i j] (format-job-list-item (inc i) j)) jobs))
         "\n\n"
         "Claim a job:\n"
         "  af ready --agent <name> --job 1    # Claim job #1\n"
         "  af ready --agent <name>            # Claim highest priority")))

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

;; -----------------------------------------------------------------------------
;; Job Preparation
;; -----------------------------------------------------------------------------

(defn- prepare-jobs
  "Load and prepare jobs with filters and prompts.

   Arguments:
   - repo-path: Path to the repository root
   - opts: Map containing:
     - :role - Optional role filter
     - :difficulty - Optional difficulty filter string
     - :priority - Optional priority filter string
     - :mote - Optional specific mote ID filter
     - :max-jobs - Maximum jobs to fetch
     - :list-mode? - Whether in list mode (fetches more for display)
     - :job - Specific job number (1-indexed)

   Returns a map with:
   - :config - Repository config
   - :motes - All loaded motes
   - :jobs - Vector of jobs with prompts attached
   - :claim-timeout - Claim timeout from config"
  [repo-path {:keys [role difficulty priority mote max-jobs list-mode? job]}]
  (let [;; Parse difficulty/priority specs
        difficulty-filter (parse-difficulty-spec difficulty)
        priority-filter (parse-priority-spec priority)

        ;; Load config and motes
        config (store/load-config repo-path)
        claim-timeout (:claim-timeout-minutes config)
        motes (store/load-all-motes repo-path)

        ;; Load active reservations and build exclusion set
        active-reservations (session/list-active-reservations repo-path)
        reserved-mote-ids (into #{} (map :mote-id active-reservations))

        ;; For list mode or when --job is specified, get more jobs
        jobs-to-fetch (if (or list-mode? job)
                        (clojure.core/max max-jobs 10)
                        max-jobs)

        ;; Select jobs (with claim timeout enforcement and reservation filtering)
        jobs (job/select-jobs motes
                              :role role
                              :difficulty difficulty-filter
                              :priority priority-filter
                              :mote-id mote
                              :max jobs-to-fetch
                              :claim-timeout claim-timeout
                              :active-reservations reserved-mote-ids)

        ;; Enrich jobs with prompts
        jobs-with-prompts (mapv (fn [j]
                                  (let [resolved-children (resolve-children (:mote j) motes)
                                        rendered-prompt (prompt/render-prompt j :resolved-children resolved-children)]
                                    (assoc j :prompt rendered-prompt)))
                                jobs)]
    {:config config
     :motes motes
     :jobs jobs-with-prompts
     :claim-timeout claim-timeout}))

;; -----------------------------------------------------------------------------
;; Mode Handlers
;; -----------------------------------------------------------------------------

(defn- handle-claim-reservation
  "Handle --claim-reservation mode: claim a previously reserved job.

   Arguments:
   - repo-path: Path to the repository root
   - token: Reservation token to claim
   - agent: Agent name claiming the reservation
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :claimed"
  [repo-path token agent role-hint]
  (let [config (store/load-config repo-path)
        session-timeout (or (:session-timeout-minutes config) 30)
        sess (session/claim-reservation! repo-path token agent
                                         :duration-minutes session-timeout)
        mote-id (:mote-id sess)
        mote (store/load-mote repo-path mote-id)
        job-role (:role sess)
        ;; Update mote with claim
        updated-mote (mote/set-claimed-by mote agent)
        motes (store/load-all-motes repo-path)
        resolved-children (resolve-children mote motes)
        session-prompt (prompt/render-prompt {:role job-role :mote mote}
                                             :resolved-children resolved-children
                                             :session sess)]
    ;; Save the claimed mote
    (tx/atomic-write! repo-path (str "Claim reserved job for " agent ": " mote-id)
                      [updated-mote] :validate false)
    {:mode :claimed
     :jobs [{:mote-id mote-id
             :mote updated-mote
             :role job-role
             :claimed-by agent
             :session-id (:session-id sess)
             :session sess
             :prompt session-prompt}]
     :output (str role-hint
                  "Claimed reserved job: " mote-id "\n"
                  "Role: " (name job-role) "\n"
                  "Session: " (:session-id sess) "\n\n"
                  session-prompt)
     :next-actions [(core/done-action (:session-id sess))]}))

(defn- handle-reserve-mode
  "Handle --reserve mode: create a reservation without claiming.

   Arguments:
   - repo-path: Path to the repository root
   - jobs: Vector of available jobs with prompts
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :reserved or :mode :no-jobs"
  [repo-path jobs role-hint]
  (if (empty? jobs)
    {:mode :no-jobs
     :jobs []
     :output (str role-hint
                  "No jobs available to reserve.\n"
                  "Run 'af ready' to see current state.")
     :next-actions [(core/status-action)]}
    (let [first-job (first jobs)
          mote-id (:mote-id first-job)
          job-role (:role first-job)
          reservation (session/create-reservation! repo-path mote-id job-role)]
      {:mode :reserved
       :reservation reservation
       :jobs [first-job]
       :output (str role-hint
                    "Reserved: " mote-id " for " (name job-role) "\n"
                    "Token: " (:token reservation) "\n"
                    "Expires in 60 seconds\n\n"
                    "Claim with:\n"
                    "  af ready --name <your-name> --claim-reservation " (:token reservation))
       :next-actions [(core/make-action (str "af ready --name <name> --claim-reservation " (:token reservation))
                                        "Claim this reservation")]})))

(defn- handle-list-mode
  "Handle list mode: show available jobs without claiming.

   Arguments:
   - jobs: Vector of available jobs with prompts
   - motes: Map of all motes (for empty-check)
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :list"
  [jobs motes role-hint]
  {:mode :list
   :jobs jobs
   :output (str role-hint
                (cond
                  ;; No motes at all - guide to create first
                  (empty? motes)
                  (str "No motes yet. Create your first proof goal:\n\n"
                       "  af create --root --claim \"Your main theorem\"\n\n"
                       "Then run 'af ready' again to start working.")
                  ;; Has motes but no jobs
                  :else
                  (format-job-list jobs)))
   :next-actions (cond
                   (empty? motes)
                   [(core/make-action "af create --root --claim \"...\"" "Create first proof goal")]
                   (empty? jobs)
                   [(core/status-action)]
                   :else
                   [(core/make-action "af ready --agent <name>" "Claim highest priority job")
                    (core/make-action "af ready --agent <name> --job 1" "Claim specific job")
                    (core/status-action)])})

(defn- handle-preview-mode
  "Handle preview mode: agent provided but --no-claim.

   Arguments:
   - jobs: Vector of available jobs with prompts
   - agent: Agent name
   - job-num: Optional specific job number (1-indexed)
   - max-jobs: Maximum jobs to show
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :preview"
  [jobs agent job-num max-jobs role-hint]
  (let [selected-jobs (if job-num
                        ;; Select specific job by number (1-indexed)
                        (let [job-idx (dec job-num)]
                          (if (and (>= job-idx 0) (< job-idx (count jobs)))
                            [(nth jobs job-idx)]
                            []))
                        ;; Take first max-jobs
                        (take max-jobs jobs))]
    {:mode :preview
     :jobs (vec selected-jobs)
     :output (str role-hint
                  (if (empty? selected-jobs)
                    (if job-num
                      (str "Job #" job-num " not found. Run 'af ready' to see available jobs.")
                      "No jobs available matching your criteria.")
                    (format-job-list selected-jobs)))
     :next-actions [(core/make-action (str "af ready --agent " agent) "Claim this job")
                    (core/status-action)]}))

(defn- try-claim-jobs
  "Attempt to claim jobs atomically with race condition handling.

   Tries each candidate job in order. On :already-claimed, skips to next.
   Creates sessions for successfully claimed jobs.

   Arguments:
   - repo-path: Path to the repository root
   - candidates: Vector of job candidates to try
   - agent: Agent name claiming the jobs
   - motes: Map of all motes (for resolving children)
   - config: Repository config
   - max-jobs: Maximum number of jobs to claim

   Returns a vector of successfully claimed jobs with session info."
  [repo-path candidates agent motes config max-jobs]
  (let [session-timeout (or (:session-timeout-minutes config) 30)
        claim-timeout (:claim-timeout-minutes config)]
    (loop [remaining candidates
           claimed []]
      (if (or (empty? remaining)
              (>= (count claimed) max-jobs))
        claimed
        (let [j (first remaining)
              mote-id (:mote-id j)
              claim-result (try
                             ;; Atomic claim with race protection
                             (let [result (claim-job-atomic! repo-path mote-id agent claim-timeout)]
                               {:success true :mote (:result result)})
                             (catch clojure.lang.ExceptionInfo e
                               (if (= :already-claimed (:type (ex-data e)))
                                 {:success false :reason :already-claimed}
                                 (throw e))))]
          (if (:success claim-result)
            ;; Create session AFTER successful atomic claim
            (let [updated-mote (:mote claim-result)
                  _ (session/ensure-session-dirs! repo-path)
                  job-role (:role j)
                  sess (session/create-session! repo-path
                                                mote-id
                                                job-role
                                                agent
                                                :duration-minutes session-timeout)
                  ;; Re-render prompt with session context
                  resolved-children (resolve-children updated-mote motes)
                  session-prompt (prompt/render-prompt j
                                                       :resolved-children resolved-children
                                                       :session sess)]
              (recur (rest remaining)
                     (conj claimed
                           (assoc j
                                  :mote updated-mote
                                  :claimed-by agent
                                  :session-id (:session-id sess)
                                  :session sess
                                  :prompt session-prompt))))
            ;; Claim failed (already claimed by another) - try next
            (recur (rest remaining) claimed)))))))

(defn- build-claim-result
  "Build the result map for successfully claimed jobs.

   Arguments:
   - claimed-jobs: Vector of successfully claimed jobs
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :claimed"
  [claimed-jobs role-hint]
  (let [first-job (first claimed-jobs)
        session-id (:session-id first-job)
        mote-id (:mote-id first-job)
        job-role (:role first-job)
        ;; Generate role-specific next actions
        role-actions (case job-role
                       :verifier [(core/vote-action mote-id session-id :for)
                                  (core/vote-action mote-id session-id :against)]
                       :advisor [(core/approve-action mote-id session-id)
                                 (core/reject-action mote-id session-id)]
                       :proposer [(core/make-action (str "af propose " mote-id " --session " session-id " --claim \"...\"")
                                                    "Submit decomposition proposal")]
                       :prover [(core/make-action (str "af add-ref " mote-id " --session " session-id " --ref \"...\"")
                                                  "Add external reference")]
                       :ref-checker [(core/make-action (str "af add-ref " mote-id " --session " session-id " --ref \"...\"")
                                                       "Add/update references")]
                       :counterexample [(core/vote-action mote-id session-id :for)
                                        (core/vote-action mote-id session-id :against)]
                       [])]
    {:mode :claimed
     :jobs claimed-jobs
     :output (str role-hint (str/join "\n\n" (map format-claimed-job-output claimed-jobs)))
     :next-actions (conj (vec role-actions) (core/done-action session-id))}))

(defn- select-job-candidates
  "Select job candidates based on job number or take first max-jobs.

   Arguments:
   - jobs: Vector of available jobs
   - job-num: Optional specific job number (1-indexed)
   - max-jobs: Maximum jobs to consider

   Returns a vector of job candidates, or throws if job number is invalid."
  [jobs job-num max-jobs]
  (if job-num
    ;; Claim specific job by number (1-indexed)
    (let [job-idx (dec job-num)]
      (if (and (>= job-idx 0) (< job-idx (count jobs)))
        [(nth jobs job-idx)]
        (throw (ex-info (str "Job #" job-num " not found")
                        {:type :not-found
                         :job-number job-num
                         :available-count (count jobs)}))))
    ;; Take first max-jobs as candidates
    (vec (take max-jobs jobs))))

(defn- handle-claim-mode
  "Handle claim mode: agent provided, claim the job(s).

   Arguments:
   - repo-path: Path to the repository root
   - jobs: Vector of available jobs with prompts
   - agent: Agent name
   - job-num: Optional specific job number (1-indexed)
   - max-jobs: Maximum jobs to claim
   - motes: Map of all motes
   - config: Repository config
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :claimed or :mode :no-jobs"
  [repo-path jobs agent job-num max-jobs motes config role-hint]
  (let [candidates (select-job-candidates jobs job-num max-jobs)
        claimed-jobs (try-claim-jobs repo-path candidates agent motes config max-jobs)]
    (if (empty? claimed-jobs)
      ;; All candidates were claimed by others
      {:mode :no-jobs
       :jobs []
       :output (str role-hint
                    "All candidate jobs were claimed by other agents.\n"
                    "Run 'af ready' to see currently available jobs.")
       :next-actions [(core/make-action "af ready" "See available jobs")
                      (core/status-action)]}
      ;; Return with formatted output
      (build-claim-result claimed-jobs role-hint))))

(defn- build-no-jobs-result
  "Build the result map when no jobs are available.

   Arguments:
   - motes: Map of all motes (for empty-check)
   - mote-filter: Optional specific mote ID that was requested
   - agent: Agent name (or nil)
   - role-hint: Optional hint about role name confusion

   Returns a result map with :mode :no-jobs"
  [motes mote-filter agent role-hint]
  {:mode :no-jobs
   :jobs []
   :output (str role-hint
                (cond
                  ;; Specific mote requested but not available
                  mote-filter
                  (str "Mote " mote-filter " is not available.\n\n"
                       "Possible reasons:\n"
                       "  - Mote doesn't exist\n"
                       "  - Already claimed by another agent\n"
                       "  - In a terminal state (verified, rejected, refuted)\n"
                       "  - No work needed (no taints)\n"
                       "\n"
                       "Run 'af show " mote-filter "' to inspect the mote.\n"
                       "Run 'af ready --name " (or agent "<name>") "' for available motes.")

                  ;; No motes exist at all - guide to create first mote
                  (empty? motes)
                  (str "No motes yet. Create your first proof goal:\n\n"
                       "  af create --root --claim \"Your main theorem\"\n\n"
                       "Then run 'af ready' again to start working.")

                  ;; Motes exist but none available
                  :else
                  (str "No jobs available.\n\n"
                       "All motes are either:\n"
                       "  - Already claimed by another agent\n"
                       "  - In a terminal state (verified, rejected, refuted)\n"
                       "  - Not in need of work (no taints)\n"
                       "\n"
                       "Run 'af status' to see project overview.")))
   :next-actions [(if (empty? motes)
                    (core/make-action "af create --root --claim \"...\"" "Create first proof goal")
                    (core/status-action))]})

;; -----------------------------------------------------------------------------
;; Ready Command
;; -----------------------------------------------------------------------------

(defn cmd-ready
  "Get next job(s) for an agent.

   Modes:
   1. List mode (no --name): Shows available jobs numbered, no claiming
   2. Claim mode (--name NAME): Claims highest priority job (or specific with --job)
   3. Preview mode (--name NAME --no-claim): Like claim mode but doesn't claim
   4. Reserve mode (--reserve): Create a reservation without claiming (for orchestrators)
   5. Claim-reservation mode (--claim-reservation TOKEN): Claim a previously reserved job

   Options:
   - :name - Agent name (auto-claims jobs unless --no-claim)
   - :role - Filter by role (:proposer, :advisor, :prover, :verifier, :ref-checker, :counterexample)
   - :difficulty - Difficulty filter (\"N\" for exact, \"N-M\" for range)
   - :priority - Priority filter (\"pN\" for exact, \"pN-pM\" for range)
   - :max - Maximum jobs to return (default: 10 for list mode, 1 for claim mode)
   - :no-claim - Don't auto-claim jobs
   - :job - Specific job number to claim (1-indexed, from list mode output)
   - :reserve - Create a reservation instead of claiming (expires in 60s)
   - :claim-reservation - Token from a previous --reserve call

   Returns:
   - In list mode: A map with :mode :list and :output (formatted string)
   - In claim mode: A map with :mode :claimed and :output (formatted string with prompt)
   - In reserve mode: A map with :mode :reserved and :reservation (with :token)
   - In claim-reservation mode: A map with :mode :claimed (like normal claim)

   Note: Automatically cleans up stale sessions (expired or crashed)
   before selecting jobs."
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [name role difficulty priority mote max no-claim job reserve claim-reservation]} options
        agent name  ;; Renamed from --agent to --name, but keep 'agent' var for session compat
        ;; Check if --name looks like a role name (common mistake)
        role-hint (when-let [matched-role (core/name-looks-like-role? name)]
                    (core/format-role-hint matched-role))
        ;; Default max depends on mode: list mode shows more, claim mode shows 1
        list-mode? (nil? agent)
        max-jobs (or max (if list-mode? 10 1))]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Handle --claim-reservation mode first (claims existing reservation)
    (if claim-reservation
      (do
        (when-not agent
          (throw (ex-info "Must provide --name when claiming a reservation"
                          {:type :validation-error
                           :message "Use: af ready --name <your-name> --claim-reservation TOKEN"})))
        (handle-claim-reservation repo-path claim-reservation agent role-hint))

      ;; Normal flow (no claim-reservation)
      (do
        ;; Clean up stale sessions (expired or crashed agents)
        (cleanup-stale-sessions-and-claims! repo-path)

        ;; Prepare jobs with filters and prompts
        (let [{:keys [config motes jobs claim-timeout]}
              (prepare-jobs repo-path {:role role
                                       :difficulty difficulty
                                       :priority priority
                                       :mote mote
                                       :max-jobs max-jobs
                                       :list-mode? list-mode?
                                       :job job})]
          (cond
            ;; Reserve mode: create reservation without claiming (for orchestrators)
            reserve
            (handle-reserve-mode repo-path jobs role-hint)

            ;; List mode: no agent provided - show numbered list
            list-mode?
            (handle-list-mode jobs motes role-hint)

            ;; Preview mode: agent provided but --no-claim
            no-claim
            (handle-preview-mode jobs agent job max-jobs role-hint)

            ;; Claim mode: agent provided, claim the job(s)
            (seq jobs)
            (handle-claim-mode repo-path jobs agent job max-jobs motes config role-hint)

            ;; No jobs available when trying to claim
            :else
            (build-no-jobs-result motes mote agent role-hint)))))))
