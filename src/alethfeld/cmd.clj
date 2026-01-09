(ns alethfeld.cmd
  "CLI command implementations.

   Each command function follows the pattern:
   - Takes a context map with :id, :args, :options
   - Returns data to be formatted and output
   - Throws ExceptionInfo for errors

   All commands return a :next-actions key with suggested next steps:
   [{:command \"af ...\" :description \"...\"}]"
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
            [alethfeld.repair :as repair]
            [alethfeld.session :as session]
            [alethfeld.verify :as verify]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Next Actions Helpers
;; -----------------------------------------------------------------------------

(defn- make-action
  "Create a next-action map."
  [command description]
  {:command command :description description})

(defn- done-action
  "Create the standard 'af done' action for a session."
  [session-id]
  (make-action (str "af done --session " session-id)
               "End session (work complete)"))

(defn- show-action
  "Create an 'af show' action for a mote."
  [mote-id]
  (make-action (str "af show " mote-id)
               "View mote details"))

(defn- tree-action
  "Create an 'af tree' action for a mote."
  [mote-id]
  (make-action (str "af tree " mote-id)
               "View proof structure"))

(defn- status-action
  "Create an 'af status' action."
  []
  (make-action "af status" "View project overview"))

(defn- ready-action
  "Create an 'af ready' action for starting work."
  []
  (make-action "af ready --agent <name>" "Get assigned a task"))

(defn- vote-action
  "Create a vote action for a mote."
  [mote-id session-id direction]
  (let [flag (if (= direction :for) "--for" "--against")]
    (make-action (str "af vote " mote-id " " flag " --session " session-id " --reason \"...\"")
                 (if (= direction :for) "Vote claim is valid" "Vote claim is invalid"))))

(defn- approve-action
  "Create an approve action for a proposal."
  [mote-id session-id]
  (make-action (str "af approve " mote-id " --session " session-id)
               "Approve the proposal"))

(defn- reject-action
  "Create a reject action for a proposal."
  [mote-id session-id]
  (make-action (str "af reject " mote-id " --session " session-id)
               "Reject the proposal"))

(defn- find-votable-siblings
  "Find siblings of a mote that need verification and the agent can vote on.

   Returns a vector of mote IDs."
  [repo-path mote-id agent]
  (when-let [parent-id (id/parent-id mote-id)]
    (when-let [parent (store/load-mote repo-path parent-id)]
      (let [sibling-ids (remove #{mote-id} (:children parent))
            motes (store/load-all-motes repo-path)]
        (->> sibling-ids
             (filter (fn [sib-id]
                       (when-let [sib (get motes sib-id)]
                         (and (verify/needs-verification? sib)
                              (session/can-vote? sib agent)
                              (not (verify/has-voted? sib agent))))))
             vec)))))

(defn- generate-vote-next-actions
  "Generate intelligent next-actions after a vote based on current state.

   Logic from AGENT-UX-PLAN.md Section 3.2:
   - If quorum not reached: 'Waiting for N more votes'
   - If quorum reached and more siblings need voting: 'Continue: af vote 1.2'
   - If all siblings done or no siblings: 'af done'"
  [repo-path mote-id session-id agent quorum-status]
  (let [;; Check for votable siblings
        votable-siblings (find-votable-siblings repo-path mote-id agent)]
    (cond
      ;; Quorum not yet reached - suggest waiting or done
      (= :pending quorum-status)
      [(make-action "# Waiting for more votes" "Other verifiers need to vote")
       (done-action session-id)]

      ;; Quorum reached, but there are more siblings to vote on
      (seq votable-siblings)
      (let [next-sibling (first votable-siblings)]
        [(vote-action next-sibling session-id :for)
         (vote-action next-sibling session-id :against)
         (done-action session-id)])

      ;; All done - suggest ending session
      :else
      [(done-action session-id)])))

;; -----------------------------------------------------------------------------
;; Dry Run Helpers
;; -----------------------------------------------------------------------------

(defn- format-dry-run-header
  "Format the dry-run header banner."
  []
  "DRY RUN - No changes made\n")

(defn- format-dry-run-footer
  "Format the dry-run footer with execution hint."
  []
  "\nRun without --dry-run to execute.")

(defn- format-would-create
  "Format a 'would create' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould create:\n"
         (str/join "\n"
                   (for [item items]
                     (if (map? item)
                       (str "  " (:id item) " [" (name (:status item :proposed)) "] " (:claim item))
                       (str "  " item)))))))

(defn- format-would-update
  "Format a 'would update' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould update:\n"
         (str/join "\n"
                   (for [item items]
                     (if (map? item)
                       (str "  " (:id item) " -> " (:change item))
                       (str "  " item)))))))

(defn- format-would-delete
  "Format a 'would delete' section for dry-run output."
  [items]
  (when (seq items)
    (str "\nWould delete/archive:\n"
         (str/join "\n"
                   (for [item items]
                     (str "  " item))))))

(defn- dry-run-result
  "Create a standard dry-run result map.

   Arguments:
   - output: The formatted dry-run output string
   - would-create: Vector of items that would be created
   - would-update: Vector of items that would be updated
   - would-delete: Vector of items that would be deleted

   Returns a map suitable for dry-run command results."
  [& {:keys [output would-create would-update would-delete next-actions]}]
  {:dry-run true
   :output (str (format-dry-run-header)
                output
                (format-dry-run-footer))
   :would-create (vec would-create)
   :would-update (vec would-update)
   :would-delete (vec would-delete)
   :next-actions (or next-actions [(status-action)])})

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
   - :dry-run - Show what would be created without executing

   Returns the config that was created."
  [{:keys [options]}]
  (let [repo-path "."
        project-name (:name options "Alethfeld Project")
        dry-run? (:dry-run options)]

    ;; Check if already initialized
    (when (store/repo-exists? repo-path)
      (throw (ex-info "Repository already initialized"
                      {:type :already-initialized
                       :path repo-path})))

    (if dry-run?
      ;; Dry run - show what would be created
      (dry-run-result
       :output (str "Would initialize Alethfeld repository: " project-name
                    (format-would-create
                     [".alethfeld/config.edn"
                      ".alethfeld/motes/"
                      ".alethfeld/proposed/"
                      ".alethfeld/archive/"
                      ".alethfeld/sessions/active/"
                      ".alethfeld/sessions/completed/"])
                    "\n\nWould create git commit: \"Initialize Alethfeld: " project-name "\"")
       :would-create [".alethfeld/"])
      ;; Execute
      (do
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
           :config config
           :next-actions [(make-action "af create --root --claim \"Your main theorem\""
                                       "Create your first proof goal")
                          (status-action)]})))))

;; -----------------------------------------------------------------------------
;; Show Command
;; -----------------------------------------------------------------------------

(defn- format-show-concise
  "Format concise mote display (default).

   Returns a human-readable summary string."
  [mote]
  (let [status (name (:status mote))
        taints (when (seq (:taint mote))
                 (str " (" (str/join ", " (map name (:taint mote))) ")"))
        claim (:claim mote)]
    (str (:id mote) " [" status "]" taints "\n"
         claim)))

(defn- format-show-verbose
  "Format verbose mote display (with --verbose flag).

   Returns a detailed human-readable string."
  [mote]
  (let [sep (apply str (repeat 40 "-"))]
    (str sep "\n"
         "Mote: " (:id mote) "\n"
         sep "\n"
         "Status: " (name (:status mote)) "\n"
         "Claim: " (:claim mote) "\n"
         "Priority: " (name (:priority mote)) "\n"
         "Difficulty: " (:difficulty mote) "\n"
         (when (seq (:taint mote))
           (str "Taints: " (str/join ", " (map name (:taint mote))) "\n"))
         (when (:claimed-by mote)
           (str "Claimed by: " (:claimed-by mote) "\n"))
         (when (seq (:children mote))
           (str "Children: " (str/join ", " (:children mote)) "\n"))
         (when (:parent mote)
           (str "Parent: " (:parent mote) "\n"))
         (when-let [proposal (:proposal mote)]
           (str "\nProposal:\n"
                "  Proposer: " (:proposer proposal) "\n"
                "  Children: " (str/join ", " (:children proposal)) "\n"
                (when (seq (:votes proposal))
                  (str "  Votes: " (count (:votes proposal)) "\n"))))
         (when (seq (:votes mote))
           (str "\nVotes: " (count (:votes mote))
                " (for: " (count (filter #(= :for (:type %)) (:votes mote)))
                ", against: " (count (filter #(= :against (:type %)) (:votes mote))) ")\n"))
         (when (seq (:assumptions mote))
           (str "\nAssumptions: " (count (:assumptions mote)) "\n"))
         (when (seq (:definitions mote))
           (str "Definitions: " (count (:definitions mote)) "\n"))
         (when (seq (:depends-on mote))
           (str "Dependencies: " (str/join ", " (map :ref (:depends-on mote))) "\n"))
         "\nCreated: " (:created-at mote) " by " (:created-by mote))))

(defn cmd-show
  "Display a mote's details.

   Arguments (in context):
   - :id - The mote ID to display

   Options:
   - :verbose - Show detailed output (default: concise)

   Returns the mote map, or throws if not found."
  [{:keys [id options]}]
  (let [repo-path "."
        verbose? (:verbose options)
        mote (store/load-mote repo-path id)]
    (if mote
      (let [output (if verbose?
                     (format-show-verbose mote)
                     (format-show-concise mote))]
        (assoc mote
               :output output
               :verbose? verbose?
               :next-actions [(tree-action id)
                              (ready-action)
                              (status-action)]))
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
   - :dry-run - Show what would be created without executing

   For root motes:
   - Generates next available root ID (1, 2, 3, ...)

   For child motes:
   - Parent must exist
   - Generates next child ID based on parent's existing children
   - Inherits priority/difficulty from parent if not specified

   Returns the created mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim root difficulty priority name dry-run]} options
        agent (or name "cli-user")]

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
            eff-difficulty (or difficulty 3)
            eff-priority (or priority :p2)]
        (if dry-run
          ;; Dry run
          (dry-run-result
           :output (str (format-would-create
                         [{:id new-id :status :fixed :claim claim}])
                        "\n\nPriority: " (name eff-priority) ", Difficulty: " eff-difficulty)
           :would-create [{:id new-id :claim claim :status :fixed}])
          ;; Execute
          (let [new-mote (mote/make-root-mote new-id claim agent
                                              :difficulty eff-difficulty
                                              :priority eff-priority)
                _ (tx/atomic-write! repo-path
                                    (str "Create root mote " new-id)
                                    [new-mote])]
            (assoc new-mote :next-actions [(show-action new-id)
                                           (ready-action)
                                           (status-action)]))))

      ;; Create child mote
      (let [parent (store/load-mote repo-path id)]
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id id})))

        (let [existing-children (:children parent)
              new-id (id/next-child-id id existing-children)
              eff-difficulty (or difficulty (:difficulty parent))
              eff-priority (or priority (:priority parent))]
          (if dry-run
            ;; Dry run
            (dry-run-result
             :output (str (format-would-create
                           [{:id new-id :status :fixed :claim claim}])
                          (format-would-update
                           [{:id id :change (str "add child " new-id)}])
                          "\n\nPriority: " (name eff-priority) ", Difficulty: " eff-difficulty)
             :would-create [{:id new-id :claim claim :status :fixed}]
             :would-update [{:id id :change (str "add child " new-id)}])
            ;; Execute
            (let [new-mote (mote/make-child-mote new-id claim agent parent
                                                 :difficulty eff-difficulty
                                                 :priority eff-priority)
                  updated-parent (mote/add-child parent new-id)
                  _ (tx/atomic-write! repo-path
                                      (str "Create child mote " new-id)
                                      [new-mote updated-parent])]
              (assoc new-mote :next-actions [(show-action new-id)
                                             (tree-action id)
                                             (ready-action)]))))))))

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

(defn cmd-ready
  "Get next job(s) for an agent.

   Modes:
   1. List mode (no --agent): Shows available jobs numbered, no claiming
   2. Claim mode (--agent NAME): Claims highest priority job (or specific with --job)
   3. Preview mode (--agent NAME --no-claim): Like claim mode but doesn't claim

   Options:
   - :agent - Agent name (auto-claims jobs unless --no-claim)
   - :role - Filter by role (:proposer, :advisor, :prover, :verifier, :ref-checker, :counterexample)
   - :difficulty - Difficulty filter (\"N\" for exact, \"N-M\" for range)
   - :priority - Priority filter (\"pN\" for exact, \"pN-pM\" for range)
   - :max - Maximum jobs to return (default: 10 for list mode, 1 for claim mode)
   - :no-claim - Don't auto-claim jobs
   - :job - Specific job number to claim (1-indexed, from list mode output)

   Returns:
   - In list mode: A map with :mode :list and :output (formatted string)
   - In claim mode: A map with :mode :claimed and :output (formatted string with prompt)
     plus the full job data

   Note: Automatically cleans up stale sessions (expired or crashed)
   before selecting jobs."
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [name role difficulty priority max no-claim job]} options
        agent name  ;; Renamed from --agent to --name, but keep 'agent' var for session compat
        ;; Default max depends on mode: list mode shows more, claim mode shows 1
        list-mode? (nil? agent)
        max-jobs (or max (if list-mode? 10 1))]

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
          ;; For list mode or when --job is specified, get more jobs
          jobs-to-fetch (if (or list-mode? job) (clojure.core/max max-jobs 10) max-jobs)
          jobs (job/select-jobs motes
                                :role role
                                :difficulty difficulty-filter
                                :priority priority-filter
                                :max jobs-to-fetch
                                :claim-timeout claim-timeout)

          ;; Enrich jobs with prompts
          jobs-with-prompts (mapv (fn [j]
                                    (let [resolved-children (resolve-children (:mote j) motes)
                                          rendered-prompt (prompt/render-prompt j :resolved-children resolved-children)]
                                      (assoc j :prompt rendered-prompt)))
                                  jobs)]

      (cond
        ;; List mode: no agent provided - show numbered list
        list-mode?
        {:mode :list
         :jobs jobs-with-prompts
         :output (format-job-list jobs-with-prompts)
         :next-actions (if (empty? jobs-with-prompts)
                         [(status-action)]
                         [(make-action "af ready --agent <name>" "Claim highest priority job")
                          (make-action "af ready --agent <name> --job 1" "Claim specific job")
                          (status-action)])}

        ;; Preview mode: agent provided but --no-claim
        no-claim
        (let [selected-jobs (if job
                              ;; Select specific job by number (1-indexed)
                              (let [job-idx (dec job)]
                                (if (and (>= job-idx 0) (< job-idx (count jobs-with-prompts)))
                                  [(nth jobs-with-prompts job-idx)]
                                  []))
                              ;; Take first max-jobs
                              (take max-jobs jobs-with-prompts))]
          {:mode :preview
           :jobs (vec selected-jobs)
           :output (if (empty? selected-jobs)
                     (if job
                       (str "Job #" job " not found. Run 'af ready' to see available jobs.")
                       "No jobs available matching your criteria.")
                     (format-job-list selected-jobs))
           :next-actions [(make-action (str "af ready --agent " agent) "Claim this job")
                          (status-action)]})

        ;; Claim mode: agent provided, claim the job(s)
        (seq jobs-with-prompts)
        (let [;; Select which jobs to claim
              jobs-to-claim (if job
                              ;; Claim specific job by number (1-indexed)
                              (let [job-idx (dec job)]
                                (if (and (>= job-idx 0) (< job-idx (count jobs-with-prompts)))
                                  [(nth jobs-with-prompts job-idx)]
                                  []))
                              ;; Take first max-jobs
                              (take max-jobs jobs-with-prompts))]
          (if (empty? jobs-to-claim)
            ;; Invalid job number
            (throw (ex-info (str "Job #" job " not found")
                            {:type :not-found
                             :job-number job
                             :available-count (count jobs-with-prompts)}))

            ;; Proceed with claiming
            (let [;; Ensure session directories exist
                  _ (session/ensure-session-dirs! repo-path)
                  ;; Get session timeout from config (default: 30 minutes)
                  session-timeout (or (:session-timeout-minutes config) 30)
                  ;; Update motes with claims and create sessions
                  claimed-jobs (mapv (fn [j]
                                       (let [;; Create session for this job
                                             job-role (:role j)
                                             sess (session/create-session! repo-path
                                                                           (:mote-id j)
                                                                           job-role
                                                                           agent
                                                                           :duration-minutes session-timeout)
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
                                     jobs-to-claim)
                  ;; Extract updated motes for atomic write
                  updated-motes (mapv :mote claimed-jobs)
                  ;; Commit all claims atomically via transaction layer
                  commit-msg (str "Claim jobs for " agent ": "
                                  (str/join ", " (map :mote-id claimed-jobs)))]
              (tx/atomic-write! repo-path commit-msg updated-motes :validate false)

              ;; Return with formatted output - generate intelligent next-actions
              (let [first-job (first claimed-jobs)
                    session-id (:session-id first-job)
                    mote-id (:mote-id first-job)
                    job-role (:role first-job)
                    ;; Generate role-specific next actions
                    role-actions (case job-role
                                   :verifier [(vote-action mote-id session-id :for)
                                              (vote-action mote-id session-id :against)]
                                   :advisor [(approve-action mote-id session-id)
                                             (reject-action mote-id session-id)]
                                   :proposer [(make-action (str "af propose " mote-id " --session " session-id " --claim \"...\"")
                                                           "Submit decomposition proposal")]
                                   :prover [(make-action (str "af add-ref " mote-id " --session " session-id " --ref \"...\"")
                                                         "Add external reference")]
                                   :ref-checker [(make-action (str "af add-ref " mote-id " --session " session-id " --ref \"...\"")
                                                              "Add/update references")]
                                   :counterexample [(vote-action mote-id session-id :for)
                                                    (vote-action mote-id session-id :against)]
                                   [])]
                {:mode :claimed
                 :jobs claimed-jobs
                 :output (str/join "\n\n" (map format-claimed-job-output claimed-jobs))
                 :next-actions (conj (vec role-actions) (done-action session-id))}))))

        ;; No jobs available when trying to claim
        :else
        {:mode :no-jobs
         :jobs []
         :output (str "No jobs available.\n\n"
                      "All motes are either:\n"
                      "  - Already claimed by another agent\n"
                      "  - In a terminal state (verified, rejected, refuted)\n"
                      "  - Not in need of work (no taints)\n"
                      "\n"
                      "Run 'af status' to see project overview.")
         :next-actions [(status-action)]}))))

;; -----------------------------------------------------------------------------
;; Propose Command
;; -----------------------------------------------------------------------------

(defn- parse-claims
  "Parse claims from command-line args.

   Each claim is a string. Can optionally include difficulty with @ notation
   and atomic marker with ! notation:
   'My claim @3' -> {:claim 'My claim' :difficulty 3}
   'My claim !' -> {:claim 'My claim' :atomic true}
   'My claim @3!' -> {:claim 'My claim' :difficulty 3 :atomic true}
   'My claim' -> {:claim 'My claim'}

   Returns vector of {:claim ... :difficulty ... :atomic ...} maps."
  [args]
  (mapv (fn [arg]
          (let [;; Check for trailing ! (atomic marker)
                [arg-without-atomic atomic?] (if (str/ends-with? arg "!")
                                               [(subs arg 0 (dec (count arg))) true]
                                               [arg false])
                ;; Check for @N difficulty notation
                [claim difficulty] (if-let [[_ c d] (re-matches #"(.+?)\s*@(\d+)\s*$" arg-without-atomic)]
                                     [(str/trim c) (Integer/parseInt d)]
                                     [arg-without-atomic nil])]
            (cond-> {:claim claim}
              difficulty (assoc :difficulty difficulty)
              atomic? (assoc :atomic true))))
        args))

(defn- merge-option-claims
  "Merge claims from --claim options with --difficulty and --atomic options.

   The --difficulty and --atomic options are positional and apply to claims
   in order. If there are fewer difficulty/atomic values than claims, the
   remaining claims inherit from parent (difficulty) or default to false (atomic).

   Arguments:
   - claim-texts: Vector of claim text strings from --claim options
   - difficulties: Vector of difficulty values from --difficulty options
   - atomics: Vector of booleans from --atomic options

   Returns vector of {:claim ... :difficulty ... :atomic ...} maps."
  [claim-texts difficulties atomics]
  (mapv (fn [idx claim-text]
          (let [difficulty (get difficulties idx)
                atomic? (get atomics idx)]
            (cond-> {:claim claim-text}
              difficulty (assoc :difficulty difficulty)
              atomic? (assoc :atomic true))))
        (range (count claim-texts))
        claim-texts))

(defn cmd-propose!
  "Create a proposal to decompose a mote into children.

   Arguments (in context):
   - :id - The parent mote ID (required)
   - :args - Child claims (required unless --claim used)
             Each claim can optionally include difficulty with @ notation:
             'My claim @3' sets difficulty to 3
             Add ! suffix to mark as atomic: 'My claim !' or 'My claim @3!'

   Options:
   - :session - Session token (required)
   - :claim - Claim text (repeatable, alternative to positional args)
   - :difficulty - Difficulty for claims (repeatable, positional)
   - :atomic - Mark claim as atomic (repeatable, positional)
   - :agent - Agent name (defaults to session agent)
   - :dry-run - Show what would be created without executing

   Creates proposed children with :proposed status and attaches
   a proposal to the parent. Sets parent taint to :needs-proposal-review.
   Atomic claims get :needs-verification taint instead of :needs-decomposition.

   Returns map with:
   - :proposal - The created proposal
   - :children - Vector of created child motes"
  [{:keys [id args options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID"]})))

    ;; Get claims from both args and --claim options
    (let [option-claims (:claim options)
          positional-claims args]
      (when (and (empty? positional-claims) (empty? option-claims))
        (throw (ex-info "At least one claim is required"
                        {:type :validation-failed
                         :errors ["Provide claims as arguments or with --claim"]})))

      ;; Check repository exists
      (when-not (store/repo-exists? repo-path)
        (throw (ex-info "Not an Alethfeld repository"
                        {:type :not-initialized
                         :path repo-path})))

      ;; Session enforcement (skip for dry-run)
      (when (and (not dry-run?) (not session-id))
        (throw (ex-info "Session token is required"
                        {:type :validation-failed
                         :errors ["Provide --session with session token"]})))

      ;; Parse positional claims (with @N and ! notation support)
      (let [parsed-positional (parse-claims positional-claims)
            ;; Parse option-based claims (merge with --difficulty and --atomic)
            parsed-options (when (seq option-claims)
                            (merge-option-claims option-claims
                                                 (:difficulty options)
                                                 (:atomic options)))
            ;; Combine claims (positional first, then options)
            claims (vec (concat parsed-positional parsed-options))]

        (if dry-run?
          ;; Dry run - show what would be created
          (let [parent (store/load-mote repo-path id)
                _ (when-not parent
                    (throw (ex-info "Parent mote not found"
                                    {:type :not-found
                                     :mote-id id})))
                existing-children (:children parent)
                ;; Calculate what IDs would be assigned
                child-infos (map-indexed
                             (fn [idx claim-info]
                               (let [child-id (id/next-child-id id (concat existing-children
                                                                            (map :id (take idx []))))]
                                 {:id (str id "." (+ 1 idx (count existing-children)))
                                  :status :proposed
                                  :claim (:claim claim-info)
                                  :atomic (:atomic claim-info)}))
                             claims)
                config (store/load-config repo-path)]
            (dry-run-result
             :output (str (format-would-create child-infos)
                          (format-would-update
                           [{:id id :change "set taint :needs-proposal-review"}])
                          "\n\nWould require " (:proposal-quorum config 2) " advisor votes to approve.")
             :would-create (vec child-infos)
             :would-update [{:id id :change "set taint :needs-proposal-review"}]
             :next-actions [(done-action (or session-id "<session>"))
                            (show-action id)]))

          ;; Execute
          (let [sess (session/enforce-session! repo-path session-id :propose id)
                agent (or (:name options) (:agent sess))
                result (proposal/create-proposal! repo-path id claims agent)
                proposal-result (:result result)
                child-count (count (:children proposal-result))]
            (assoc proposal-result
                   :next-actions [(done-action session-id)
                                  (show-action id)]
                   :message (str "Created proposal with " child-count " children. Waiting for advisor approval."))))))))

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
   - :dry-run - Show what would happen without executing

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
        reason (:reason options)
        dry-run? (:dry-run options)]

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

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run?
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            proposal (:proposal mote)
            _ (when-not proposal
                (throw (ex-info "No active proposal on this mote"
                                {:type :no-proposal
                                 :mote-id id})))
            config (store/load-config repo-path)
            current-approvals (count (filter #(= :approve (:type %)) (:votes proposal)))
            quorum (:proposal-quorum config 2)
            would-reach-quorum? (>= (inc current-approvals) quorum)]
        (dry-run-result
         :output (str "Would record approval vote on " id
                      "\n\nCurrent votes: " current-approvals "/" quorum " approvals"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached!"
                             (format-would-update
                              (mapv (fn [child-id] {:id child-id :change "promote to :fixed status"})
                                    (:children proposal)))
                             (format-would-update [{:id id :change "clear proposal, update children list"}]))
                        (str "\n\nQuorum not yet reached. " (- quorum (inc current-approvals)) " more votes needed.")))
         :would-update (if would-reach-quorum?
                         (conj (mapv (fn [child-id] {:id child-id :change "promote"})
                                     (:children proposal))
                               {:id id :change "clear proposal"})
                         [{:id id :change "add approval vote"}])
         :next-actions [(done-action (or session-id "<session>"))
                        (show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session-id :approve id)
            agent (or (:name options) (:agent sess))
            result (proposal/approve-proposal! repo-path id agent :reason reason)
            approve-result (:result result)
            quorum-status (:quorum-status approve-result)]
        (assoc approve-result
               :next-actions (if (= :approved quorum-status)
                               ;; Quorum reached - children promoted
                               [(done-action session-id)]
                               ;; Still pending - waiting for more votes
                               [(done-action session-id)
                                (show-action id)])
               :message (if (= :approved quorum-status)
                          "Proposal approved! Children promoted to fixed status."
                          "Vote recorded. Waiting for more advisor votes."))))))

;; -----------------------------------------------------------------------------
;; Approve-All Command
;; -----------------------------------------------------------------------------

(defn- find-motes-with-proposals
  "Find all motes that have pending proposals the agent can vote on."
  [repo-path agent]
  (let [all-motes (store/load-all-motes repo-path)]
    (->> all-motes
         (filter (fn [[_id mote]]
                   (when-let [prop (:proposal mote)]
                     (and (= :pending (:status prop))
                          (not (proposal/has-voted? prop agent))))))
         (sort-by first))))

(defn cmd-approve-all!
  "Approve all pending proposals in session scope.

   Options:
   - :session - Session token (required)
   - :name - Agent name (defaults to session agent)
   - :reason - Reason for all approvals (optional)
   - :dry-run - Show what would be approved without approving

   Finds all motes that have pending proposals that the agent can vote on
   (excluding those already voted on), then casts an approval vote on each.

   Returns map with:
   - :approved - Vector of mote IDs that were approved
   - :skipped - Vector of maps with :mote-id and :reason for skipped motes
   - :total-approved - Count of approvals cast
   - :total-skipped - Count of motes skipped
   - :dry-run - True if this was a dry run"
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [session reason dry-run]} options]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (but allow viewing dry-run without session)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [;; Get agent from session or options
          sess (when session
                 (session/load-session repo-path session))
          agent (or (:name options)
                    (:agent sess)
                    (when dry-run "dry-run-agent"))

          _ (when (and (not dry-run) (not agent))
              (throw (ex-info "Agent name is required"
                              {:type :validation-failed
                               :errors ["Provide --name or use a valid session"]})))

          ;; Find motes with pending proposals
          eligible (find-motes-with-proposals repo-path agent)
          eligible-ids (map first eligible)]

      (if dry-run
        ;; Dry run - just report what would be approved
        {:approved []
         :would-approve (vec eligible-ids)
         :total-would-approve (count eligible-ids)
         :dry-run true
         :output (str "Would approve " (count eligible-ids) " proposals: "
                      (str/join ", " eligible-ids))
         :next-actions [(make-action "af approve-all --session <session> --reason \"...\""
                                     "Execute batch approval")
                        (status-action)]}

        ;; Actually cast approvals
        (let [results (reduce
                       (fn [acc [mote-id _mote]]
                         (try
                           (proposal/approve-proposal! repo-path mote-id agent :reason reason)
                           (update acc :approved conj mote-id)
                           (catch Exception e
                             (update acc :skipped conj
                                     {:mote-id mote-id
                                      :reason (ex-message e)}))))
                       {:approved [] :skipped []}
                       eligible)]
          (assoc results
                 :total-approved (count (:approved results))
                 :total-skipped (count (:skipped results))
                 :dry-run false
                 :output (str "Approved " (count (:approved results)) " proposals: "
                              (str/join ", " (:approved results)))
                 :next-actions [(done-action session)
                                (status-action)]
                 :message (str "Approved " (count (:approved results)) " proposals.")))))))

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
   - :dry-run - Show what would happen without executing

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
        reason (:reason options)
        dry-run? (:dry-run options)]

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

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run?
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            proposal (:proposal mote)
            _ (when-not proposal
                (throw (ex-info "No active proposal on this mote"
                                {:type :no-proposal
                                 :mote-id id})))
            config (store/load-config repo-path)
            current-rejections (count (filter #(= :reject (:type %)) (:votes proposal)))
            quorum (:proposal-quorum config 2)
            would-reach-quorum? (>= (inc current-rejections) quorum)]
        (dry-run-result
         :output (str "Would record rejection vote on " id
                      "\n\nCurrent votes: " current-rejections "/" quorum " rejections"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached!"
                             (format-would-delete (:children proposal))
                             (format-would-update [{:id id :change "clear proposal, add :needs-decomposition taint"}]))
                        (str "\n\nQuorum not yet reached. " (- quorum (inc current-rejections)) " more votes needed.")))
         :would-delete (when would-reach-quorum? (:children proposal))
         :would-update [{:id id :change (if would-reach-quorum?
                                          "clear proposal, add :needs-decomposition"
                                          "add rejection vote")}]
         :next-actions [(done-action (or session-id "<session>"))
                        (show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session-id :reject id)
            agent (or (:name options) (:agent sess))
            result (proposal/reject-proposal! repo-path id agent :reason reason)
            reject-result (:result result)
            quorum-status (:quorum-status reject-result)]
        (assoc reject-result
               :next-actions (if (= :rejected quorum-status)
                               ;; Quorum reached - children archived
                               [(done-action session-id)]
                               ;; Still pending - waiting for more votes
                               [(done-action session-id)
                                (show-action id)])
               :message (if (= :rejected quorum-status)
                          "Proposal rejected. Children archived."
                          "Vote recorded. Waiting for more advisor votes."))))))

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
   - :dry-run - Show what would change without executing

   At least one of claim/priority/difficulty must be provided.

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim priority difficulty name dry-run]} options
        agent (or name "cli-user")]

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

        (if dry-run
          ;; Dry run - show what would change
          (let [changes (cond-> []
                          claim (conj (str "claim: \"" (:claim current-mote) "\" -> \"" claim "\""))
                          parsed-priority (conj (str "priority: " (name (:priority current-mote)) " -> " (name parsed-priority)))
                          difficulty (conj (str "difficulty: " (:difficulty current-mote) " -> " difficulty)))]
            (dry-run-result
             :output (str (format-would-update
                           [{:id id :change (str/join ", " changes)}]))
             :would-update [{:id id :change (str/join ", " changes)}]
             :next-actions [(show-action id)
                            (ready-action)]))
          ;; Execute
          (let [updated-mote (cond-> current-mote
                              claim (mote/set-claim claim)
                              parsed-priority (mote/set-priority parsed-priority)
                              difficulty (mote/set-difficulty difficulty))]
            (tx/atomic-write! repo-path
                              (str "Update mote " id)
                              [updated-mote])
            (assoc updated-mote
                   :next-actions [(show-action id)
                                  (ready-action)])))))))

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
   - :propagate - Auto-vote on parents when all children verified
   - :dry-run - Show what would happen without executing

   Exactly one of --for or --against must be provided.

   When quorum is reached:
   - :verified if unanimous for votes
   - :refuted if unanimous against votes
   - :contested if mixed votes

   When --propagate is used:
   - After voting, checks if all siblings are verified
   - If yes and agent can vote on parent, auto-votes on parent
   - Recursively continues up the tree

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :pending, :verified, :refuted, or :contested
   - :status-changed - Whether the mote status changed
   - :new-status - The new mote status
   - :propagated - Vector of parent IDs that were auto-voted (if --propagate)"
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [for against reason session propagate dry-run]} options]

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

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            config (store/load-config repo-path)
            vote-type (if for "FOR" "AGAINST")
            current-votes (:votes mote)
            for-votes (count (filter #(= :for (:type %)) current-votes))
            against-votes (count (filter #(= :against (:type %)) current-votes))
            quorum (:vote-quorum config 2)
            new-for (if for (inc for-votes) for-votes)
            new-against (if against (inc against-votes) against-votes)
            total-votes (+ new-for new-against)
            would-reach-quorum? (>= total-votes quorum)
            predicted-status (when would-reach-quorum?
                               (cond
                                 (and (pos? new-for) (zero? new-against)) :verified
                                 (and (zero? new-for) (pos? new-against)) :refuted
                                 :else :contested))]
        (dry-run-result
         :output (str "Would vote " vote-type " on " id
                      "\n\nCurrent votes: " for-votes " for, " against-votes " against (quorum: " quorum ")"
                      "\nAfter vote: " new-for " for, " new-against " against"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached! Status would change to: " (name predicted-status))
                        (str "\n\nQuorum not yet reached. Need " (- quorum total-votes) " more votes.")))
         :would-update [{:id id :change (str "add " vote-type " vote"
                                             (when would-reach-quorum?
                                               (str ", change status to " (name predicted-status))))}]
         :next-actions [(done-action (or session "<session>"))
                        (show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session :vote id)
            agent (or (:name options) (:agent sess))
            vote-type (if for :for :against)
            result (verify/cast-vote! repo-path id agent vote-type :reason reason)
            vote-result (:result result)
            quorum-status (:quorum-status vote-result)
            ;; Handle propagation if requested and vote was for (not against)
            final-result (if (and propagate for (= :verified quorum-status))
                           (let [propagated (verify/propagate-verification! repo-path id agent :reason reason)]
                             (assoc vote-result :propagated propagated))
                           vote-result)
            ;; Generate intelligent next-actions based on state
            next-acts (generate-vote-next-actions repo-path id session agent quorum-status)]
        (assoc final-result
               :next-actions next-acts
               :message (case quorum-status
                          :verified "Mote verified! Quorum reached."
                          :refuted "Mote refuted. Quorum reached."
                          :contested "Mote contested - votes are mixed."
                          :pending (str "Vote recorded. Waiting for more votes.")))))))

;; -----------------------------------------------------------------------------
;; Batch Vote Command
;; -----------------------------------------------------------------------------

(defn- find-eligible-motes-for-voting
  "Find all motes that an agent can vote on.

   Returns motes that:
   - Need verification (status :fixed with :needs-verification taint)
   - Agent hasn't already voted on
   - Agent can vote on (not a contributor)

   Arguments:
   - repo-path: Path to the repository
   - agent: Agent identifier

   Returns sequence of [mote-id mote] pairs."
  [repo-path agent]
  (let [all-motes (store/load-all-motes repo-path)]
    (->> all-motes
         (filter (fn [[_id mote]]
                   (and (verify/needs-verification? mote)
                        (not (verify/has-voted? mote agent))
                        (session/can-vote? mote agent))))
         (sort-by first))))

(defn cmd-vote-all!
  "Cast verification votes on multiple motes at once.

   Options:
   - :session - Session token (required)
   - :for - Vote in favor of verification
   - :against - Vote against verification
   - :reason - Reason for votes (optional)
   - :agent - Agent name (defaults to session agent)
   - :pending - Only vote on motes needing verification (default true)
   - :dry-run - Show what would be voted on without voting

   Finds all motes that need verification and that the agent can vote on
   (excluding self-votes), then casts the specified vote on each.

   Returns map with:
   - :voted - Vector of mote IDs that were voted on
   - :skipped - Vector of maps with :mote-id and :reason for skipped motes
   - :total-voted - Count of votes cast
   - :total-skipped - Count of motes skipped
   - :dry-run - True if this was a dry run"
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [for against reason session dry-run]} options]

    ;; Validation
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

    ;; Session enforcement (but allow viewing dry-run without session)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [;; Get agent from session or options
          sess (when session
                 (session/load-session repo-path session))
          agent (or (:name options)
                    (:agent sess)
                    (when dry-run "dry-run-agent"))

          _ (when (and (not dry-run) (not agent))
              (throw (ex-info "Agent name is required"
                              {:type :validation-failed
                               :errors ["Provide --name or use a valid session"]})))

          ;; Find eligible motes
          eligible (find-eligible-motes-for-voting repo-path agent)
          eligible-ids (map first eligible)]

      (if dry-run
        ;; Dry run - just report what would be voted on
        {:voted []
         :would-vote (vec eligible-ids)
         :total-would-vote (count eligible-ids)
         :dry-run true
         :next-actions [(make-action (str "af vote-all " (if for "--for" "--against") " --session <session>")
                                     "Execute batch vote")
                        (status-action)]}

        ;; Actually cast votes
        (let [vote-type (if for :for :against)
              results (reduce
                       (fn [acc [mote-id _mote]]
                         (try
                           (verify/cast-vote! repo-path mote-id agent vote-type :reason reason)
                           (update acc :voted conj mote-id)
                           (catch Exception e
                             (update acc :skipped conj
                                     {:mote-id mote-id
                                      :reason (ex-message e)}))))
                       {:voted [] :skipped []}
                       eligible)]
          (assoc results
                 :total-voted (count (:voted results))
                 :total-skipped (count (:skipped results))
                 :dry-run false
                 :next-actions [(done-action session)
                                (status-action)]
                 :message (str "Voted on " (count (:voted results)) " motes.")))))))

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
   - :dry-run - Show what would change without executing

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
        {:keys [add remove session dry-run]} options
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

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

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

        (if dry-run
          ;; Dry run - show what would change
          (let [current-taints (set (:taint current-mote))
                new-taints (-> current-taints
                               (into (filter some? parsed-adds))
                               (disj (filter some? parsed-removes)))
                changes (cond-> []
                          (seq adds) (conj (str "add: " (str/join ", " (map name (filter some? parsed-adds)))))
                          (seq removes) (conj (str "remove: " (str/join ", " (map name (filter some? parsed-removes))))))]
            (dry-run-result
             :output (str "Current taints: " (if (seq current-taints)
                                               (str/join ", " (map name current-taints))
                                               "(none)")
                          (format-would-update
                           [{:id id :change (str/join "; " changes)}]))
             :would-update [{:id id :change (str/join "; " changes)}]
             :next-actions [(done-action (or session "<session>"))
                            (show-action id)]))

          ;; Execute
          (do
            ;; Enforce session - check both actions if both operations requested
            (when (seq adds)
              (session/enforce-session! repo-path session :taint-add id))
            (when (seq removes)
              (session/enforce-session! repo-path session :taint-remove id))

            ;; Apply taint changes
            (let [updated-mote (as-> current-mote m
                                (reduce mote/add-taint m (filter some? parsed-adds))
                                (reduce mote/remove-taint m (filter some? parsed-removes)))]
              (tx/atomic-write! repo-path
                                (str "Update taints on " id)
                                [updated-mote])
              (assoc updated-mote
                     :next-actions [(done-action session)
                                    (show-action id)]))))))))

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
   - :dry-run - Show what would happen without executing

   Errors if mote is already claimed by another agent.

   Returns the updated mote with :session-id."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [name role dry-run]} options
        agent name]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to claim"]})))

    (when-not agent
      (throw (ex-info "Agent name is required"
                      {:type :validation-failed
                       :errors ["Provide --name to claim the mote"]})))

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
      (when-let [current-claimer (:claimed-by current-mote)]
        (when (not= current-claimer agent)
          (throw (ex-info "Mote already claimed"
                          {:type :already-claimed
                           :mote-id id
                           :claimed-by current-claimer}))))

      (if dry-run
        ;; Dry run - show what would happen
        (dry-run-result
         :output (str "Would claim mote " id " for agent \"" agent "\" as " (name role)
                      (format-would-create
                       [(str "session for " agent " on " id " as " (name role))])
                      (format-would-update
                       [{:id id :change (str "set claimed-by to \"" agent "\"")}]))
         :would-create [{:type :session :agent agent :mote-id id :role role}]
         :would-update [{:id id :change (str "claimed-by: " agent)}]
         :next-actions [(show-action id)
                        (ready-action)])

        ;; Execute
        (do
          ;; Ensure session directories exist
          (session/ensure-session-dirs! repo-path)

          ;; Create session with configurable timeout
          (let [config (store/load-config repo-path)
                session-timeout (or (:session-timeout-minutes config) 30)
                sess (session/create-session! repo-path id role agent
                                              :duration-minutes session-timeout)
                session-id (:session-id sess)
                updated-mote (mote/set-claimed-by current-mote agent)]
            (tx/atomic-write! repo-path
                              (str "Claim mote " id " for " agent " as " (name role))
                              [updated-mote])
            (assoc updated-mote
                   :session-id session-id
                   :next-actions (conj
                                  (case role
                                    :verifier [(vote-action id session-id :for)
                                               (vote-action id session-id :against)]
                                    :advisor [(approve-action id session-id)
                                              (reject-action id session-id)]
                                    :proposer [(make-action (str "af propose " id " --session " session-id " --claim \"...\"")
                                                            "Submit decomposition proposal")]
                                    :prover [(make-action (str "af add-ref " id " --session " session-id " --ref \"...\"")
                                                          "Add external reference")]
                                    :ref-checker [(make-action (str "af add-ref " id " --session " session-id " --ref \"...\"")
                                                               "Add/update references")]
                                    :counterexample [(vote-action id session-id :for)
                                                     (vote-action id session-id :against)]
                                    [])
                                  (done-action session-id)))))))))

;; -----------------------------------------------------------------------------
;; Unclaim Command
;; -----------------------------------------------------------------------------

(defn cmd-unclaim!
  "Release claim on a mote.

   Arguments (in context):
   - :id - The mote ID to unclaim (required)

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Note: Prefer using 'af done' which properly ends the session.
   This command releases the claim but does not end the session.

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

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

    ;; Session enforcement (lighter validation - any session holder can unclaim, skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      (if dry-run?
        ;; Dry run - show what would happen
        (dry-run-result
         :output (str "Would release claim on mote " id
                      (when (:claimed-by current-mote)
                        (str " (currently claimed by \"" (:claimed-by current-mote) "\")"))
                      (format-would-update
                       [{:id id :change "clear claimed-by"}]))
         :would-update [{:id id :change "clear claimed-by"}]
         :next-actions [(ready-action)
                        (status-action)])

        ;; Execute
        (do
          (session/validate-session! repo-path session-id id)

          ;; Clear claim
          (let [updated-mote (mote/clear-claim current-mote)]
            (tx/atomic-write! repo-path
                              (str "Unclaim mote " id)
                              [updated-mote])
            (assoc updated-mote
                   :next-actions [(ready-action)
                                  (status-action)])))))))

;; -----------------------------------------------------------------------------
;; Done Command
;; -----------------------------------------------------------------------------

(defn cmd-done!
  "End a session and release the claimed mote.

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Ends the active session and releases the mote for other agents.
   The session is moved to the completed directory with stats recorded.

   Returns map with:
   - :session-id - The session that was ended
   - :mote-id - The mote that was released
   - :action-count - Number of actions performed in the session"
  [{:keys [options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

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

        (if dry-run?
          ;; Dry run - show what would happen
          (dry-run-result
           :output (str "Would end session " session-id
                        "\n\nSession info:"
                        "\n  Agent: " (:agent sess)
                        "\n  Mote: " mote-id
                        "\n  Role: " (name (:role sess))
                        "\n  Actions: " (:action-count sess 0)
                        (format-would-delete
                         [(str "session " session-id)])
                        (format-would-update
                         [{:id mote-id :change "clear claimed-by"}]))
           :would-delete [(str "session " session-id)]
           :would-update [{:id mote-id :change "clear claimed-by"}]
           :next-actions [(ready-action)
                          (status-action)])

          ;; Execute
          (let [ended-session (session/end-session! repo-path session-id :record-stats true)
                updated-mote (mote/clear-claim mote)]

            ;; Commit the changes
            (tx/atomic-write! repo-path
                              (str "Done: end session for " mote-id)
                              [updated-mote])

            {:session-id session-id
             :mote-id mote-id
             :action-count (:action-count ended-session)
             ;; CRITICAL: Agent termination message (alethfeld-atkc)
             :agent-should-terminate true
             :message "Session ended successfully."
             :terminate-message (str "\nYour work is complete. This agent should now terminate.\n\n"
                                     "To start new work, spawn a fresh agent:\n"
                                     "  af ready --agent <new-name>")
             :next-actions [(make-action "# Agent should terminate now" "Work complete - end this agent")
                            (make-action "af ready --agent <new-name>" "Start fresh agent for new work")]}))))))

;; -----------------------------------------------------------------------------
;; Withdraw Command
;; -----------------------------------------------------------------------------

(defn cmd-withdraw!
  "Withdraw a proposal that you created.

   Arguments (in context):
   - :id - The parent mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Only the original proposer can withdraw their own proposal.
   The proposal must be pending (not yet approved or rejected).

   On withdrawal:
   - Proposed children are archived
   - Parent gets :needs-decomposition taint back
   - Parent proposal is cleared

   Returns map with:
   - :withdrawn-children - Vector of archived child IDs
   - :mote-id - The parent mote ID"
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID with the proposal"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run?
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            proposal (:proposal mote)
            _ (when-not proposal
                (throw (ex-info "No active proposal on this mote"
                                {:type :no-proposal
                                 :mote-id id})))
            children (:children proposal)]
        (dry-run-result
         :output (str "Would withdraw proposal on " id
                      (format-would-delete children)
                      (format-would-update
                       [{:id id :change "clear proposal, add :needs-decomposition taint"}]))
         :would-delete children
         :would-update [{:id id :change "clear proposal"}]
         :next-actions [(done-action (or session-id "<session>"))
                        (show-action id)]))

      ;; Execute
      (let [sess (session/load-active-session repo-path session-id)]
        (when-not sess
          (throw (ex-info "Session not found or expired"
                          {:type :invalid-session
                           :session-id session-id})))
        (when (session/session-expired? sess)
          (throw (ex-info "Session has expired"
                          {:type :session-expired
                           :session-id session-id})))

        (let [agent (:agent sess)
              result (proposal/withdraw-proposal! repo-path id agent)]
          (assoc (:result result)
                 :mote-id id
                 :message "Proposal withdrawn. Children archived."
                 :next-actions [(done-action session-id)
                                (show-action id)]))))))

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
        (assoc updated-mote
               :message "Reference added."
               :next-actions [(make-action (str "af add-ref " id " --session " session " --ref \"...\"")
                                           "Add another reference")
                              (done-action session)
                              (show-action id)])))))

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
        (assoc updated-mote
               :message "Assumption added."
               :next-actions [(make-action (str "af add-assumption " id " --session " session " --ref <mote-id>")
                                           "Add another assumption")
                              (done-action session)
                              (show-action id)])))))

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
        (assoc updated-mote
               :message (str "Definition added: " symbol)
               :next-actions [(make-action (str "af add-definition " id " --session " session " --symbol \"...\" --meaning \"...\"")
                                           "Add another definition")
                              (done-action session)
                              (show-action id)])))))

;; -----------------------------------------------------------------------------
;; Add-Dependency Command
;; -----------------------------------------------------------------------------

(defn cmd-add-dep!
  "Add a dependency to a mote (mote X depends on mote Y).

   Arguments (in context):
   - :id - The mote ID to add dependency to (required)

   Options:
   - :session - Session token (required)
   - :depends-on - The mote ID that this mote depends on (required)
   - :reason - Optional note explaining why this dependency exists

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [depends-on reason session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add dependency to"]})))

    (when-not depends-on
      (throw (ex-info "Dependency target is required"
                      {:type :validation-failed
                       :errors ["Provide --depends-on with the mote ID"]})))

    (when (= id depends-on)
      (throw (ex-info "Mote cannot depend on itself"
                      {:type :validation-failed
                       :errors ["A mote cannot have a dependency on itself"]})))

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

    (session/enforce-session! repo-path session :add-dep id)

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Validate dependency target exists
      (when-not (store/load-mote repo-path depends-on)
        (throw (ex-info "Dependency target mote not found"
                        {:type :not-found
                         :mote-id depends-on})))

      ;; Check for duplicate dependency
      (when (some #(= depends-on (:ref %)) (:depends-on current-mote))
        (throw (ex-info "Dependency already exists"
                        {:type :validation-failed
                         :errors [(str "Mote " id " already depends on " depends-on)]})))

      ;; Create dependency and add to mote
      (let [dependency (cond-> {:ref depends-on}
                          reason (assoc :reason reason))
            updated-mote (mote/add-dep current-mote dependency)]
        (tx/atomic-write! repo-path
                          (str "Add dependency " id " -> " depends-on)
                          [updated-mote])
        (assoc updated-mote
               :message (str "Dependency added: " id " -> " depends-on)
               :next-actions [(make-action (str "af add-dep " id " --session " session " --depends-on <mote-id>")
                                           "Add another dependency")
                              (done-action session)
                              (show-action id)])))))

;; -----------------------------------------------------------------------------
;; Check Command
;; -----------------------------------------------------------------------------

(defn- format-check-concise
  "Format concise check output (default).

   Returns a human-readable summary string."
  [valid? mote-count schema-error-count dag-error-count]
  (if valid?
    (str "OK - " mote-count " motes validated")
    (str "FAILED - " (+ schema-error-count dag-error-count) " errors found"
         (when (pos? schema-error-count)
           (str " (" schema-error-count " schema)"))
         (when (pos? dag-error-count)
           (str " (" dag-error-count " DAG)")))))

(defn- format-check-verbose
  "Format verbose check output (with --verbose flag).

   Returns a detailed human-readable string."
  [valid? mote-count schema-errors dag-errors]
  (str "DAG Integrity Check\n"
       "==================\n"
       "Motes checked: " mote-count "\n"
       "Result: " (if valid? "VALID" "INVALID") "\n"
       (when (seq schema-errors)
         (str "\nSchema Errors (" (count schema-errors) "):\n"
              (str/join "\n"
                        (for [{:keys [mote-id error]} schema-errors]
                          (str "  " mote-id ": " error)))))
       (when (seq dag-errors)
         (str "\nDAG Errors (" (count dag-errors) "):\n"
              (str/join "\n"
                        (for [error dag-errors]
                          (str "  " (if (map? error)
                                      (str (:type error) ": " (:message error))
                                      error))))))))

(defn cmd-check
  "Validate entire DAG integrity.

   Validates:
   1. All parent refs exist
   2. All children refs exist and point back
   3. No cycles in assumption graph
   4. All internal assumption refs exist
   5. Schema validation on all motes

   Options:
   - :verbose - Show detailed error information

   Returns a result map:
   - :valid? - true if all validations passed
   - :mote-count - number of motes checked
   - :schema-errors - vector of schema validation errors (if any)
   - :dag-errors - vector of DAG validation errors (if any)
   - :output - Formatted check result string"
  [{:keys [options]}]
  (let [repo-path "."
        verbose? (:verbose options)]

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
                          (:valid? dag-result))

          ;; Format output
          output (if verbose?
                   (format-check-verbose all-valid? (count motes) schema-errors dag-errors)
                   (format-check-concise all-valid? (count motes) (count schema-errors) (count dag-errors)))]

      {:valid? all-valid?
       :mote-count (count motes)
       :schema-errors (when (seq schema-errors) schema-errors)
       :dag-errors (when (seq dag-errors) dag-errors)
       :output output
       :verbose? verbose?
       :message (if all-valid?
                  (str "All " (count motes) " motes valid.")
                  (str "Validation failed - found errors."))
       :next-actions (if all-valid?
                       [(status-action)
                        (ready-action)]
                       [(status-action)])})))

;; -----------------------------------------------------------------------------
;; Repair Command
;; -----------------------------------------------------------------------------

(defn cmd-repair
  "Detect and repair DAG inconsistencies.

   Options:
   - :dry-run - Show what would be fixed without fixing
   - :auto - Automatically fix all repairable issues

   Default behavior (no flags) shows detected issues with repair options.

   Returns map with:
   - :issues - Detected issues
   - :repairs - Repair results (if --auto)
   - :output - Formatted output string"
  [{:keys [options]}]
  (let [repo-path "."
        dry-run? (:dry-run options)
        auto? (:auto options)]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Detect issues
    (let [issues (repair/detect-issues repo-path)
          has-issues? (pos? (:total-issues issues))]

      (cond
        ;; No issues found
        (not has-issues?)
        {:issues issues
         :valid? true
         :output "Checking DAG integrity...\n\nNo issues found. DAG is healthy."
         :message "DAG is healthy."
         :next-actions [(status-action)]}

        ;; Dry run - show issues without fixing
        (or dry-run? (not auto?))
        {:issues issues
         :valid? false
         :output (str "Checking DAG integrity...\n\n"
                      "Found " (:total-issues issues) " issues:\n"
                      (repair/format-issues issues)
                      (when-not auto?
                        (str "\n\nRepair options:\n"
                             "  af repair --dry-run     Show what would be fixed\n"
                             "  af repair --auto        Fix automatically")))
         :message (str "Found " (:total-issues issues) " issues.")
         :next-actions [(make-action "af repair --auto" "Fix issues automatically")
                        (status-action)]}

        ;; Auto repair
        auto?
        (let [repairs (repair/execute-repairs! repo-path issues)]
          {:issues issues
           :repairs repairs
           :valid? false
           :output (str "Checking DAG integrity...\n\n"
                        "Found " (:total-issues issues) " issues:\n"
                        (repair/format-issues issues)
                        "\n\nRepairs applied:\n"
                        (repair/format-repairs repairs))
           :message "Repairs applied."
           :next-actions [(make-action "af check" "Verify repairs")
                          (status-action)]})))))

;; -----------------------------------------------------------------------------
;; Log Command
;; -----------------------------------------------------------------------------

(defn- format-log-concise
  "Format concise log output (default).

   Returns a human-readable summary string."
  [commits mote-id]
  (if (empty? commits)
    (str "No history for mote " mote-id)
    (str "History for " mote-id " (" (count commits) " commits):\n"
         (str/join "\n"
                   (for [commit commits]
                     (str "  " (:sha commit) " " (:message commit)))))))

(defn- format-log-verbose
  "Format verbose log output (with --verbose flag).

   Returns a detailed human-readable string."
  [commits mote-id]
  (if (empty? commits)
    (str "No history for mote " mote-id)
    (str "History for " mote-id " (" (count commits) " commits):\n"
         (str/join "\n\n"
                   (for [commit commits]
                     (str "  " (:sha commit) "\n"
                          "    " (:message commit)
                          (when (:author commit)
                            (str "\n    Author: " (:author commit)))
                          (when (:date commit)
                            (str "\n    Date: " (:date commit)))))))))

(defn cmd-log
  "Show git history for a mote.

   Arguments (in context):
   - :id - The mote ID to show history for (required)

   Options:
   - :limit - Maximum number of commits to show (default: 50)
   - :verbose - Show detailed commit info (author, date)

   Returns a map with:
   - :commits - Vector of commit maps
   - :mote-id - The mote ID
   - :output - Formatted history string"
  [{:keys [id options]}]
  (let [repo-path "."
        limit (or (:limit options) 50)
        verbose? (:verbose options)]

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
            history (git/git-log repo-path :path mote-file-path :max-count limit)
            commits (or history [])
            output (if verbose?
                     (format-log-verbose commits id)
                     (format-log-concise commits id))]
        {:commits commits
         :mote-id id
         :output output
         :verbose? verbose?
         :next-actions [(show-action id)
                        (tree-action id)
                        (status-action)]}))))

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
   - :dry-run - Show what would happen without executing

   Returns a result map:
   - :pulled - true if pull succeeded (or :skipped if no remote)
   - :committed - true if commit was made
   - :pushed - true if push succeeded (or :skipped if no remote or --no-push)
   - :commit-sha - SHA of the sync commit (if committed)

   Note: If no remote is configured, pull and push are skipped gracefully."
  [{:keys [options]}]
  (let [repo-path "."
        no-push (:no-push options)
        dry-run? (:dry-run options)]

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

    (if dry-run?
      ;; Dry run - show what would happen
      (let [has-remote (git/git-has-remote? repo-path)
            status (git/git-status repo-path)
            staged-files (:staged status)
            unstaged-files (:unstaged status)
            untracked-files (:untracked status)]
        (dry-run-result
         :output (str "Would sync with git:"
                      (if has-remote
                        "\n  1. git pull --rebase"
                        "\n  1. [skip] git pull (no remote configured)")
                      "\n  2. git add .alethfeld/"
                      "\n  3. git commit -m 'af sync <timestamp>'"
                      (cond
                        no-push "\n  4. [skip] git push (--no-push)"
                        has-remote "\n  4. git push"
                        :else "\n  4. [skip] git push (no remote configured)")
                      "\n\nFiles that would be staged:"
                      (if (or (seq staged-files) (seq unstaged-files) (seq untracked-files))
                        (str "\n  " (str/join "\n  "
                                              (concat staged-files unstaged-files
                                                      (map #(str "(new) " %) untracked-files))))
                        "\n  (no changes detected)"))
         :would-update [{:id "git" :change "sync with remote"}]
         :next-actions [(status-action)
                        (ready-action)]))

      ;; Execute
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
         :commit-sha (:sha commit-result)
         :message "Sync complete."
         :next-actions [(status-action)
                        (ready-action)]}))))

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
         :keys (keys config-keys)
         :next-actions [(make-action "af config set <key> <value>" "Update a config value")
                        (status-action)]})

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
           :default (:default spec)
           :next-actions [(make-action (str "af config set " key-name " <value>") "Change this value")
                          (make-action "af config list" "View all config")]}))

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
           :previous (get config key-kw)
           :message (str "Config updated: " key-name " = " parsed-value)
           :next-actions [(make-action "af config list" "View all config")
                          (status-action)]}))

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
   - verbose?: Whether to include extra details

   Returns a string representing this node."
  [mote prefix connector max-claim-len verbose?]
  (let [mote-id (:id mote)
        status (format-status (:status mote))
        taints (format-taints (:taint mote))
        claim (truncate-claim (:claim mote) max-claim-len)
        extra (when verbose?
                (str " [p:" (name (:priority mote)) " d:" (:difficulty mote) "]"
                     (when (:claimed-by mote) (str " *" (:claimed-by mote)))
                     (when (seq (:votes mote))
                       (let [for-count (count (filter #(= :for (:type %)) (:votes mote)))
                             against-count (count (filter #(= :against (:type %)) (:votes mote)))]
                         (str " votes:" for-count "/" against-count)))))]
    (str prefix connector mote-id " " status " " claim taints extra)))

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
   - verbose?: Whether to show extra details (optional, default false)
   - is-root: Whether this is the root node (no connector)

   Returns a vector of strings (one per line)."
  ;; Backward-compatible 7-arg entry point (for tests)
  ([mote motes prefix is-last current-depth max-depth max-claim-len]
   (render-tree mote motes prefix is-last current-depth max-depth max-claim-len false true))

  ;; 8-arg entry point with verbose flag
  ([mote motes prefix is-last current-depth max-depth max-claim-len verbose?]
   (render-tree mote motes prefix is-last current-depth max-depth max-claim-len verbose? true))

  ;; Full 9-arg implementation
  ([mote motes prefix is-last current-depth max-depth max-claim-len verbose? is-root]
   (let [;; Determine connector for this node
         connector (if is-root "" (if is-last "\\-- " "+-- "))
         ;; Render this node
         node-line (render-tree-node mote prefix connector max-claim-len verbose?)
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
                                          verbose?
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
   - :verbose - Show extra details (priority, difficulty, votes)

   Returns a map with:
   - :lines - Vector of rendered tree lines
   - :mote-count - Number of motes displayed
   - :output - Formatted tree string"
  [{:keys [id options]}]
  (let [repo-path "."
        max-depth (:depth options)
        verbose? (:verbose options)]

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
            ;; Render the tree (use longer claim length in verbose mode)
            max-claim-len (if verbose? 100 60)
            lines (render-tree mote motes "" true 0 max-depth max-claim-len verbose?)
            output (str/join "\n" lines)]
        {:lines (vec lines)
         :mote-count (count lines)
         :output output
         :verbose? verbose?
         :next-actions [(show-action id)
                        (ready-action)
                        (status-action)]}))))

;; -----------------------------------------------------------------------------
;; Status Command
;; -----------------------------------------------------------------------------

(defn- count-motes-by-role-needed
  "Count how many motes need each type of role.

   Returns a map of role -> count."
  [motes config]
  (let [mote-list (vals motes)
        claim-timeout (:claim-timeout-minutes config)
        workable (filter #(job/workable? % :claim-timeout claim-timeout) mote-list)
        roles (mapcat #(job/mote->roles %) workable)]
    (frequencies roles)))

(defn- format-status-concise
  "Format concise status output (default).

   Returns a human-readable summary string."
  [{:keys [project-name total-motes verified-count ready-for-work role-counts]}]
  (let [percent (if (pos? total-motes)
                  (int (* 100 (/ verified-count total-motes)))
                  0)
        role-summary (when (pos? ready-for-work)
                       (str/join ", "
                                 (for [[role cnt] (sort-by (comp - val) role-counts)
                                       :when (pos? cnt)]
                                   (str cnt " " (name role)))))]
    (str project-name " - " percent "% verified (" verified-count "/" total-motes ")\n"
         (if (pos? ready-for-work)
           (str "Ready work: " ready-for-work " motes (" role-summary ")")
           "No work available"))))

(defn- format-status-verbose
  "Format verbose status output (with --verbose flag).

   Returns a detailed human-readable summary string."
  [{:keys [project-name total-motes verified-count status-counts taint-counts
           active-sessions role-counts recent-activity]}]
  (let [percent (if (pos? total-motes)
                  (int (* 100 (/ verified-count total-motes)))
                  0)]
    (str project-name " - " percent "% verified\n"
         "\n"
         "By status:\n"
         (str/join "\n"
                   (for [[status cnt] (sort-by first status-counts)]
                     (str "  " (name status) ": " cnt)))
         "\n"
         (when (seq taint-counts)
           (str "\nBy taint:\n"
                (str/join "\n"
                          (for [[taint cnt] (sort-by first taint-counts)]
                            (str "  " (name taint) ": " cnt)))
                "\n"))
         "\nBy role needed:\n"
         (str/join "\n"
                   (for [role [:advisor :verifier :proposer :prover :ref-checker :counterexample]]
                     (let [cnt (get role-counts role 0)]
                       (str "  " (name role) ": " cnt " mote" (when (not= cnt 1) "s")))))
         "\n"
         "\nActive sessions: " active-sessions
         (when recent-activity
           (str "\nRecent: " recent-activity)))))

(defn cmd-status
  "Display project status summary.

   Options:
   - :verbose - Show detailed output (default: concise)

   Returns a map with:
   - :project-name - Name of the project
   - :root-motes - Number of root motes
   - :total-motes - Total number of motes
   - :status-counts - Map of status -> count
   - :taint-counts - Map of taint -> count
   - :active-sessions - Number of active sessions
   - :ready-for-work - Number of workable motes
   - :output - Formatted human-readable output"
  [{:keys [options]}]
  (let [repo-path "."
        verbose? (:verbose options)]

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
          verified-count (get status-counts :verified 0)

          ;; Count by taint
          taint-counts (->> mote-list
                            (mapcat :taint)
                            frequencies)

          ;; Load active sessions
          active-sessions (session/load-all-active-sessions repo-path)

          ;; Count workable motes (using job/workable?)
          claim-timeout (:claim-timeout-minutes config)
          workable-count (count (filter #(job/workable? % :claim-timeout claim-timeout) mote-list))

          ;; Count by role needed
          role-counts (count-motes-by-role-needed motes config)

          ;; Build status data
          status-data {:project-name project-name
                       :root-motes root-motes
                       :total-motes total-motes
                       :verified-count verified-count
                       :status-counts status-counts
                       :taint-counts taint-counts
                       :active-sessions (count active-sessions)
                       :ready-for-work workable-count
                       :role-counts role-counts}

          ;; Format output based on verbose flag
          output (if verbose?
                   (format-status-verbose status-data)
                   (format-status-concise status-data))]

      (assoc status-data
             :output output
             :verbose? verbose?
             :next-actions (if (pos? workable-count)
                             [(ready-action)
                              (make-action "af tree 1" "View proof structure")]
                             [(make-action "af check" "Validate DAG integrity")])))))

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
  (cli/register-handler! "vote-all" cmd-vote-all!)
  (cli/register-handler! "approve-all" cmd-approve-all!)
  (cli/register-handler! "taint" cmd-taint!)
  (cli/register-handler! "claim" cmd-claim!)
  (cli/register-handler! "unclaim" cmd-unclaim!)
  (cli/register-handler! "done" cmd-done!)
  (cli/register-handler! "withdraw" cmd-withdraw!)
  (cli/register-handler! "add-ref" cmd-add-ref!)
  (cli/register-handler! "add-assumption" cmd-add-assumption!)
  (cli/register-handler! "add-definition" cmd-add-definition!)
  (cli/register-handler! "add-dep" cmd-add-dep!)
  (cli/register-handler! "check" cmd-check)
  (cli/register-handler! "repair" cmd-repair)
  (cli/register-handler! "log" cmd-log)
  (cli/register-handler! "sync" cmd-sync!)
  (cli/register-handler! "config" cmd-config)
  (cli/register-handler! "tree" cmd-tree)
  (cli/register-handler! "status" cmd-status))

;; Auto-register handlers when namespace is loaded
(register-handlers!)
