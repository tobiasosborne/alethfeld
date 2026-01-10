(ns alethfeld.cmd.utility
  "Utility commands: check, repair, log, sync, tree, status."
  (:require [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.dag :as dag]
            [alethfeld.id :as id]
            [alethfeld.job :as job]
            [alethfeld.path :as path]
            [alethfeld.repair :as repair]
            [alethfeld.session :as session]
            [alethfeld.cmd.core :as core]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Display Constants
;; -----------------------------------------------------------------------------

(def ^:const tree-claim-verbose-max-length
  "Maximum length for claim text in verbose tree display.
   Verbose mode shows more context, so longer claims are useful."
  100)

(def ^:const tree-claim-default-max-length
  "Maximum length for claim text in default (non-verbose) tree display.
   Shorter to keep tree output compact and readable."
  60)

(def ^:const default-log-limit
  "Default maximum number of commits to show in log output."
  50)

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
  [{:keys [options repo-path] :or {repo-path "."}}]
  (let [verbose? (:verbose options)]

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
                       [(core/status-action)
                        (core/ready-action)]
                       [(core/status-action)])})))

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
  [{:keys [options repo-path] :or {repo-path "."}}]
  (let [dry-run? (:dry-run options)
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
         :next-actions [(core/status-action)]}

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
         :next-actions [(core/make-action "af repair --auto" "Fix issues automatically")
                        (core/status-action)]}

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
           :next-actions [(core/make-action "af check" "Verify repairs")
                          (core/status-action)]})))))

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
  [{:keys [id options repo-path] :or {repo-path "."}}]
  (let [limit (or (:limit options) default-log-limit)
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
         :next-actions [(core/show-action id)
                        (core/tree-action id)
                        (core/status-action)]}))))

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
  [{:keys [options repo-path] :or {repo-path "."}}]
  (let [no-push (:no-push options)
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
        (core/dry-run-result
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
         :next-actions [(core/status-action)
                        (core/ready-action)]))

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
         :next-actions [(core/status-action)
                        (core/ready-action)]}))))

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
  [{:keys [id options repo-path] :or {repo-path "."}}]
  (let [max-depth (:depth options)
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
            max-claim-len (if verbose? tree-claim-verbose-max-length tree-claim-default-max-length)
            lines (render-tree mote motes "" true 0 max-depth max-claim-len verbose?)
            output (str/join "\n" lines)]
        {:lines (vec lines)
         :mote-count (count lines)
         :output output
         :verbose? verbose?
         :next-actions [(core/show-action id)
                        (core/ready-action)
                        (core/status-action)]}))))

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

(defn- leaf-mote?
  "Check if a mote is a leaf (has no children)."
  [mote]
  (empty? (:children mote)))

(defn- intermediate-mote?
  "Check if a mote is intermediate (has children)."
  [mote]
  (seq (:children mote)))

(defn- categorize-motes
  "Categorize motes into leaf and intermediate.
   Returns {:leaf-motes [...] :intermediate-motes [...]}."
  [mote-list]
  {:leaf-motes (filterv leaf-mote? mote-list)
   :intermediate-motes (filterv intermediate-mote? mote-list)})

(defn- count-motes-needing-proposer-work
  "Count motes that need proposer work (decomposition).
   Only counts motes with :needs-decomposition taint."
  [mote-list]
  (count (filter #(contains? (:taint %) :needs-decomposition) mote-list)))

(defn- count-motes-needing-advisor-work
  "Count motes that need advisor review (proposal review).
   Only counts motes with :needs-proposal-review taint."
  [mote-list]
  (count (filter #(contains? (:taint %) :needs-proposal-review) mote-list)))

(defn- count-motes-needing-verification
  "Count motes that need verification votes.
   Only counts leaf motes with :needs-verification taint."
  [mote-list]
  (count (filter #(and (leaf-mote? %)
                       (contains? (:taint %) :needs-verification))
                 mote-list)))

(defn- count-votes-at-quorum
  "Count how many leaf motes with :needs-verification have reached quorum.
   Returns {:at-quorum n :total m}."
  [mote-list quorum]
  (let [needs-verify (filter #(and (leaf-mote? %)
                                   (contains? (:taint %) :needs-verification))
                             mote-list)
        total (count needs-verify)
        at-quorum (count (filter (fn [mote]
                                   (let [votes (:votes mote [])
                                         for-count (count (filter #(= :for (:vote %)) votes))]
                                     (>= for-count quorum)))
                                 needs-verify))]
    {:at-quorum at-quorum :total total}))

(defn- all-leaves-verified?
  "Check if all leaf motes are verified."
  [mote-list]
  (let [leaves (filter leaf-mote? mote-list)]
    (and (seq leaves)
         (every? #(= :verified (:status %)) leaves))))

(defn- has-fixed-intermediate-motes?
  "Check if there are intermediate motes with :fixed status."
  [mote-list]
  (some #(and (intermediate-mote? %)
              (= :fixed (:status %)))
        mote-list))

(defn- suggest-next-action
  "Suggest the next action based on work remaining by stage.
   Returns a string suggestion."
  [proposer-work advisor-work verifier-work]
  (cond
    (pos? verifier-work) "af ready --role verifier"
    (pos? advisor-work)  "af ready --role advisor"
    (pos? proposer-work) "af ready --role proposer"
    :else                nil))

(defn- format-progress-by-stage
  "Format the progress breakdown by stage.
   Returns a string with proposer/advisor/verifier work remaining."
  [{:keys [proposer-work advisor-work verifier-work quorum-progress]}]
  (let [{:keys [at-quorum total]} quorum-progress]
    (str "Progress by stage:\n"
         "  Proposer work:    " proposer-work " remaining"
         (when (zero? proposer-work) " (all decomposed)") "\n"
         "  Advisor reviews:  " advisor-work " remaining"
         (when (zero? advisor-work) " (all proposals approved)") "\n"
         "  Verifier votes:   " verifier-work " remaining"
         (when (pos? total)
           (str " (" at-quorum "/" total " at quorum)"))
         (when (zero? verifier-work) " (all verified)"))))

(defn- format-structure-summary
  "Format the mote structure summary.
   Returns a string like 'Structure: 5 intermediate + 14 leaf motes'."
  [{:keys [leaf-count intermediate-count]}]
  (str "Structure: " intermediate-count " intermediate + " leaf-count " leaf motes"))

(defn- format-intermediate-mote-note
  "Format the explanatory note when all leaves are verified but parents are fixed.
   Returns nil if not applicable."
  [{:keys [all-leaves-verified? fixed-intermediate-count]}]
  (when (and all-leaves-verified? (pos? fixed-intermediate-count))
    (str "\nNote: " fixed-intermediate-count " intermediate mote"
         (when (> fixed-intermediate-count 1) "s")
         " " (if (> fixed-intermediate-count 1) "are" "is")
         " \"fixed\" (decomposed into children).\n"
         "      Verification applies to leaf motes only.\n"
         "      All leaves verified = proof complete.")))

(defn- format-status-concise
  "Format concise status output (default).

   Returns a human-readable summary string."
  [{:keys [project-name total-motes verified-count ready-for-work
           proposer-work advisor-work verifier-work quorum-progress
           leaf-count intermediate-count all-leaves-verified? fixed-intermediate-count
           next-action-suggestion]}]
  (let [percent (if (pos? total-motes)
                  (int (* 100 (/ verified-count total-motes)))
                  0)
        has-work? (or (pos? proposer-work)
                      (pos? advisor-work)
                      (pos? verifier-work))]
    (str project-name " - " percent "% verified (" verified-count "/" total-motes ")\n"
         "\n"
         (format-progress-by-stage {:proposer-work proposer-work
                                    :advisor-work advisor-work
                                    :verifier-work verifier-work
                                    :quorum-progress quorum-progress})
         "\n\n"
         (format-structure-summary {:leaf-count leaf-count
                                    :intermediate-count intermediate-count})
         (when-let [note (format-intermediate-mote-note
                          {:all-leaves-verified? all-leaves-verified?
                           :fixed-intermediate-count fixed-intermediate-count})]
           note)
         (when (and has-work? next-action-suggestion)
           (str "\nNext action: " next-action-suggestion)))))

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
   - :proposer-work - Motes needing decomposition
   - :advisor-work - Motes needing proposal review
   - :verifier-work - Motes needing verification
   - :leaf-count - Number of leaf motes
   - :intermediate-count - Number of intermediate motes
   - :output - Formatted human-readable output"
  [{:keys [options repo-path] :or {repo-path "."}}]
  (let [verbose? (:verbose options)]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (let [;; Load config for project name and quorum
          config (store/load-config repo-path)
          project-name (:project-name config "Unnamed Project")
          vote-quorum (or (:vote-quorum config) 1)

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

          ;; Enhanced status: work by stage
          proposer-work (count-motes-needing-proposer-work mote-list)
          advisor-work (count-motes-needing-advisor-work mote-list)
          verifier-work (count-motes-needing-verification mote-list)
          quorum-progress (count-votes-at-quorum mote-list vote-quorum)

          ;; Enhanced status: mote categorization
          {:keys [leaf-motes intermediate-motes]} (categorize-motes mote-list)
          leaf-count (count leaf-motes)
          intermediate-count (count intermediate-motes)

          ;; Enhanced status: check if all leaves verified
          leaves-verified? (all-leaves-verified? mote-list)
          fixed-intermediate-count (count (filter #(= :fixed (:status %)) intermediate-motes))

          ;; Suggest next action
          next-action-suggestion (suggest-next-action proposer-work advisor-work verifier-work)

          ;; Build status data
          status-data {:project-name project-name
                       :root-motes root-motes
                       :total-motes total-motes
                       :verified-count verified-count
                       :status-counts status-counts
                       :taint-counts taint-counts
                       :active-sessions (count active-sessions)
                       :ready-for-work workable-count
                       :role-counts role-counts
                       ;; Enhanced fields for v0.2-4.2 and v0.2-4.3
                       :proposer-work proposer-work
                       :advisor-work advisor-work
                       :verifier-work verifier-work
                       :quorum-progress quorum-progress
                       :leaf-count leaf-count
                       :intermediate-count intermediate-count
                       :all-leaves-verified? leaves-verified?
                       :fixed-intermediate-count fixed-intermediate-count
                       :next-action-suggestion next-action-suggestion}

          ;; Format output based on verbose flag
          output (if verbose?
                   (format-status-verbose status-data)
                   (format-status-concise status-data))]

      (assoc status-data
             :output output
             :verbose? verbose?
             :next-actions (if (pos? workable-count)
                             [(core/ready-action)
                              (core/make-action "af tree 1" "View proof structure")]
                             [(core/make-action "af check" "Validate DAG integrity")])))))
