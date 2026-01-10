(ns alethfeld.git
  "Git operations for Alethfeld repositories.

   All functions use babashka/process to shell out to git.
   Functions are designed to be testable with temp directories."
  (:require [babashka.fs :as fs]
            [babashka.process :as process]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Configuration Constants
;; -----------------------------------------------------------------------------

(def ^:private default-git-log-limit
  "Default maximum number of commits to return from git-log."
  50)

;; -----------------------------------------------------------------------------
;; Internal Helpers
;; -----------------------------------------------------------------------------

(defn- run-git
  "Run a git command in the specified directory.

   Arguments:
   - dir: Working directory for git command
   - args: Vector of git arguments (without 'git')
   - opts: Optional map with:
     - :check - If true (default), throws on non-zero exit

   Returns:
   - Map with :out, :err, :exit on success
   - Throws ExceptionInfo with :type :git-error on failure (when :check true)"
  [dir args & {:keys [check] :or {check true}}]
  (let [cmd (into ["git"] args)
        result (apply process/shell {:dir dir
                                     :out :string
                                     :err :string
                                     :continue true}
                      cmd)]
    (if (and check (not= 0 (:exit result)))
      (throw (ex-info "Git command failed"
                      {:type :git-error
                       :command (str/join " " cmd)
                       :exit (:exit result)
                       :stderr (:err result)
                       :stdout (:out result)}))
      result)))

(defn- git-dir
  "Get the .git directory path for a repository."
  [repo-path]
  (str repo-path "/.git"))

;; -----------------------------------------------------------------------------
;; Status & Queries
;; -----------------------------------------------------------------------------

(defn git-initialized?
  "Check if a directory is a git repository.

   Arguments:
   - repo-path: Path to check

   Returns true if .git directory exists."
  [repo-path]
  (fs/directory? (git-dir repo-path)))

(defn git-status
  "Get the status of the git repository.

   Arguments:
   - repo-path: Path to the git repository

   Returns map with:
   - :clean? - true if working tree is clean
   - :staged - vector of staged files
   - :unstaged - vector of modified but not staged files
   - :untracked - vector of untracked files

   Throws if not a git repository."
  [repo-path]
  (let [result (run-git repo-path ["status" "--porcelain"])
        lines (when-not (str/blank? (:out result))
                (str/split-lines (:out result)))
        parse-line (fn [line]
                     (when (>= (count line) 3)
                       (let [index-status (nth line 0)
                             worktree-status (nth line 1)
                             filename (str/trim (subs line 3))]
                         {:index-status index-status
                          :worktree-status worktree-status
                          :filename filename})))
        parsed (keep parse-line lines)
        staged (filterv #(not= \space (:index-status %)) parsed)
        unstaged (filterv #(and (not= \space (:worktree-status %))
                                (not= \? (:worktree-status %)))
                          parsed)
        untracked (filterv #(= \? (:index-status %)) parsed)]
    {:clean? (empty? parsed)
     :staged (mapv :filename staged)
     :unstaged (mapv :filename unstaged)
     :untracked (mapv :filename untracked)}))

(defn git-has-commits?
  "Check if the repository has any commits.

   Arguments:
   - repo-path: Path to the git repository

   Returns true if HEAD exists (at least one commit)."
  [repo-path]
  (let [result (run-git repo-path ["rev-parse" "HEAD"] :check false)]
    (= 0 (:exit result))))

;; -----------------------------------------------------------------------------
;; Init Operations
;; -----------------------------------------------------------------------------

(defn git-init!
  "Initialize a git repository.

   Arguments:
   - repo-path: Path to initialize

   Options:
   - :initial-branch - Name for initial branch (default: 'main')

   Returns the repo path.
   Does nothing if already initialized."
  [repo-path & {:keys [initial-branch] :or {initial-branch "main"}}]
  (when-not (git-initialized? repo-path)
    (fs/create-dirs repo-path)
    (run-git repo-path ["init" "-b" initial-branch]))
  repo-path)

;; -----------------------------------------------------------------------------
;; Staging Operations
;; -----------------------------------------------------------------------------

(defn git-add!
  "Stage specific files for commit.

   Arguments:
   - repo-path: Path to the git repository
   - paths: String or vector of paths to stage (relative to repo)

   Returns the repo path."
  [repo-path paths]
  (let [path-vec (if (string? paths) [paths] paths)]
    (when (seq path-vec)
      (run-git repo-path (into ["add"] path-vec))))
  repo-path)

(defn git-add-all!
  "Stage all changes in .alethfeld/ directory.

   Arguments:
   - repo-path: Path to the git repository

   Returns the repo path."
  [repo-path]
  (run-git repo-path ["add" ".alethfeld/"])
  repo-path)

;; -----------------------------------------------------------------------------
;; Commit Operations
;; -----------------------------------------------------------------------------

(defn git-commit!
  "Create a commit with the staged changes.

   Arguments:
   - repo-path: Path to the git repository
   - message: Commit message

   Options:
   - :allow-empty - If true, allow commits with no changes (default: false)
   - :author - Author string 'Name <email>' (uses git config if not specified)

   Returns map with:
   - :sha - The commit SHA (first 7 chars)
   - :message - The commit message

   Throws if no changes staged (unless :allow-empty true)."
  [repo-path message & {:keys [allow-empty author] :or {allow-empty false}}]
  (let [args (cond-> ["commit" "-m" message]
               allow-empty (conj "--allow-empty")
               author (conj "--author" author))
        _ (run-git repo-path args)
        ;; Get the SHA of the commit we just made
        sha-result (run-git repo-path ["rev-parse" "--short" "HEAD"])]
    {:sha (str/trim (:out sha-result))
     :message message}))

;; -----------------------------------------------------------------------------
;; Log Operations
;; -----------------------------------------------------------------------------

(defn git-log
  "Get commit history.

   Arguments:
   - repo-path: Path to the git repository

   Options:
   - :path - If specified, only show commits affecting this path
   - :max-count - Maximum number of commits to return (default: 50)
   - :format - Output format :oneline, :short, :full (default: :oneline)

   Returns vector of commit maps with:
   - :sha - Commit SHA (short)
   - :message - Commit message
   - :author - Author name (if format is :short or :full)
   - :date - Commit date (if format is :full)"
  [repo-path & {:keys [path max-count format]
                :or {max-count default-git-log-limit format :oneline}}]
  (when (git-has-commits? repo-path)
    (let [format-str (case format
                       :oneline "%h %s"
                       :short "%h|%an|%s"
                       :full "%h|%an|%ai|%s")
          args (cond-> ["log" (str "--max-count=" max-count)
                        (str "--format=" format-str)]
                 path (conj "--" path))
          result (run-git repo-path args)
          lines (when-not (str/blank? (:out result))
                  (str/split-lines (:out result)))
          parse-line (fn [line]
                       (case format
                         :oneline
                         (let [[sha & rest] (str/split line #" " 2)]
                           {:sha sha
                            :message (str/join " " rest)})
                         :short
                         (let [[sha author message] (str/split line #"\|" 3)]
                           {:sha sha
                            :author author
                            :message message})
                         :full
                         (let [[sha author date message] (str/split line #"\|" 4)]
                           {:sha sha
                            :author author
                            :date date
                            :message message})))]
      (mapv parse-line lines))))

;; -----------------------------------------------------------------------------
;; Remote Operations
;; -----------------------------------------------------------------------------

(defn git-has-remote?
  "Check if the repository has a remote configured.

   Arguments:
   - repo-path: Path to the git repository
   - remote: Remote name to check (default: 'origin')

   Returns true if remote exists."
  [repo-path & {:keys [remote] :or {remote "origin"}}]
  (let [result (run-git repo-path ["remote" "get-url" remote] :check false)]
    (= 0 (:exit result))))

(defn git-pull!
  "Pull changes from remote with rebase.

   Arguments:
   - repo-path: Path to the git repository

   Options:
   - :remote - Remote name (default: 'origin')
   - :branch - Branch name (default: current branch)
   - :rebase - If true (default), use rebase instead of merge

   Returns map with:
   - :success - true if pull succeeded
   - :up-to-date - true if already up to date

   Throws if pull fails (conflicts, no remote, etc.)."
  [repo-path & {:keys [remote branch rebase]
                :or {remote "origin" rebase true}}]
  (when-not (git-has-remote? repo-path :remote remote)
    (throw (ex-info "No remote configured"
                    {:type :no-remote
                     :remote remote})))
  (let [args (cond-> ["pull" remote]
               branch (conj branch)
               rebase (conj "--rebase"))
        result (run-git repo-path args)]
    {:success true
     :up-to-date (str/includes? (:out result) "Already up to date")}))

(defn git-push!
  "Push commits to remote.

   Arguments:
   - repo-path: Path to the git repository

   Options:
   - :remote - Remote name (default: 'origin')
   - :branch - Branch name (default: current branch)
   - :set-upstream - If true, set upstream tracking (default: false)

   Returns map with:
   - :success - true if push succeeded

   Throws if push fails."
  [repo-path & {:keys [remote branch set-upstream]
                :or {remote "origin" set-upstream false}}]
  (when-not (git-has-remote? repo-path :remote remote)
    (throw (ex-info "No remote configured"
                    {:type :no-remote
                     :remote remote})))
  (let [args (cond-> ["push" remote]
               branch (conj branch)
               set-upstream (conj "--set-upstream"))
        _ (run-git repo-path args)]
    {:success true}))

;; -----------------------------------------------------------------------------
;; Configuration
;; -----------------------------------------------------------------------------

(defn git-config!
  "Set a git configuration value.

   Arguments:
   - repo-path: Path to the git repository
   - key: Configuration key (e.g., 'user.name')
   - value: Configuration value

   Returns the repo path."
  [repo-path key value]
  (run-git repo-path ["config" key value])
  repo-path)

(defn git-config
  "Get a git configuration value.

   Arguments:
   - repo-path: Path to the git repository
   - key: Configuration key (e.g., 'user.name')

   Returns the value, or nil if not set."
  [repo-path key]
  (let [result (run-git repo-path ["config" "--get" key] :check false)]
    (when (= 0 (:exit result))
      (str/trim (:out result)))))
