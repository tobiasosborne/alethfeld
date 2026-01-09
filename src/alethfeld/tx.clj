(ns alethfeld.tx
  "Transaction layer for git-backed ACID operations.

   Provides atomic, validated operations that wrap mote changes
   in git commits with automatic rollback on validation failure."
  (:require [alethfeld.git :as git]
            [alethfeld.store :as store]
            [alethfeld.dag :as dag]
            [alethfeld.io :as io]
            [babashka.fs :as fs])
  (:import [java.util.concurrent.locks ReentrantLock]
           [java.util.concurrent ConcurrentHashMap]))

;; -----------------------------------------------------------------------------
;; Repository Locking
;; -----------------------------------------------------------------------------

(def ^:private repo-locks
  "Map of canonical repo paths to their ReentrantLocks.
   Used to serialize transactions per repository.

   LOCK LIFECYCLE:
   Lock entries accumulate in this map and are never removed. This is acceptable
   for typical CLI usage where each process operates on a single repository.
   The memory overhead per entry is minimal (~1KB: path string + ReentrantLock).

   For long-running processes that operate on many different repositories over
   time (e.g., a daemon managing thousands of repos), entries will accumulate.
   This is a known limitation. If this becomes an issue, consider:
   - Restarting the process periodically
   - Implementing LRU eviction (would require careful locking semantics)
   - Using weak references (but could cause lock loss during active transactions)"
  (ConcurrentHashMap.))

(defn- normalize-repo-path
  "Normalize a repository path for consistent lock identification.

   Attempts to canonicalize the path (resolving symlinks, normalizing '..' etc).
   Falls back to absolute path if canonicalization fails (e.g., broken symlinks,
   permission issues, or invalid paths).

   The result is always a string with:
   - Resolved symlinks (when possible)
   - Normalized path separators
   - No trailing slashes (except for root '/')

   LIMITATION: On case-insensitive filesystems, paths that differ only in case
   will not be normalized to the same value. This is a known limitation - callers
   should avoid using paths that differ only in case for the same repository."
  [repo-path]
  (when-not repo-path
    (throw (IllegalArgumentException. "Repository path cannot be nil")))
  (let [path-str (str repo-path)
        ;; Try canonicalization first (resolves symlinks, normalizes path)
        normalized (try
                     (str (fs/canonicalize path-str))
                     (catch Exception _
                       ;; Fall back to absolute path if canonicalization fails
                       ;; This handles broken symlinks, permission issues, etc.
                       (str (fs/absolutize path-str))))]
    ;; Remove trailing slash for consistency (except for root "/")
    (if (and (> (count normalized) 1)
             (.endsWith normalized "/"))
      (subs normalized 0 (dec (count normalized)))
      normalized)))

(defn- get-repo-lock
  "Get or create a lock for the given repository path.

   Uses normalized canonical path to ensure consistent locking across:
   - Symlinked paths (resolve to same lock)
   - Paths with different representations (e.g., '/foo/../bar' vs '/bar')
   - Relative vs absolute paths

   Thread-safe: Uses ConcurrentHashMap.computeIfAbsent for atomic lock creation."
  [repo-path]
  (let [normalized (normalize-repo-path repo-path)]
    (.computeIfAbsent repo-locks normalized
                      (reify java.util.function.Function
                        (apply [_ _] (ReentrantLock.))))))

(defn- with-repo-lock
  "Execute f while holding the repository lock.
   Ensures only one transaction runs at a time per repository."
  [repo-path f]
  (let [lock (get-repo-lock repo-path)]
    (.lock lock)
    (try
      (f)
      (finally
        (.unlock lock)))))

;; -----------------------------------------------------------------------------
;; Internal Helpers
;; -----------------------------------------------------------------------------

(defn- alethfeld-dir
  "Get the .alethfeld directory path."
  [repo-path]
  (str repo-path "/.alethfeld"))

(defn- snapshot-files
  "Take a snapshot of all .edn files in .alethfeld/ for potential rollback.
   Returns a map of {file-path -> content-map}."
  [repo-path]
  (let [base (alethfeld-dir repo-path)
        files (io/list-edn-files base :recursive true)]
    (reduce (fn [acc path]
              (if-let [content (io/read-edn path)]
                (assoc acc path content)
                acc))
            {}
            files)))

(defn- restore-snapshot!
  "Restore files from a snapshot.
   Removes any new files not in the snapshot.

   Error handling:
   - Logs and continues on delete failures (best effort cleanup)
   - Uses atomic writes (temp file + rename) for safer restoration
   - Throws on write failures to signal incomplete restoration

   Returns true if all operations succeeded, false if any deletions failed
   (writes that fail throw exceptions)."
  [repo-path snapshot]
  (let [base (alethfeld-dir repo-path)
        current-files (set (io/list-edn-files base :recursive true))
        snapshot-files (set (keys snapshot))
        files-to-delete (clojure.set/difference current-files snapshot-files)
        delete-errors (atom [])]
    ;; Phase 1: Delete files that weren't in the snapshot (best-effort)
    (doseq [path files-to-delete]
      (try
        (let [deleted? (io/delete-file path)]
          (when-not deleted?
            (swap! delete-errors conj {:path path :error "File did not exist or could not be deleted"})))
        (catch Exception e
          (swap! delete-errors conj {:path path :error (.getMessage e)}))))

    ;; Log any delete errors (but continue with restoration)
    (when (seq @delete-errors)
      (binding [*out* *err*]
        (println "Warning: Some files could not be deleted during rollback:")
        (doseq [{:keys [path error]} @delete-errors]
          (println (str "  " path ": " error)))))

    ;; Phase 2: Restore original content using atomic writes
    ;; Write to temp file first, then rename for atomicity
    (doseq [[path content] snapshot]
      (let [temp-path (str path ".tmp." (System/currentTimeMillis))]
        (try
          ;; Write to temp file
          (io/write-edn temp-path content)
          ;; Atomic rename (overwrites existing file)
          (fs/move temp-path path {:replace-existing true})
          (catch Exception e
            ;; Clean up temp file if it exists
            (try (fs/delete-if-exists temp-path) (catch Exception _))
            ;; Re-throw with context - restoration is incomplete
            (throw (ex-info "Failed to restore file during rollback"
                            {:type :restore-failed
                             :path path
                             :cause (.getMessage e)}
                            e))))))

    ;; Return success indicator
    (empty? @delete-errors)))

(defn- ensure-git-config!
  "Ensure git has user config for commits (uses defaults if not set)."
  [repo-path]
  (when-not (git/git-config repo-path "user.name")
    (git/git-config! repo-path "user.name" "alethfeld"))
  (when-not (git/git-config repo-path "user.email")
    (git/git-config! repo-path "user.email" "alethfeld@local")))

;; -----------------------------------------------------------------------------
;; Transaction Core
;; -----------------------------------------------------------------------------

(defn transact!
  "Execute a function within a git transaction.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - f: Function to execute (receives repo-path as argument)

   The function f should perform mote operations using store functions.
   After f completes, all .alethfeld/ changes are staged and committed.

   Thread safety: Uses per-repository locking to serialize transactions.
   Multiple threads can safely call transact! on the same repository.

   Returns map with:
   - :result - Return value of f
   - :commit - Commit info {:sha, :message}

   Throws if f throws (changes are NOT automatically rolled back in this case)."
  [repo-path message f]
  (with-repo-lock repo-path
    (fn []
      ;; Ensure git is initialized
      (when-not (git/git-initialized? repo-path)
        (git/git-init! repo-path))
      (ensure-git-config! repo-path)

      ;; Execute the function
      (let [result (f repo-path)]
        ;; Stage and commit
        (git/git-add-all! repo-path)
        (let [status (git/git-status repo-path)]
          (if (or (seq (:staged status))
                  (not (git/git-has-commits? repo-path)))
            ;; Changes to commit (or first commit)
            (let [commit (if (seq (:staged status))
                           (git/git-commit! repo-path message)
                           (git/git-commit! repo-path message :allow-empty true))]
              {:result result
               :commit commit})
            ;; No changes - still return success but no commit
            {:result result
             :commit nil}))))))

(defn with-validation
  "Execute a function with validation, rolling back on failure.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - f: Function to execute (receives repo-path as argument)

   After f completes:
   1. Loads all motes
   2. Validates the mote graph
   3. If valid: commits changes
   4. If invalid: restores previous state and throws

   Thread safety: Uses per-repository locking to serialize transactions.
   Multiple threads can safely call with-validation on the same repository.

   Returns map with:
   - :result - Return value of f
   - :commit - Commit info {:sha, :message}

   Throws ExceptionInfo with :type :validation-failed if validation fails.

   RACE WINDOW NOTE:
   There is a small window between validation passing and git commit completing
   where changes are written to disk but not yet recorded in git. If the process
   crashes during this window:
   - Files on disk are validated and consistent
   - Git history does not reflect the changes
   - Concurrent agents using `git pull` will not see the changes

   This is an acceptable trade-off because:
   1. The window is typically <100ms for normal operations
   2. Validated changes are not rolled back (data integrity preserved)
   3. Manual recovery is straightforward: run `git add . && git commit -m 'recovery'`
   4. Concurrent access is serialized via per-repository locks

   Future improvements could validate against git index instead of working tree,
   or add startup recovery to detect uncommitted validated changes."
  [repo-path message f]
  (with-repo-lock repo-path
    (fn []
      ;; Ensure git is initialized
      (when-not (git/git-initialized? repo-path)
        (git/git-init! repo-path))
      (ensure-git-config! repo-path)

      ;; Take snapshot before changes
      (let [snapshot (snapshot-files repo-path)]
        ;; Execute function and validate - rollback on failure here
        (let [result (try
                       (f repo-path)
                       (catch Exception e
                         (restore-snapshot! repo-path snapshot)
                         (throw e)))
              ;; Validate the graph (exclude archived - they're historical data)
              motes (store/load-all-motes repo-path)
              validation (dag/validate-mote-graph motes)]
          (if (:valid? validation)
            ;; Valid - commit (no rollback after this point, changes are validated)
            (do
              (git/git-add-all! repo-path)
              (let [status (git/git-status repo-path)]
                (if (seq (:staged status))
                  {:result result
                   :commit (git/git-commit! repo-path message)}
                  {:result result
                   :commit nil})))
            ;; Invalid - rollback and throw
            (do
              (restore-snapshot! repo-path snapshot)
              (throw (ex-info "Validation failed after transaction"
                              {:type :validation-failed
                               :errors (:errors validation)})))))))))

;; -----------------------------------------------------------------------------
;; Atomic Operations
;; -----------------------------------------------------------------------------

(defn atomic-write!
  "Write multiple motes atomically in a single transaction.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - motes: Collection of motes to write

   All motes are written together in a single commit.
   If any write fails, no changes are persisted.

   Options:
   - :validate - If true (default), validate graph after write

   Returns map with:
   - :result - Vector of written mote IDs
   - :commit - Commit info {:sha, :message}"
  [repo-path message motes & {:keys [validate] :or {validate true}}]
  (let [write-fn (fn [repo]
                   (doseq [mote motes]
                     (store/save-mote! repo mote))
                   (mapv :id motes))]
    (if validate
      (with-validation repo-path message write-fn)
      (transact! repo-path message write-fn))))

(defn atomic-delete!
  "Delete multiple motes atomically in a single transaction.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - mote-ids: Collection of mote IDs to delete

   All motes are deleted together in a single commit.

   Options:
   - :validate - If true (default), validate graph after delete

   Returns map with:
   - :result - Vector of {id deleted?} results
   - :commit - Commit info {:sha, :message}"
  [repo-path message mote-ids & {:keys [validate] :or {validate true}}]
  (let [delete-fn (fn [repo]
                    (mapv (fn [id]
                            {:id id
                             :deleted? (store/delete-mote! repo id)})
                          mote-ids))]
    (if validate
      (with-validation repo-path message delete-fn)
      (transact! repo-path message delete-fn))))

(defn atomic-update!
  "Update a mote atomically with validation.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - mote-id: ID of mote to update
   - update-fn: Function that takes the current mote and returns updated mote

   Loads the mote, applies update-fn, validates, and commits.

   Returns map with:
   - :result - The updated mote
   - :commit - Commit info {:sha, :message}

   Throws if mote not found or validation fails."
  [repo-path message mote-id update-fn & {:keys [validate] :or {validate true}}]
  (let [do-update (fn [repo]
                    (let [current (store/load-mote repo mote-id)]
                      (when-not current
                        (throw (ex-info "Mote not found"
                                        {:type :not-found
                                         :mote-id mote-id})))
                      (let [updated (update-fn current)]
                        (store/save-mote! repo updated)
                        updated)))]
    (if validate
      (with-validation repo-path message do-update)
      (transact! repo-path message do-update))))

(defn atomic-write-config!
  "Write config atomically with git commit.

   Arguments:
   - repo-path: Path to the repository
   - message: Git commit message
   - config: Config map to write

   Returns map with:
   - :result - The config that was written
   - :commit - Commit info {:sha, :message}"
  [repo-path message config]
  (transact! repo-path message
             (fn [repo]
               (store/save-config! repo config)
               config)))

;; -----------------------------------------------------------------------------
;; Transaction Status
;; -----------------------------------------------------------------------------

(defn pending-changes?
  "Check if there are uncommitted changes in .alethfeld/.

   Returns true if there are staged, unstaged, or untracked .alethfeld files.
   Returns false if git is not initialized or no changes."
  [repo-path]
  (if (git/git-initialized? repo-path)
    (let [status (git/git-status repo-path)
          alethfeld-file? #(clojure.string/starts-with? % ".alethfeld/")]
      (boolean
       (or (some alethfeld-file? (:staged status))
           (some alethfeld-file? (:unstaged status))
           (some alethfeld-file? (:untracked status)))))
    false))

(defn last-commit
  "Get information about the last commit affecting .alethfeld/.

   Returns map with :sha, :message, :author, :date, or nil if no commits."
  [repo-path]
  (when (and (git/git-initialized? repo-path)
             (git/git-has-commits? repo-path))
    (first (git/git-log repo-path :path ".alethfeld/" :max-count 1 :format :full))))
