(ns alethfeld.tx
  "Transaction layer for git-backed ACID operations.

   Provides atomic, validated operations that wrap mote changes
   in git commits with automatic rollback on validation failure."
  (:require [alethfeld.git :as git]
            [alethfeld.store :as store]
            [alethfeld.dag :as dag]
            [alethfeld.io :as io]
            [babashka.fs :as fs]))

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
   Removes any new files not in the snapshot."
  [repo-path snapshot]
  (let [base (alethfeld-dir repo-path)
        current-files (set (io/list-edn-files base :recursive true))
        snapshot-files (set (keys snapshot))]
    ;; Delete files that weren't in the snapshot
    (doseq [path (clojure.set/difference current-files snapshot-files)]
      (io/delete-file path))
    ;; Restore original content
    (doseq [[path content] snapshot]
      (io/write-edn path content))))

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

   Returns map with:
   - :result - Return value of f
   - :commit - Commit info {:sha, :message}

   Throws if f throws (changes are NOT automatically rolled back in this case)."
  [repo-path message f]
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
         :commit nil}))))

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

   Returns map with:
   - :result - Return value of f
   - :commit - Commit info {:sha, :message}

   Throws ExceptionInfo with :type :validation-failed if validation fails.
   Note: Once validation passes, git failures do NOT trigger rollback
   (validated changes are preserved on disk for manual recovery)."
  [repo-path message f]
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
          ;; Validate the graph
          motes (store/load-all-motes repo-path :include-archived true)
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
                           :errors (:errors validation)})))))))

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
