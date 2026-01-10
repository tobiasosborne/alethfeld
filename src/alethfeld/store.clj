(ns alethfeld.store
  "Mote persistence layer.

   Provides CRUD operations for motes and config, integrating
   path derivation with EDN I/O."
  (:require [alethfeld.errors :as err]
            [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.schema :as schema]
            [babashka.fs :as fs]
            [malli.core :as m]))

;; -----------------------------------------------------------------------------
;; Caching Support
;; -----------------------------------------------------------------------------

(def ^:dynamic *motes-cache*
  "Dynamic var for command-scoped mote caching.
   When bound to an atom, load-all-motes will cache results.

   Usage:
     (binding [*motes-cache* (atom nil)]
       (cmd-ready ...)  ; All calls share cache within this scope)

   Set to nil (default) to disable caching."
  nil)

(defmacro with-motes-cache
  "Execute body with motes caching enabled.

   All calls to load-all-motes within body will share a cache,
   avoiding redundant file I/O for commands that call it multiple times.

   Example:
     (with-motes-cache
       (let [motes1 (load-all-motes repo)   ; Reads from disk
             motes2 (load-all-motes repo)]  ; Returns cached result
         ...))

   Note: Cache is invalidated if options change (e.g., include-archived)."
  [& body]
  `(binding [*motes-cache* (atom nil)]
     ~@body))

;; -----------------------------------------------------------------------------
;; Path Helpers
;; -----------------------------------------------------------------------------

(defn- mote-path
  "Get full path to a mote file.
   Returns nil if mote-id is invalid."
  [repo-path mote-id status]
  (when-let [relative (path/mote-id->path mote-id status)]
    (io/full-path repo-path relative)))

;; -----------------------------------------------------------------------------
;; Config Operations
;; -----------------------------------------------------------------------------

(defn- format-config-error
  "Format a Malli validation error into a human-readable string."
  [{:keys [path value] :as error}]
  (let [field-path (if (seq path)
                     (str (name (first path))
                          (when (> (count path) 1)
                            (str " > " (name (second path)))))
                     "config")]
    (cond
      ;; Missing required field
      (nil? value)
      (str "Missing required field: " field-path)

      ;; Wrong type
      (keyword? value)
      (str field-path ": expected a different type, got " (pr-str value))

      ;; Value out of range (e.g., difficulty 1-5)
      (number? value)
      (str field-path ": invalid value " value
           (when (= (first path) :default-difficulty)
             " (must be 1-5)"))

      ;; Generic error
      :else
      (str field-path ": invalid value " (pr-str value)))))

(defn- explain-config-errors
  "Convert Malli explain result into a list of human-readable error strings."
  [explain-result]
  (when explain-result
    (let [errors (:errors explain-result)]
      (mapv format-config-error errors))))

(defn validate-config
  "Validate a config against the schema.

   Returns nil if valid, or explanation if invalid."
  [config]
  (m/explain schema/Config config))

(defn load-config
  "Load config.edn from a repository.

   Arguments:
   - repo-path: Path to the repository root

   Options:
   - :validate - Run schema validation (default: false for backward compatibility).
                 Set to true at CLI entry points after user provides config.

   Returns:
   - Config map if file exists and is valid
   - nil if file doesn't exist

   Throws:
   - ExceptionInfo with :type :invalid-config if validation fails and :validate is true"
  [repo-path & {:keys [validate] :or {validate false}}]
  (let [config-file (io/full-path repo-path (path/config-path))
        config (io/read-edn config-file)]
    (when config
      (if validate
        (if-let [explain-result (m/explain schema/Config config)]
          (err/throw-error :invalid-config
                           "Invalid configuration"
                           {:path config-file
                            :errors (explain-config-errors explain-result)})
          config)
        config))))

(defn save-config!
  "Save config to a repository.

   Arguments:
   - repo-path: Path to the repository root
   - config: Config map to save

   Creates .alethfeld directory if needed.
   Returns the path written to."
  [repo-path config]
  (let [config-file (io/full-path repo-path (path/config-path))]
    (io/write-edn config-file config)))

;; -----------------------------------------------------------------------------
;; Single Mote Operations
;; -----------------------------------------------------------------------------

(defn load-mote
  "Load a mote from a repository.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to load

   Options:
   - :validate - Run schema validation (default: true). Set to false for
                 trusted reads to improve performance on large repositories.

   Searches in order: motes/, proposed/, archive/
   Returns nil if not found, mote-id is invalid, or mote fails schema validation."
  [repo-path mote-id & {:keys [validate] :or {validate true}}]
  (let [statuses [:fixed :proposed :rejected]]
    (some (fn [status]
            (when-let [file-path (mote-path repo-path mote-id status)]
              (when-let [mote (io/read-edn file-path)]
                ;; Only return mote if validation is disabled or it passes schema
                (when (or (not validate) (m/validate schema/Mote mote))
                  mote))))
          statuses)))

(defn save-mote!
  "Save a mote to a repository.

   Arguments:
   - repo-path: Path to the repository root
   - mote: The mote map to save

   Writes to the appropriate location based on mote status.
   Returns the path written to."
  [repo-path mote]
  (let [mote-id (:id mote)
        status (:status mote)
        file-path (mote-path repo-path mote-id status)]
    (io/write-edn file-path mote)))

(defn delete-mote!
  "Delete a mote from a repository.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to delete

   Searches in all locations (motes/, proposed/, archive/).
   Returns true if deleted, false if not found or invalid ID."
  [repo-path mote-id]
  (let [statuses [:fixed :proposed :rejected]]
    (boolean
     (some (fn [status]
             (when-let [file-path (mote-path repo-path mote-id status)]
               (when (io/file-exists? file-path)
                 (io/delete-file file-path))))
           statuses))))

(defn move-mote!
  "Move a mote to a new status location.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to move
   - new-status: The new status (:fixed, :proposed, :rejected)

   Loads the mote, updates its status, and moves the file.
   Returns the new path, or nil if mote not found."
  [repo-path mote-id new-status]
  (when-let [mote (load-mote repo-path mote-id)]
    (let [old-status (:status mote)
          old-path (mote-path repo-path mote-id old-status)
          new-path (mote-path repo-path mote-id new-status)
          updated-mote (assoc mote :status new-status)]
      ;; Write to new location with updated status
      (io/write-edn new-path updated-mote)
      ;; Delete from old location (if different)
      (when (not= old-path new-path)
        (io/delete-file old-path))
      new-path)))

;; -----------------------------------------------------------------------------
;; Batch Load Operations
;; -----------------------------------------------------------------------------

(defn load-motes
  "Batch load multiple motes by ID, returning a map of id->mote.

   Arguments:
   - repo-path: Path to the repository root
   - mote-ids: Collection of mote IDs to load

   Options:
   - :validate - Run schema validation (default: true). Set to false for
                 trusted reads to improve performance on large repositories.

   Returns a map of {mote-id -> mote} for motes that exist.
   Missing motes are not included in the result map.

   Performance: This function avoids N+1 query patterns by loading all
   motes in a single pass through the filesystem, using the existing
   load-all-motes cache when available."
  [repo-path mote-ids & {:keys [validate] :or {validate true}}]
  (if (empty? mote-ids)
    {}
    ;; Strategy: If cache is available, use it. Otherwise, load individually.
    (if (and *motes-cache* @*motes-cache*)
      ;; Cache hit - filter from cached motes
      (let [cached-motes (:motes @*motes-cache*)]
        (reduce (fn [acc id]
                  (if-let [mote (get cached-motes id)]
                    (assoc acc id mote)
                    acc))
                {}
                mote-ids))
      ;; No cache - load motes individually
      (reduce (fn [acc id]
                (if-let [mote (load-mote repo-path id :validate validate)]
                  (assoc acc id mote)
                  acc))
              {}
              mote-ids))))

;; -----------------------------------------------------------------------------
;; Bulk Load Operations
;; -----------------------------------------------------------------------------

(defn- load-all-motes-impl
  "Internal implementation of load-all-motes (no caching)."
  [repo-path {:keys [include-proposed include-archived validate]
              :or {include-proposed true
                   include-archived false
                   validate true}}]
  (let [motes-base (io/full-path repo-path (path/motes-path))
        proposed-base (io/full-path repo-path (path/proposed-path))
        archive-base (io/full-path repo-path (path/archive-path))

        ;; Collect paths from each location
        mote-paths (io/list-edn-files motes-base :recursive true)
        proposed-paths (when include-proposed
                         (io/list-edn-files proposed-base :recursive true))
        archive-paths (when include-archived
                        (io/list-edn-files archive-base :recursive true))

        ;; Combine all paths
        all-paths (concat mote-paths proposed-paths archive-paths)]

    ;; Load each mote and build map (skip invalid motes when validating)
    (reduce (fn [acc file-path]
              (if-let [mote (io/read-edn file-path)]
                (if (or (not validate) (m/validate schema/Mote mote))
                  (assoc acc (:id mote) mote)
                  acc)  ; Skip invalid motes
                acc))
            {}
            all-paths)))

(defn load-all-motes
  "Load all motes from a repository.

   Arguments:
   - repo-path: Path to the repository root

   Options:
   - :include-proposed - Include motes from proposed/ (default: true)
   - :include-archived - Include motes from archive/ (default: false)
   - :validate - Run schema validation on each mote (default: true).
                 Set to false for trusted reads to improve performance.
   - :use-cache - Use *motes-cache* if bound (default: true).
                  Set to false to force a fresh load.

   Caching:
   When *motes-cache* is bound to an atom, results are cached for the
   duration of that binding. Useful for commands that call load-all-motes
   multiple times.

   Returns a map of mote-id → mote."
  [repo-path & {:keys [include-proposed include-archived validate use-cache]
                :or {include-proposed true
                     include-archived false
                     validate true
                     use-cache true}
                :as opts}]
  (let [cache-key {:repo-path repo-path
                   :include-proposed include-proposed
                   :include-archived include-archived
                   :validate validate}]
    (if (and use-cache *motes-cache*)
      ;; Cache is enabled and bound
      (let [cached @*motes-cache*]
        (if (and cached (= (:cache-key cached) cache-key))
          ;; Cache hit - return cached motes
          (:motes cached)
          ;; Cache miss - load, cache, and return
          (let [motes (load-all-motes-impl repo-path opts)]
            (reset! *motes-cache* {:cache-key cache-key :motes motes})
            motes)))
      ;; No caching - load directly
      (load-all-motes-impl repo-path opts))))

;; -----------------------------------------------------------------------------
;; Repository Initialization
;; -----------------------------------------------------------------------------

(def default-config
  "Default configuration for a new repository."
  {:project-name "Unnamed Proof"
   :version "0.1"
   :default-difficulty 3
   :vote-quorum 1
   :proposal-quorum 1
   :claim-timeout-minutes 30})

(defn init-repo!
  "Initialize a new Alethfeld repository.

   Arguments:
   - repo-path: Path to initialize

   Options:
   - :project-name - Name of the project
   - :config - Full config map (overrides project-name)

   Creates .alethfeld/ directory structure and config.edn.
   Returns the config that was written."
  [repo-path & {:keys [project-name config]}]
  (let [final-config (or config
                         (if project-name
                           (assoc default-config :project-name project-name)
                           default-config))]
    ;; Create directories
    (io/ensure-dir (io/full-path repo-path (path/motes-path)))
    (io/ensure-dir (io/full-path repo-path (path/proposed-path)))
    (io/ensure-dir (io/full-path repo-path (path/archive-path)))
    ;; Write config
    (save-config! repo-path final-config)
    final-config))

(defn repo-exists?
  "Check if an Alethfeld repository exists at the given path."
  [repo-path]
  (io/file-exists? (io/full-path repo-path (path/config-path))))

;; -----------------------------------------------------------------------------
;; Validation
;; -----------------------------------------------------------------------------

(defn validate-mote
  "Validate a mote against the schema.

   Returns nil if valid, or explanation if invalid."
  [mote]
  (m/explain schema/Mote mote))
