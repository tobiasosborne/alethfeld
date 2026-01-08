(ns alethfeld.store
  "Mote persistence layer.

   Provides CRUD operations for motes and config, integrating
   path derivation with EDN I/O."
  (:require [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.schema :as schema]
            [babashka.fs :as fs]
            [malli.core :as m]))

;; -----------------------------------------------------------------------------
;; Path Helpers
;; -----------------------------------------------------------------------------

(defn- full-path
  "Prepend repo-path to a relative path."
  [repo-path relative-path]
  (str repo-path "/" relative-path))

(defn- mote-path
  "Get full path to a mote file.
   Returns nil if mote-id is invalid."
  [repo-path mote-id status]
  (when-let [relative (path/mote-id->path mote-id status)]
    (full-path repo-path relative)))

;; -----------------------------------------------------------------------------
;; Config Operations
;; -----------------------------------------------------------------------------

(defn load-config
  "Load config.edn from a repository.

   Arguments:
   - repo-path: Path to the repository root

   Returns:
   - Config map if file exists and is valid
   - nil if file doesn't exist"
  [repo-path]
  (io/read-edn (full-path repo-path (path/config-path))))

(defn save-config!
  "Save config to a repository.

   Arguments:
   - repo-path: Path to the repository root
   - config: Config map to save

   Creates .alethfeld directory if needed.
   Returns the path written to."
  [repo-path config]
  (let [config-file (full-path repo-path (path/config-path))]
    (io/write-edn config-file config)))

;; -----------------------------------------------------------------------------
;; Single Mote Operations
;; -----------------------------------------------------------------------------

(defn load-mote
  "Load a mote from a repository.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to load

   Searches in order: motes/, proposed/, archive/
   Returns nil if not found or mote-id is invalid."
  [repo-path mote-id]
  (let [statuses [:fixed :proposed :rejected]]
    (some (fn [status]
            (when-let [file-path (mote-path repo-path mote-id status)]
              (io/read-edn file-path)))
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
;; Bulk Load Operations
;; -----------------------------------------------------------------------------

(defn load-all-motes
  "Load all motes from a repository.

   Arguments:
   - repo-path: Path to the repository root

   Options:
   - :include-proposed - Include motes from proposed/ (default: true)
   - :include-archived - Include motes from archive/ (default: false)

   Returns a map of mote-id → mote."
  [repo-path & {:keys [include-proposed include-archived]
                :or {include-proposed true
                     include-archived false}}]
  (let [motes-base (full-path repo-path (path/motes-path))
        proposed-base (full-path repo-path (path/proposed-path))
        archive-base (full-path repo-path (path/archive-path))

        ;; Collect paths from each location
        mote-paths (io/list-edn-files motes-base :recursive true)
        proposed-paths (when include-proposed
                         (io/list-edn-files proposed-base :recursive true))
        archive-paths (when include-archived
                        (io/list-edn-files archive-base :recursive true))

        ;; Combine all paths
        all-paths (concat mote-paths proposed-paths archive-paths)]

    ;; Load each mote and build map
    (reduce (fn [acc file-path]
              (if-let [mote (io/read-edn file-path)]
                (assoc acc (:id mote) mote)
                acc))
            {}
            all-paths)))

;; -----------------------------------------------------------------------------
;; Repository Initialization
;; -----------------------------------------------------------------------------

(def default-config
  "Default configuration for a new repository."
  {:project-name "Unnamed Proof"
   :version "0.1"
   :default-difficulty 3
   :vote-quorum 2
   :proposal-quorum 2
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
    (io/ensure-dir (full-path repo-path (path/motes-path)))
    (io/ensure-dir (full-path repo-path (path/proposed-path)))
    (io/ensure-dir (full-path repo-path (path/archive-path)))
    ;; Write config
    (save-config! repo-path final-config)
    final-config))

(defn repo-exists?
  "Check if an Alethfeld repository exists at the given path."
  [repo-path]
  (io/file-exists? (full-path repo-path (path/config-path))))

;; -----------------------------------------------------------------------------
;; Validation
;; -----------------------------------------------------------------------------

(defn validate-mote
  "Validate a mote against the schema.

   Returns nil if valid, or explanation if invalid."
  [mote]
  (m/explain schema/Mote mote))
