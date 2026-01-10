(ns alethfeld.manifest
  "Manifest system for scalable mote indexing.

   Instead of scanning all mote files on every operation, the manifest
   maintains indices by status, priority, and taint for O(1) lookups.

   The manifest is stored at .alethfeld/manifest.edn and is git-ignored
   since it can be rebuilt from the source mote files at any time.

   Structure:
     {:version 1
      :updated-at <timestamp>
      :motes-by-id {\"1\" {:status :fixed :priority :p2 :taint #{:needs-verification} ...}
                    \"1.1\" {:status :proposed ...}}
      :motes-by-status {:fixed #{\"1\" \"2\"}
                        :proposed #{\"1.1\"}}
      :motes-by-priority {:p0 #{\"urgent\"}
                          :p2 #{\"1\" \"1.1\"}}
      :motes-by-taint {:needs-verification #{\"1\" \"1.1\"}
                       :needs-decomposition #{\"2\"}}}"
  (:require [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.store :as store]
            [babashka.fs :as fs]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const manifest-file "manifest.edn")
(def ^:const manifest-version 1)

;; -----------------------------------------------------------------------------
;; Path Helpers
;; -----------------------------------------------------------------------------

(defn manifest-path
  "Return the path to the manifest file.

   Example: (manifest-path) => \".alethfeld/manifest.edn\""
  []
  (str path/alethfeld-dir "/" manifest-file))

(defn- full-manifest-path
  "Get full path to manifest file for a repository."
  [repo-path]
  (io/full-path repo-path (manifest-path)))

;; -----------------------------------------------------------------------------
;; Mote Summary Extraction
;; -----------------------------------------------------------------------------

(defn mote->summary
  "Extract indexable fields from a mote for the manifest.

   Returns a map with:
   - :status - The mote's lifecycle status
   - :priority - The mote's priority level
   - :taint - Set of taint flags
   - :difficulty - Difficulty level (1-5)
   - :parent - Parent mote ID (if any)
   - :children - Vector of child IDs
   - :claimed-by - Agent with active claim (if any)
   - :updated-at - Last update timestamp"
  [mote]
  (let [fields [:status :priority :taint :difficulty :parent
                :children :claimed-by :updated-at]]
    (select-keys mote fields)))

;; -----------------------------------------------------------------------------
;; Index Building
;; -----------------------------------------------------------------------------

(defn- add-to-set-index
  "Add a mote-id to a set-based index (e.g., motes-by-status).

   Creates the set if it doesn't exist."
  [index key mote-id]
  (update index key (fnil conj #{}) mote-id))

(defn- remove-from-set-index
  "Remove a mote-id from a set-based index.

   Removes the key entirely if the set becomes empty."
  [index key mote-id]
  (let [updated (update index key disj mote-id)]
    (if (empty? (get updated key))
      (dissoc updated key)
      updated)))

(defn- build-indices-from-summaries
  "Build the by-status, by-priority, and by-taint indices from motes-by-id."
  [motes-by-id]
  (reduce-kv
   (fn [indices mote-id summary]
     (let [{:keys [status priority taint]} summary]
       (-> indices
           (update :motes-by-status add-to-set-index status mote-id)
           (update :motes-by-priority add-to-set-index priority mote-id)
           ;; Add to each taint flag's index
           (update :motes-by-taint
                   (fn [taint-index]
                     (reduce (fn [idx t]
                               (add-to-set-index idx t mote-id))
                             taint-index
                             taint))))))
   {:motes-by-status {}
    :motes-by-priority {}
    :motes-by-taint {}}
   motes-by-id))

;; -----------------------------------------------------------------------------
;; Manifest Construction
;; -----------------------------------------------------------------------------

(defn- now-timestamp
  "Get current timestamp for manifest updates."
  []
  (java.util.Date.))

(defn create-manifest
  "Create a new manifest from a map of mote-id -> mote.

   Arguments:
   - motes: Map of mote-id to full mote data

   Returns a complete manifest structure with all indices built."
  [motes]
  (let [motes-by-id (reduce-kv
                     (fn [acc mote-id mote]
                       (assoc acc mote-id (mote->summary mote)))
                     {}
                     motes)
        indices (build-indices-from-summaries motes-by-id)]
    {:version manifest-version
     :updated-at (now-timestamp)
     :motes-by-id motes-by-id
     :motes-by-status (:motes-by-status indices)
     :motes-by-priority (:motes-by-priority indices)
     :motes-by-taint (:motes-by-taint indices)}))

(defn empty-manifest
  "Create an empty manifest with proper structure."
  []
  {:version manifest-version
   :updated-at (now-timestamp)
   :motes-by-id {}
   :motes-by-status {}
   :motes-by-priority {}
   :motes-by-taint {}})

;; -----------------------------------------------------------------------------
;; Persistence
;; -----------------------------------------------------------------------------

(defn load-manifest
  "Load the manifest from a repository.

   Arguments:
   - repo-path: Path to the repository root

   Returns:
   - Manifest map if file exists and is valid
   - nil if file doesn't exist"
  [repo-path]
  (io/read-edn (full-manifest-path repo-path)))

(defn save-manifest!
  "Save the manifest to a repository.

   Arguments:
   - repo-path: Path to the repository root
   - manifest: Manifest map to save

   Creates .alethfeld directory if needed.
   Returns the path written to."
  [repo-path manifest]
  (let [updated-manifest (assoc manifest :updated-at (now-timestamp))]
    (io/write-edn (full-manifest-path repo-path) updated-manifest)))

(defn rebuild-manifest!
  "Rebuild the manifest from scratch by scanning all mote files.

   Arguments:
   - repo-path: Path to the repository root

   Options:
   - :include-proposed - Include proposed motes (default: true)
   - :include-archived - Include archived motes (default: false)

   Loads all motes and builds fresh indices. Use when manifest is
   missing, corrupted, or suspected to be out of sync.

   Returns the new manifest."
  [repo-path & {:keys [include-proposed include-archived]
                :or {include-proposed true
                     include-archived false}}]
  (let [motes (store/load-all-motes repo-path
                                     :include-proposed include-proposed
                                     :include-archived include-archived)
        manifest (create-manifest motes)]
    (save-manifest! repo-path manifest)
    manifest))

;; -----------------------------------------------------------------------------
;; Incremental Updates
;; -----------------------------------------------------------------------------

(defn update-manifest-entry
  "Update a single mote entry in the manifest (pure function).

   Arguments:
   - manifest: Current manifest
   - mote-id: ID of the mote to update
   - mote: Full mote data (or nil to remove)

   Returns updated manifest with all indices refreshed."
  [manifest mote-id mote]
  (let [old-summary (get-in manifest [:motes-by-id mote-id])
        new-summary (when mote (mote->summary mote))]
    (if (and (nil? old-summary) (nil? new-summary))
      ;; No change needed
      manifest
      ;; Update the manifest
      (let [;; Remove old entry from indices (if exists)
            manifest-without-old
            (if old-summary
              (let [{:keys [status priority taint]} old-summary]
                (-> manifest
                    (update :motes-by-status remove-from-set-index status mote-id)
                    (update :motes-by-priority remove-from-set-index priority mote-id)
                    (update :motes-by-taint
                            (fn [idx]
                              (reduce (fn [i t]
                                        (remove-from-set-index i t mote-id))
                                      idx
                                      taint)))))
              manifest)
            ;; Add new entry to indices (if exists)
            manifest-with-new
            (if new-summary
              (let [{:keys [status priority taint]} new-summary]
                (-> manifest-without-old
                    (assoc-in [:motes-by-id mote-id] new-summary)
                    (update :motes-by-status add-to-set-index status mote-id)
                    (update :motes-by-priority add-to-set-index priority mote-id)
                    (update :motes-by-taint
                            (fn [idx]
                              (reduce (fn [i t]
                                        (add-to-set-index i t mote-id))
                                      idx
                                      taint)))))
              (update manifest-without-old :motes-by-id dissoc mote-id))]
        (assoc manifest-with-new :updated-at (now-timestamp))))))

(defn update-manifest!
  "Update a single mote in the manifest (persisted).

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: ID of the mote that changed
   - mote: The updated mote (or nil if deleted)

   Loads current manifest, applies incremental update, saves.
   Creates manifest if it doesn't exist.

   Returns the updated manifest."
  [repo-path mote-id mote]
  (let [current (or (load-manifest repo-path) (empty-manifest))
        updated (update-manifest-entry current mote-id mote)]
    (save-manifest! repo-path updated)
    updated))

;; -----------------------------------------------------------------------------
;; Query Functions
;; -----------------------------------------------------------------------------

(defn motes-by-status
  "Get all mote IDs with a given status.

   Arguments:
   - manifest: The manifest to query
   - status: Status keyword (:fixed, :proposed, :verified, etc.)

   Returns a set of mote IDs, or empty set if none."
  [manifest status]
  (get-in manifest [:motes-by-status status] #{}))

(defn motes-by-priority
  "Get all mote IDs with a given priority.

   Arguments:
   - manifest: The manifest to query
   - priority: Priority keyword (:p0, :p1, :p2, :p3, :p4)

   Returns a set of mote IDs, or empty set if none."
  [manifest priority]
  (get-in manifest [:motes-by-priority priority] #{}))

(defn motes-by-taint
  "Get all mote IDs with a given taint flag.

   Arguments:
   - manifest: The manifest to query
   - taint: Taint keyword (:needs-verification, :needs-decomposition, etc.)

   Returns a set of mote IDs, or empty set if none."
  [manifest taint]
  (get-in manifest [:motes-by-taint taint] #{}))

(defn mote-summary
  "Get the summary for a specific mote.

   Arguments:
   - manifest: The manifest to query
   - mote-id: The mote ID to look up

   Returns summary map or nil if not found."
  [manifest mote-id]
  (get-in manifest [:motes-by-id mote-id]))

(defn mote-ids
  "Get all mote IDs in the manifest.

   Arguments:
   - manifest: The manifest to query

   Returns a set of all mote IDs."
  [manifest]
  (set (keys (:motes-by-id manifest))))

(defn mote-count
  "Get the total number of motes in the manifest."
  [manifest]
  (count (:motes-by-id manifest)))

;; -----------------------------------------------------------------------------
;; Staleness Detection
;; -----------------------------------------------------------------------------

(defn- get-mtime
  "Get modification time of a file as epoch milliseconds.
   Returns nil if file doesn't exist."
  [path]
  (when (fs/exists? path)
    (.toMillis (fs/last-modified-time path))))

(defn- latest-mote-mtime
  "Find the latest modification time among all mote files."
  [repo-path]
  (let [motes-base (io/full-path repo-path (path/motes-path))
        proposed-base (io/full-path repo-path (path/proposed-path))
        all-paths (concat (io/list-edn-files motes-base :recursive true)
                          (io/list-edn-files proposed-base :recursive true))]
    (when (seq all-paths)
      (apply max (map get-mtime all-paths)))))

(defn manifest-stale?
  "Check if the manifest needs rebuilding.

   Arguments:
   - repo-path: Path to the repository root

   Options:
   - :manifest - Pre-loaded manifest (avoids re-reading file)

   Returns true if:
   - Manifest file doesn't exist
   - Any mote file is newer than the manifest
   - Manifest version is outdated

   Returns false if manifest is up to date."
  [repo-path & {:keys [manifest]}]
  (let [manifest-file (full-manifest-path repo-path)
        m (or manifest (load-manifest repo-path))]
    (cond
      ;; No manifest file
      (not (fs/exists? manifest-file))
      true

      ;; No manifest data (file empty or parse error)
      (nil? m)
      true

      ;; Wrong version
      (not= manifest-version (:version m))
      true

      ;; Check mtimes - any mote newer than manifest?
      :else
      (let [manifest-mtime (get-mtime manifest-file)
            latest-mote (latest-mote-mtime repo-path)]
        (boolean
         (and manifest-mtime
              latest-mote
              (> latest-mote manifest-mtime)))))))

(defn ensure-manifest!
  "Ensure a valid, up-to-date manifest exists.

   Arguments:
   - repo-path: Path to the repository root

   If manifest is missing or stale, rebuilds it.
   Returns the manifest (loaded or rebuilt)."
  [repo-path]
  (if (manifest-stale? repo-path)
    (rebuild-manifest! repo-path)
    (load-manifest repo-path)))
