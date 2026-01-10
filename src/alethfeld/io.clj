(ns alethfeld.io
  "EDN file I/O operations.

   All functions are designed to be testable with temp directories.
   File operations are isolated here to keep other namespaces pure.

   Resource Management: This namespace uses Clojure's `slurp` and `spit`
   for file I/O. Both functions properly manage file handles internally:
   - `slurp` uses `with-open` to ensure Readers are closed after reading
   - `spit` uses `with-open` to ensure Writers are closed after writing
   File handles are automatically released even if exceptions occur."
  (:require [babashka.fs :as fs]
            [clojure.edn :as edn]
            [clojure.java.io :as io]))

;; -----------------------------------------------------------------------------
;; Read Operations
;; -----------------------------------------------------------------------------

(defn read-edn
  "Read and parse an EDN file.

   Arguments:
   - path: String or Path to the EDN file

   Returns:
   - Parsed EDN data if file exists and is valid EDN
   - nil if file does not exist or is empty

   Throws:
   - ExceptionInfo with :type :parse-error if file exists but is invalid EDN"
  [path]
  (let [f (fs/file path)]
    (when (fs/exists? f)
      (let [content (slurp f)]
        (when-not (clojure.string/blank? content)
          (try
            (edn/read-string content)
            (catch Exception e
              (throw (ex-info "Failed to parse EDN file"
                              {:type :parse-error
                               :path (str path)
                               :cause (.getMessage e)}
                              e)))))))))

;; -----------------------------------------------------------------------------
;; Write Operations
;; -----------------------------------------------------------------------------

(defn write-edn
  "Write data as EDN to a file.

   Arguments:
   - path: String or Path to the target file
   - data: EDN-serializable data

   Creates parent directories if they don't exist.
   Returns the path that was written to."
  [path data]
  (let [f (fs/file path)
        parent (fs/parent f)]
    ;; Create parent directories if needed
    (when (and parent (not (fs/exists? parent)))
      (fs/create-dirs parent))
    ;; Write the EDN data
    (spit f (pr-str data))
    (str path)))

(defn create-file-exclusive!
  "Create a file atomically, failing if it already exists.

   Uses StandardOpenOption/CREATE_NEW which is atomic on POSIX filesystems.
   This is essential for implementing lock files and preventing race
   conditions in concurrent scenarios.

   Arguments:
   - path: String or Path to the file to create
   - data: EDN-serializable data to write

   Returns:
   - true if file was created successfully
   - false if file already exists

   Throws on other I/O errors (permissions, disk full, etc.)

   Note: Parent directories are created if they don't exist."
  [path data]
  (let [f (fs/file path)
        parent (fs/parent f)]
    (when (and parent (not (fs/exists? parent)))
      (fs/create-dirs parent))
    (try
      (with-open [writer (java.io.BufferedWriter.
                          (java.io.OutputStreamWriter.
                           (java.nio.file.Files/newOutputStream
                            (.toPath f)
                            (into-array java.nio.file.OpenOption
                                        [java.nio.file.StandardOpenOption/CREATE_NEW
                                         java.nio.file.StandardOpenOption/WRITE]))))]
        (.write writer (pr-str data)))
      true
      (catch java.nio.file.FileAlreadyExistsException _
        false))))

;; -----------------------------------------------------------------------------
;; Delete Operations
;; -----------------------------------------------------------------------------

(defn delete-file
  "Delete a file.

   Arguments:
   - path: String or Path to the file to delete

   Returns:
   - true if file was deleted
   - false if file did not exist

   Does not delete directories."
  [path]
  (let [f (fs/file path)]
    (if (and (fs/exists? f) (not (fs/directory? f)))
      (do (fs/delete f) true)
      false)))

;; -----------------------------------------------------------------------------
;; Move Operations
;; -----------------------------------------------------------------------------

(defn move-file
  "Move a file from source to destination.

   Arguments:
   - src: String or Path to the source file
   - dst: String or Path to the destination

   Creates parent directories of destination if needed.
   Returns the destination path.

   Throws:
   - ExceptionInfo with :type :not-found if source doesn't exist"
  [src dst]
  (let [src-f (fs/file src)
        dst-f (fs/file dst)]
    (when-not (fs/exists? src-f)
      (throw (ex-info "Source file not found"
                      {:type :not-found
                       :path (str src)})))
    ;; Create parent directories of destination if needed
    (when-let [parent (fs/parent dst-f)]
      (when-not (fs/exists? parent)
        (fs/create-dirs parent)))
    ;; Move the file
    (fs/move src-f dst-f)
    (str dst)))

;; -----------------------------------------------------------------------------
;; List Operations
;; -----------------------------------------------------------------------------

(defn list-edn-files
  "List all .edn files in a directory.

   Arguments:
   - dir: String or Path to the directory

   Options:
   - :recursive - If true, search recursively (default: false)

   Returns:
   - Vector of file paths (as strings) ending in .edn
   - Empty vector if directory doesn't exist"
  [dir & {:keys [recursive] :or {recursive false}}]
  (let [d (fs/file dir)]
    (if (and (fs/exists? d) (fs/directory? d))
      (let [files (if recursive
                    ;; Use ** to match any depth, including root
                    (concat (fs/glob d "*.edn")
                            (fs/glob d "**/*.edn"))
                    (fs/glob d "*.edn"))]
        (->> files
             (map str)
             (distinct)
             (sort)
             vec))
      [])))

;; -----------------------------------------------------------------------------
;; Utility Functions
;; -----------------------------------------------------------------------------

(defn file-exists?
  "Check if a file exists.

   Arguments:
   - path: String or Path to check

   Returns true if path exists and is a regular file."
  [path]
  (let [f (fs/file path)]
    (and (fs/exists? f) (not (fs/directory? f)))))

(defn dir-exists?
  "Check if a directory exists.

   Arguments:
   - path: String or Path to check

   Returns true if path exists and is a directory."
  [path]
  (let [d (fs/file path)]
    (and (fs/exists? d) (fs/directory? d))))

(defn ensure-dir
  "Ensure a directory exists, creating it if necessary.

   Arguments:
   - path: String or Path to the directory

   Returns the path."
  [path]
  (let [d (fs/file path)]
    (when-not (fs/exists? d)
      (fs/create-dirs d))
    (str path)))

(defn full-path
  "Join repo path with relative path using forward slash separator."
  [repo-path relative-path]
  (str repo-path "/" relative-path))
