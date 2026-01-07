(ns alethfeld.io
  "EDN I/O with atomic writes for semantic proof graphs."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.string :as str]))

;; =============================================================================
;; Reading
;; =============================================================================

(defn read-edn
  "Read and parse EDN from a file.
   Returns {:ok data} or {:error message}."
  [path]
  (try
    (let [file (io/file path)]
      (if-not (.exists file)
        {:error (str "File not found: " path)}
        (let [content (slurp file)]
          (if (str/blank? content)
            {:error (str "Empty file: " path)}
            (let [parsed (edn/read-string content)]
              (if (nil? parsed)
                {:error "Failed to parse EDN: file contains nil or is invalid"}
                {:ok parsed}))))))
    (catch Exception e
      {:error (str "Failed to parse EDN: " (.getMessage e))})))

(defn read-graph
  "Read a semantic proof graph from an EDN file.
   Returns {:ok graph} or {:error message}."
  [path]
  (read-edn path))

(defn read-node-edn
  "Read a node definition from an EDN file.
   Returns {:ok node} or {:error message}."
  [path]
  (read-edn path))

;; =============================================================================
;; Writing
;; =============================================================================

(defn format-edn-compact
  "Format data as compact EDN string (no pretty-printing).
   Faster than pretty-print, suitable for machine consumption."
  [data]
  (with-out-str (pr data)))

(defn format-edn-pretty
  "Pretty-print data as EDN string.
   Human-readable but slower for large structures."
  [data]
  (with-out-str (pprint/pprint data)))

(defn format-edn
  "Pretty-print data as EDN string.
   Alias for format-edn-pretty for backwards compatibility."
  [data]
  (format-edn-pretty data))

(defn write-edn-atomic
  "Write data to file atomically (write temp, then rename).
   Returns {:ok path} or {:error message}."
  [path data]
  (try
    (let [file (io/file path)
          parent (.getParentFile file)
          temp-file (java.io.File/createTempFile "alethfeld-" ".edn.tmp" parent)]
      (try
        ;; Write to temp file
        (spit temp-file (format-edn data))
        ;; Atomic rename
        (let [success (.renameTo temp-file file)]
          (if success
            {:ok path}
            ;; Fallback for cross-filesystem moves
            (do
              (io/copy temp-file file)
              (.delete temp-file)
              {:ok path})))
        (catch Exception e
          (.delete temp-file)
          (throw e))))
    (catch Exception e
      {:error (str "Failed to write file: " (.getMessage e))})))

(defn write-graph
  "Write a semantic proof graph to an EDN file atomically.
   Returns {:ok path} or {:error message}."
  [path graph]
  (write-edn-atomic path graph))

;; =============================================================================
;; Stdin Reading
;; =============================================================================

(defn read-edn-stdin
  "Read EDN from stdin.
   Returns {:ok data} or {:error message}."
  []
  (try
    (let [content (slurp *in*)]
      (if (str/blank? content)
        {:error "Empty input from stdin"}
        (let [parsed (edn/read-string content)]
          (if (nil? parsed)
            {:error "Failed to parse EDN from stdin: invalid data"}
            {:ok parsed}))))
    (catch Exception e
      {:error (str "Failed to read from stdin: " (.getMessage e))})))

;; =============================================================================
;; Output Formatting
;; =============================================================================

(defn format-success
  "Format a success result for CLI output."
  [message & {:keys [graph-version data]}]
  (cond-> {:status :ok
           :message message}
    graph-version (assoc :graph-version graph-version)
    data (assoc :data data)))

(defn format-error
  "Format an error result for CLI output."
  [errors]
  {:status :error
   :errors (if (sequential? errors) errors [errors])})
