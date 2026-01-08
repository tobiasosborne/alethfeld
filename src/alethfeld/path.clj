(ns alethfeld.path
  "Path derivation functions for mote file locations.

   Motes are stored in .alethfeld/motes/ with a hierarchical directory structure.
   Proposed motes go in .alethfeld/proposed/.
   Rejected motes are archived in .alethfeld/archive/."
  (:require [clojure.string :as str]
            [alethfeld.id :as id]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const alethfeld-dir ".alethfeld")
(def ^:const motes-dir "motes")
(def ^:const proposed-dir "proposed")
(def ^:const archive-dir "archive")
(def ^:const sessions-dir "sessions")
(def ^:const active-sessions-dir "active")
(def ^:const completed-sessions-dir "completed")
(def ^:const config-file "config.edn")

;; -----------------------------------------------------------------------------
;; Base Paths
;; -----------------------------------------------------------------------------

(defn config-path
  "Return the path to config.edn.

   Example: (config-path) => \".alethfeld/config.edn\""
  []
  (str alethfeld-dir "/" config-file))

(defn motes-path
  "Return the base path to the motes directory.

   Example: (motes-path) => \".alethfeld/motes\""
  []
  (str alethfeld-dir "/" motes-dir))

(defn proposed-path
  "Return the base path to the proposed directory.

   Example: (proposed-path) => \".alethfeld/proposed\""
  []
  (str alethfeld-dir "/" proposed-dir))

(defn archive-path
  "Return the base path to the archive directory.

   Example: (archive-path) => \".alethfeld/archive\""
  []
  (str alethfeld-dir "/" archive-dir))

;; -----------------------------------------------------------------------------
;; Mote Path Derivation
;; -----------------------------------------------------------------------------

(defn- ancestor-path
  "Build the directory path from ancestor IDs.
   For \"1.2.3\", ancestors are [\"1.2\" \"1\"], reversed to [\"1\" \"1.2\"],
   joined as \"1/1.2\"."
  [mote-id]
  (let [ancestors (id/ancestor-ids mote-id)]
    (when (seq ancestors)
      (str/join "/" (reverse ancestors)))))

(defn mote-id->path
  "Derive file path from mote ID and status.

   For :fixed, :verified, :refuted, :contested status:
     - Root motes: .alethfeld/motes/<id>.edn
     - Children: .alethfeld/motes/<ancestor-path>/<id>.edn

   For :proposed status:
     - .alethfeld/proposed/<id>.edn

   For :rejected status:
     - .alethfeld/archive/<ancestor-path>/<id>.edn

   Examples:
     (mote-id->path \"1\" :fixed)       => \".alethfeld/motes/1.edn\"
     (mote-id->path \"1.2\" :fixed)     => \".alethfeld/motes/1/1.2.edn\"
     (mote-id->path \"1.2.3\" :fixed)   => \".alethfeld/motes/1/1.2/1.2.3.edn\"
     (mote-id->path \"1.2.3\" :proposed) => \".alethfeld/proposed/1.2.3.edn\"
     (mote-id->path \"1.2.3\" :rejected) => \".alethfeld/archive/1/1.2/1.2.3.edn\""
  [mote-id status]
  (when (id/valid-id? mote-id)
    (let [filename (str mote-id ".edn")
          anc-path (ancestor-path mote-id)]
      (case status
        :proposed
        (str (proposed-path) "/" filename)

        :rejected
        (if anc-path
          (str (archive-path) "/" anc-path "/" filename)
          (str (archive-path) "/" filename))

        ;; Default: :fixed, :verified, :refuted, :contested
        (if anc-path
          (str (motes-path) "/" anc-path "/" filename)
          (str (motes-path) "/" filename))))))

(defn path->mote-id
  "Extract mote ID from a file path.

   Examples:
     (path->mote-id \".alethfeld/motes/1.edn\")         => \"1\"
     (path->mote-id \".alethfeld/motes/1/1.2.edn\")     => \"1.2\"
     (path->mote-id \".alethfeld/proposed/1.2.3.edn\")  => \"1.2.3\"
     (path->mote-id \"/abs/path/.alethfeld/motes/1.edn\") => \"1\"

   Returns nil if the path doesn't match expected patterns."
  [path]
  (when (string? path)
    ;; Extract filename, remove .edn extension
    (when-let [match (re-find #"([^/]+)\.edn$" path)]
      (let [candidate (second match)]
        (when (id/valid-id? candidate)
          candidate)))))

(defn path->status
  "Infer status from a file path.

   Examples:
     (path->status \".alethfeld/motes/1.edn\")    => :fixed
     (path->status \".alethfeld/proposed/1.edn\") => :proposed
     (path->status \".alethfeld/archive/1.edn\")  => :rejected

   Returns nil if status cannot be determined."
  [path]
  (when (string? path)
    (cond
      (str/includes? path (str "/" proposed-dir "/")) :proposed
      (str/includes? path (str "/" archive-dir "/")) :rejected
      (str/includes? path (str "/" motes-dir "/")) :fixed
      :else nil)))

;; -----------------------------------------------------------------------------
;; Directory Derivation
;; -----------------------------------------------------------------------------

(defn mote-dir
  "Return the directory where a mote's children would be stored.

   Examples:
     (mote-dir \"1\")   => \".alethfeld/motes/1\"
     (mote-dir \"1.2\") => \".alethfeld/motes/1/1.2\""
  [mote-id]
  (when (id/valid-id? mote-id)
    (let [anc-path (ancestor-path mote-id)]
      (if anc-path
        (str (motes-path) "/" anc-path "/" mote-id)
        (str (motes-path) "/" mote-id)))))

(defn parent-dir
  "Return the directory containing a mote file.

   Examples:
     (parent-dir \"1\")     => \".alethfeld/motes\"
     (parent-dir \"1.2\")   => \".alethfeld/motes/1\"
     (parent-dir \"1.2.3\") => \".alethfeld/motes/1/1.2\""
  [mote-id]
  (when (id/valid-id? mote-id)
    (let [anc-path (ancestor-path mote-id)]
      (if anc-path
        (str (motes-path) "/" anc-path)
        (motes-path)))))

;; -----------------------------------------------------------------------------
;; Session Paths
;; -----------------------------------------------------------------------------

(defn sessions-base-path
  "Return the base path to the sessions directory.

   Example: (sessions-base-path) => \".alethfeld/sessions\""
  []
  (str alethfeld-dir "/" sessions-dir))

(defn active-sessions-path
  "Return the path to the active sessions directory.

   Example: (active-sessions-path) => \".alethfeld/sessions/active\""
  []
  (str (sessions-base-path) "/" active-sessions-dir))

(defn completed-sessions-path
  "Return the path to the completed sessions directory.

   Example: (completed-sessions-path) => \".alethfeld/sessions/completed\""
  []
  (str (sessions-base-path) "/" completed-sessions-dir))

(defn session-path
  "Return the file path for a session.

   Examples:
     (session-path \"abc-123\" :active)    => \".alethfeld/sessions/active/abc-123.edn\"
     (session-path \"abc-123\" :completed) => \".alethfeld/sessions/completed/abc-123.edn\""
  [session-id status]
  (let [base (case status
               :active (active-sessions-path)
               :completed (completed-sessions-path))]
    (str base "/" session-id ".edn")))
