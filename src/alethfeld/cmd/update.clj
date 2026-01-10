(ns alethfeld.cmd.update
  "Update command implementation."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Update Command
;; -----------------------------------------------------------------------------

(def ^:private valid-priorities
  "Valid priority values."
  #{:p0 :p1 :p2 :p3 :p4})

(defn- parse-priority
  "Parse priority string to keyword. Returns nil if invalid."
  [s]
  (when s
    (let [kw (keyword (str/lower-case s))]
      (when (valid-priorities kw)
        kw))))

(defn cmd-update!
  "Update mote fields.

   Arguments (in context):
   - :id - The mote ID to update (required)

   Options:
   - :claim - New claim text
   - :priority - New priority (p0-p4)
   - :difficulty - New difficulty (1-5)
   - :agent - Agent name (default: 'cli-user')
   - :dry-run - Show what would change without executing

   At least one of claim/priority/difficulty must be provided.

   Returns the updated mote."
  [{:keys [id options repo-path] :or {repo-path "."}}]
  (let [{:keys [claim priority difficulty name dry-run]} options
        agent (or name "cli-user")]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to update"]})))

    (when (and (nil? claim) (nil? priority) (nil? difficulty))
      (throw (ex-info "No update fields provided"
                      {:type :validation-failed
                       :errors ["Provide at least one of --claim, --priority, or --difficulty"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Parse and validate priority
      (let [parsed-priority (when priority (parse-priority priority))]
        (when (and priority (nil? parsed-priority))
          (throw (ex-info "Invalid priority"
                          {:type :validation-failed
                           :errors [(str "Priority must be p0-p4, got: " priority)]})))

        ;; Validate difficulty
        (when (and difficulty (or (< difficulty 1) (> difficulty 5)))
          (throw (ex-info "Invalid difficulty"
                          {:type :validation-failed
                           :errors [(str "Difficulty must be 1-5, got: " difficulty)]})))

        (if dry-run
          ;; Dry run - show what would change
          (let [changes (cond-> []
                          claim (conj (str "claim: \"" (:claim current-mote) "\" -> \"" claim "\""))
                          parsed-priority (conj (str "priority: " (clojure.core/name (:priority current-mote)) " -> " (clojure.core/name parsed-priority)))
                          difficulty (conj (str "difficulty: " (:difficulty current-mote) " -> " difficulty)))]
            (core/dry-run-result
             :output (str (core/format-would-update
                           [{:id id :change (str/join ", " changes)}]))
             :would-update [{:id id :change (str/join ", " changes)}]
             :next-actions [(core/show-action id)
                            (core/ready-action)]))
          ;; Execute
          (let [updated-mote (cond-> current-mote
                              claim (mote/set-claim claim)
                              parsed-priority (mote/set-priority parsed-priority)
                              difficulty (mote/set-difficulty difficulty))]
            (tx/atomic-write! repo-path
                              (str "Update mote " id)
                              [updated-mote])
            (assoc updated-mote
                   :next-actions [(core/show-action id)
                                  (core/ready-action)])))))))
