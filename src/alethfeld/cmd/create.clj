(ns alethfeld.cmd.create
  "Create command implementation."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.id :as id]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]))

;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(defn- next-root-id
  "Get the next available root mote ID.
   Scans existing motes and returns the next integer as a string."
  [repo-path]
  (let [motes (store/load-all-motes repo-path)
        root-ids (->> (keys motes)
                      (filter #(= 1 (id/id-depth %)))
                      (map #(parse-long %))
                      (filter some?))]
    (str (if (empty? root-ids)
           1
           (inc (apply max root-ids))))))

;; -----------------------------------------------------------------------------
;; Create Command
;; -----------------------------------------------------------------------------

(defn cmd-create!
  "Create a new mote.

   Arguments (in context):
   - :id - Parent mote ID (required unless --root)

   Options:
   - :claim - The claim text (required)
   - :root - Create root mote (no parent)
   - :difficulty - Difficulty 1-5 (optional, inherits from parent or defaults to 3)
   - :priority - Priority :p0-:p4 (optional, inherits from parent or defaults to :p2)
   - :agent - Agent name (default: 'cli-user')
   - :dry-run - Show what would be created without executing

   For root motes:
   - Generates next available root ID (1, 2, 3, ...)

   For child motes:
   - Parent must exist
   - Generates next child ID based on parent's existing children
   - Inherits priority/difficulty from parent if not specified

   Returns the created mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim root difficulty priority name dry-run]} options
        agent (or name "cli-user")]

    ;; Validation
    (when-not claim
      (throw (ex-info "Claim is required"
                      {:type :validation-failed
                       :errors ["--claim is required"]})))

    (when (and root id)
      (throw (ex-info "Cannot specify both --root and parent ID"
                      {:type :validation-failed
                       :errors ["Use either --root or provide a parent ID, not both"]})))

    (when (and (not root) (not id))
      (throw (ex-info "Parent ID required for non-root motes"
                      {:type :validation-failed
                       :errors ["Provide parent ID or use --root for root motes"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (if root
      ;; Create root mote
      (let [new-id (next-root-id repo-path)
            eff-difficulty (or difficulty 3)
            eff-priority (or priority :p2)]
        (if dry-run
          ;; Dry run
          (core/dry-run-result
           :output (str (core/format-would-create
                         [{:id new-id :status :fixed :claim claim}])
                        "\n\nPriority: " (name eff-priority) ", Difficulty: " eff-difficulty)
           :would-create [{:id new-id :claim claim :status :fixed}])
          ;; Execute
          (let [new-mote (mote/make-root-mote new-id claim agent
                                              :difficulty eff-difficulty
                                              :priority eff-priority)
                _ (tx/atomic-write! repo-path
                                    (str "Create root mote " new-id)
                                    [new-mote])]
            (assoc new-mote :next-actions [(core/show-action new-id)
                                           (core/ready-action)
                                           (core/status-action)]))))

      ;; Create child mote
      (let [parent (store/load-mote repo-path id)]
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id id})))

        (let [existing-children (:children parent)
              new-id (id/next-child-id id existing-children)
              eff-difficulty (or difficulty (:difficulty parent))
              eff-priority (or priority (:priority parent))]
          (if dry-run
            ;; Dry run
            (core/dry-run-result
             :output (str (core/format-would-create
                           [{:id new-id :status :fixed :claim claim}])
                          (core/format-would-update
                           [{:id id :change (str "add child " new-id)}])
                          "\n\nPriority: " (name eff-priority) ", Difficulty: " eff-difficulty)
             :would-create [{:id new-id :claim claim :status :fixed}]
             :would-update [{:id id :change (str "add child " new-id)}])
            ;; Execute
            (let [new-mote (mote/make-child-mote new-id claim agent parent
                                                 :difficulty eff-difficulty
                                                 :priority eff-priority)
                  updated-parent (mote/add-child parent new-id)
                  _ (tx/atomic-write! repo-path
                                      (str "Create child mote " new-id)
                                      [new-mote updated-parent])]
              (assoc new-mote :next-actions [(core/show-action new-id)
                                             (core/tree-action id)
                                             (core/ready-action)]))))))))
