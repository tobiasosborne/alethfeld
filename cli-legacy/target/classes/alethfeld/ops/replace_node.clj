(ns alethfeld.ops.replace-node
  "ReplaceNode operation - replaces a rejected node with a revised version."
  (:require [alethfeld.config :as config]
            [alethfeld.schema :as schema]
            [alethfeld.graph :as graph]
            [alethfeld.ops.add-node :as add-node]))

;; =============================================================================
;; Precondition Checks
;; =============================================================================

(defn- check-old-node-exists
  "Check that the old node exists."
  [graph old-id]
  (when-not (graph/get-node graph old-id)
    {:type :node-not-found
     :node-id old-id
     :message (str "Node " old-id " not found in graph")}))

(defn- check-old-node-rejected
  "Check that the old node has status :rejected."
  [graph old-id]
  (let [node (graph/get-node graph old-id)]
    (when (and node (not= :rejected (:status node)))
      {:type :not-rejected
       :node-id old-id
       :status (:status node)
       :message (str "Node " old-id " has status " (:status node)
                     " but must be :rejected to replace")})))

(defn validate-preconditions
  "Run all precondition checks."
  [graph old-id]
  (let [errors (remove nil?
                       [(check-old-node-exists graph old-id)
                        (check-old-node-rejected graph old-id)])]
    (when (seq errors)
      (vec errors))))

;; =============================================================================
;; Dependency Rewriting
;; =============================================================================

(defn- rewrite-dependencies
  "Rewrite all nodes that depend on old-id to depend on new-id instead."
  [graph old-id new-id]
  (reduce (fn [g [node-id node]]
            (if (contains? (:dependencies node) old-id)
              (let [new-deps (-> (:dependencies node)
                                 (disj old-id)
                                 (conj new-id))]
                (assoc-in g [:nodes node-id :dependencies] new-deps))
              g))
          graph
          (:nodes graph)))

;; =============================================================================
;; Main Operation
;; =============================================================================

(defn replace-node
  "Replace a rejected node with a revised version.

   - Old node must have status :rejected
   - Old node is archived
   - New node gets :provenance/revision-of pointing to old
   - Dependencies on old node are rewritten to new node

   Returns {:ok new-graph} or {:error errors}"
  [graph old-id new-node]
  ;; Check preconditions for old node
  (if-let [errors (validate-preconditions graph old-id)]
    {:error errors}

    ;; Validate new node schema
    (let [schema-result (schema/validate-partial-node new-node)]
      (if (not (:valid schema-result))
        {:error [{:type :schema-validation
                  :errors (:errors schema-result)
                  :message "New node fails schema validation"}]}

        (let [old-node (graph/get-node graph old-id)
              new-id (:id new-node)

              ;; Archive the old node
              graph (-> graph
                        (assoc-in [:archived-nodes old-id] old-node)
                        (update :nodes dissoc old-id))

              ;; Prepare new node with provenance
              new-node-with-provenance (assoc new-node
                                              :provenance (merge (or (:provenance new-node)
                                                                     (config/default-provenance :prover))
                                                                 {:revision-of old-id}))

              ;; Rewrite dependencies from old to new
              graph (rewrite-dependencies graph old-id new-id)

              ;; Add the new node using add-node logic
              add-result (add-node/add-node graph new-node-with-provenance)]

          (if (:error add-result)
            ;; Rollback: restore old node
            {:error (:error add-result)}
            {:ok (:ok add-result)}))))))
