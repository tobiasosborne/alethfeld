(ns alethfeld.ops.delete-node
  "DeleteNode operation - deletes (archives) a node from the graph."
  (:require [alethfeld.graph :as graph]
            [alethfeld.validators :as validators]))

;; =============================================================================
;; Precondition Checks
;; =============================================================================

(defn- check-node-exists
  "Check that the node exists."
  [graph node-id]
  (when-not (graph/get-node graph node-id)
    {:type :node-not-found
     :node-id node-id
     :message (str "Node " node-id " not found in graph")}))

(defn- check-no-dependents
  "Check that no other nodes depend on this node."
  [graph node-id]
  (let [dependents (graph/get-direct-dependents graph node-id)]
    (when (seq dependents)
      {:type :has-dependents
       :node-id node-id
       :dependents dependents
       :message (str "Cannot delete node " node-id
                     " - other nodes depend on it: " (pr-str dependents))})))

(defn validate-preconditions
  "Run all precondition checks."
  [graph node-id]
  (let [errors (remove nil?
                       [(check-node-exists graph node-id)
                        (check-no-dependents graph node-id)])]
    (when (seq errors)
      (vec errors))))

;; =============================================================================
;; Main Operation
;; =============================================================================

(defn delete-node
  "Delete a node from the graph.

   The node is moved to :archived-nodes, not destroyed.

   Preconditions:
   - Node must exist
   - No other nodes can depend on it

   Postconditions:
   - Node moved to :archived-nodes
   - Node removed from :nodes
   - Version incremented

   Returns {:ok new-graph} or {:error errors}"
  [graph node-id]
  (if-let [errors (validate-preconditions graph node-id)]
    {:error errors}

    (let [node (graph/get-node graph node-id)

          ;; Archive the node
          graph (assoc-in graph [:archived-nodes node-id] node)

          ;; Remove from active nodes
          graph (update graph :nodes dissoc node-id)

          ;; Update metadata
          graph (-> graph
                    (graph/increment-version)
                    (graph/update-last-modified)
                    (graph/update-context-budget)
                    (graph/invalidate-caches))]

      ;; Assert graph invariants are maintained
      (validators/assert-valid-graph! graph "delete-node postcondition")
      {:ok graph})))
