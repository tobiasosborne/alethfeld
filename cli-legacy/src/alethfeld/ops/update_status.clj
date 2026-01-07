(ns alethfeld.ops.update-status
  "UpdateNodeStatus operation - updates verification status of a node."
  (:require [alethfeld.config :as config]
            [alethfeld.graph :as graph]
            [alethfeld.validators :as validators]))

;; =============================================================================
;; Valid Statuses
;; =============================================================================

(def valid-statuses
  "Set of valid node statuses."
  #{:proposed :verified :admitted :rejected})

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

(defn- check-valid-status
  "Check that the new status is valid."
  [new-status]
  (when-not (contains? valid-statuses new-status)
    {:type :invalid-status
     :status new-status
     :valid-statuses valid-statuses
     :message (str "Invalid status " new-status ". Valid: " valid-statuses)}))

(defn validate-preconditions
  "Run all precondition checks."
  [graph node-id new-status]
  (let [errors (remove nil?
                       [(check-node-exists graph node-id)
                        (check-valid-status new-status)])]
    (when (seq errors)
      (vec errors))))

;; =============================================================================
;; Taint Recomputation
;; =============================================================================

(defn- recompute-taint-for-node
  "Recompute taint for a single node."
  [graph node-id]
  (let [new-taint (graph/compute-taint graph node-id)]
    (assoc-in graph [:nodes node-id :taint] new-taint)))

(defn- recompute-taints-from
  "Recompute taints for a node and all its descendants."
  [graph node-id]
  (let [descendants (graph/get-descendants graph node-id)
        all-to-update (cons node-id (graph/topological-sort graph descendants))]
    (reduce recompute-taint-for-node graph all-to-update)))

;; =============================================================================
;; Obligation Management
;; =============================================================================

(defn- add-obligation
  "Add a proof obligation for an admitted node."
  [graph node-id]
  (let [node (graph/get-node graph node-id)
        assumptions (graph/active-assumptions graph node-id)
        assumption-details (map (fn [a-id]
                                  {:id a-id
                                   :statement (:statement (graph/get-node graph a-id))})
                                assumptions)
        scope-details (map (fn [s-id]
                             {:id s-id
                              :introduces (:introduces (graph/get-node graph s-id))})
                           (:scope node))
        obligation {:node-id node-id
                    :claim (:statement node)
                    :context {:assumptions (vec assumption-details)
                              :scope (vec scope-details)}}]
    (update graph :obligations conj obligation)))

(defn- remove-obligation
  "Remove an obligation for a node (if it exists)."
  [graph node-id]
  (update graph :obligations
          (fn [obs]
            (vec (remove #(= node-id (:node-id %)) obs)))))

;; =============================================================================
;; Main Operation
;; =============================================================================

(defn update-status
  "Update a node's verification status.

   Recomputes taint for the node and all its transitive dependents.
   If status is :admitted, adds a proof obligation.
   If status changes from :admitted, removes the obligation.

   Returns {:ok new-graph} or {:error errors}"
  [graph node-id new-status]
  (if-let [errors (validate-preconditions graph node-id new-status)]
    {:error errors}

    (let [node (graph/get-node graph node-id)
          old-status (:status node)

          ;; Update the status
          graph (assoc-in graph [:nodes node-id :status] new-status)

          ;; Recompute taints from this node downward
          graph (recompute-taints-from graph node-id)

          ;; Handle obligations
          graph (cond
                  ;; Newly admitted -> add obligation
                  (and (= :admitted new-status) (not= :admitted old-status))
                  (add-obligation graph node-id)

                  ;; No longer admitted -> remove obligation
                  (and (not= :admitted new-status) (= :admitted old-status))
                  (remove-obligation graph node-id)

                  ;; No change
                  :else graph)

          ;; Update metadata
          graph (-> graph
                    (graph/increment-version)
                    (graph/update-last-modified))]

      ;; Assert graph invariants are maintained
      (validators/assert-valid-graph! graph "update-status postcondition")
      {:ok graph})))
