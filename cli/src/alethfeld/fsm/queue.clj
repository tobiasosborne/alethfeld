(ns alethfeld.fsm.queue
  "FSM queue operations for managing expansion and verification queues.

   The expand-verify-loop phase uses two queues:
   - Expansion queue: Nodes waiting to be expanded into substeps
   - Verification queue: Nodes waiting to be verified by triple-verifier

   Queues are stored at [:fsm :pending :expansions] and [:fsm :pending :verifications].
   All operations maintain FIFO order and prevent duplicates."
  (:require [alethfeld.fsm.schema :as fsm-schema]))

;; =============================================================================
;; Internal Helpers
;; =============================================================================

(defn- ensure-fsm-pending
  "Ensure graph has FSM pending structure initialized.
   Returns graph with [:fsm :pending] initialized if missing."
  [graph]
  (cond-> graph
    (nil? (:fsm graph))
    (assoc :fsm {:phase fsm-schema/initial-state
                 :phase-entered-at nil
                 :previous-phase nil
                 :history []
                 :pending {:expansions []
                           :verifications []}})

    (nil? (get-in graph [:fsm :pending]))
    (assoc-in [:fsm :pending] {:expansions []
                               :verifications []})

    (nil? (get-in graph [:fsm :pending :expansions]))
    (assoc-in [:fsm :pending :expansions] [])

    (nil? (get-in graph [:fsm :pending :verifications]))
    (assoc-in [:fsm :pending :verifications] [])))

(defn- get-queue
  "Get a queue from the graph."
  [graph queue-key]
  (or (get-in graph [:fsm :pending queue-key]) []))

;; =============================================================================
;; Queue Status
;; =============================================================================

(defn get-queue-status
  "Get status of both queues.

   Returns:
   {:expansions [<node-ids>]
    :verifications [<node-ids>]
    :expansion-count <int>
    :verification-count <int>
    :total-pending <int>}"
  [graph]
  (let [expansions (get-queue graph :expansions)
        verifications (get-queue graph :verifications)]
    {:expansions expansions
     :verifications verifications
     :expansion-count (count expansions)
     :verification-count (count verifications)
     :total-pending (+ (count expansions) (count verifications))}))

(defn queues-empty?
  "Returns true if both expansion and verification queues are empty."
  [graph]
  (let [status (get-queue-status graph)]
    (zero? (:total-pending status))))

;; =============================================================================
;; Add to Queue Operations
;; =============================================================================

(defn add-to-expansion-queue
  "Add a node-id to the expansion queue.

   Arguments:
   - graph: The proof graph
   - node-id: The node ID to add

   Returns:
   {:ok updated-graph} with node-id appended to expansion queue.
   Does not add duplicates.
   Increments graph version."
  [graph node-id]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :expansions)]
    (if (some #{node-id} current-queue)
      ;; Already in queue, no change (still return incremented version for consistency)
      {:ok (update g :version inc)}
      {:ok (-> g
               (update-in [:fsm :pending :expansions] conj node-id)
               (update :version inc))})))

(defn add-to-verification-queue
  "Add a node-id to the verification queue.

   Arguments:
   - graph: The proof graph
   - node-id: The node ID to add

   Returns:
   {:ok updated-graph} with node-id appended to verification queue.
   Does not add duplicates.
   Increments graph version."
  [graph node-id]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :verifications)]
    (if (some #{node-id} current-queue)
      ;; Already in queue, no change
      {:ok (update g :version inc)}
      {:ok (-> g
               (update-in [:fsm :pending :verifications] conj node-id)
               (update :version inc))})))

;; =============================================================================
;; Pop from Queue Operations
;; =============================================================================

(defn pop-expansion
  "Pop and return the first node from expansion queue.

   Returns:
   {:ok updated-graph :node-id <id-or-nil>}

   Returns nil node-id if queue is empty.
   Increments graph version."
  [graph]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :expansions)]
    (if (empty? current-queue)
      {:ok (update g :version inc) :node-id nil}
      {:ok (-> g
               (assoc-in [:fsm :pending :expansions] (vec (rest current-queue)))
               (update :version inc))
       :node-id (first current-queue)})))

(defn pop-verification
  "Pop and return the first node from verification queue.

   Returns:
   {:ok updated-graph :node-id <id-or-nil>}

   Returns nil node-id if queue is empty.
   Increments graph version."
  [graph]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :verifications)]
    (if (empty? current-queue)
      {:ok (update g :version inc) :node-id nil}
      {:ok (-> g
               (assoc-in [:fsm :pending :verifications] (vec (rest current-queue)))
               (update :version inc))
       :node-id (first current-queue)})))

;; =============================================================================
;; Clear Queue Operations
;; =============================================================================

(defn clear-expansion-queue
  "Clear all items from the expansion queue.

   Returns:
   {:ok updated-graph} with empty expansion queue.
   Increments graph version."
  [graph]
  (let [g (ensure-fsm-pending graph)]
    {:ok (-> g
             (assoc-in [:fsm :pending :expansions] [])
             (update :version inc))}))

(defn clear-verification-queue
  "Clear all items from the verification queue.

   Returns:
   {:ok updated-graph} with empty verification queue.
   Increments graph version."
  [graph]
  (let [g (ensure-fsm-pending graph)]
    {:ok (-> g
             (assoc-in [:fsm :pending :verifications] [])
             (update :version inc))}))

;; =============================================================================
;; Remove from Queue Operations
;; =============================================================================

(defn remove-from-expansion-queue
  "Remove a specific node-id from the expansion queue.

   Arguments:
   - graph: The proof graph
   - node-id: The node ID to remove

   Returns:
   {:ok updated-graph} with node-id removed from expansion queue.
   No-op if node-id not in queue.
   Increments graph version."
  [graph node-id]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :expansions)
        new-queue (vec (remove #{node-id} current-queue))]
    {:ok (-> g
             (assoc-in [:fsm :pending :expansions] new-queue)
             (update :version inc))}))

(defn remove-from-verification-queue
  "Remove a specific node-id from the verification queue.

   Arguments:
   - graph: The proof graph
   - node-id: The node ID to remove

   Returns:
   {:ok updated-graph} with node-id removed from verification queue.
   No-op if node-id not in queue.
   Increments graph version."
  [graph node-id]
  (let [g (ensure-fsm-pending graph)
        current-queue (get-queue g :verifications)
        new-queue (vec (remove #{node-id} current-queue))]
    {:ok (-> g
             (assoc-in [:fsm :pending :verifications] new-queue)
             (update :version inc))}))
