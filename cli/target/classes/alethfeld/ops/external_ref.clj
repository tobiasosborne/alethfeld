(ns alethfeld.ops.external-ref
  "External reference operations - add and update literature citations."
  (:require [alethfeld.config :as config]
            [alethfeld.graph :as graph]))

;; =============================================================================
;; ID Generation
;; =============================================================================

(defn generate-ref-id
  "Generate a new external reference ID."
  []
  (str "ext-" (config/generate-uuid-prefix)))

;; =============================================================================
;; Valid Statuses
;; =============================================================================

(def valid-verification-statuses
  #{:pending :verified :mismatch :not-found :metadata-only})

;; =============================================================================
;; Add External Reference
;; =============================================================================

(defn- validate-ref [ref]
  (let [errors (atom [])]
    (when-not (or (:doi ref) (:arxiv ref) (:url ref))
      (swap! errors conj {:type :no-identifier
                          :message "External ref must have at least one of: :doi, :arxiv, :url"}))
    (when-not (:claimed-statement ref)
      (swap! errors conj {:type :missing-claimed-statement
                          :message "External ref must have :claimed-statement"}))
    (when (seq @errors)
      @errors)))

(defn add-external-ref
  "Add a new external reference (literature citation).

   Required fields: :claimed-statement, and at least one of :doi, :arxiv, :url
   Optional: :bibdata, :notes

   Generates ID, sets status to :pending.
   Returns {:ok new-graph :ref-id <id>} or {:error errors}"
  [graph ref]
  (if-let [errors (validate-ref ref)]
    {:error errors}
    (let [ref-id (or (:id ref) (generate-ref-id))
          complete-ref (merge {:id ref-id
                               :verification-status :pending
                               :verified-statement nil
                               :bibdata nil
                               :notes nil}
                              ref
                              {:id ref-id})
          new-graph (-> graph
                        (assoc-in [:external-refs ref-id] complete-ref)
                        (graph/increment-version)
                        (graph/update-last-modified))]
      {:ok new-graph :ref-id ref-id})))

;; =============================================================================
;; Update External Reference
;; =============================================================================

(defn- check-ref-exists [graph ref-id]
  (when-not (get-in graph [:external-refs ref-id])
    {:type :ref-not-found
     :ref-id ref-id
     :message (str "External reference " ref-id " not found")}))

(defn- check-valid-status [status]
  (when-not (contains? valid-verification-statuses status)
    {:type :invalid-status
     :status status
     :valid-statuses valid-verification-statuses
     :message (str "Invalid status " status ". Valid: " valid-verification-statuses)}))

(defn update-external-ref
  "Update an external reference after verification.

   verification-result should be a map with:
   - :status - one of :verified, :mismatch, :not-found, :metadata-only
   - :verified-statement - optional, the actual statement from source
   - :bibdata - optional, bibliographic data
   - :notes - optional, verification notes

   Returns {:ok new-graph} or {:error errors}"
  [graph ref-id verification-result]
  (let [status (:status verification-result)
        errors (remove nil?
                       [(check-ref-exists graph ref-id)
                        (check-valid-status status)])]
    (if (seq errors)
      {:error (vec errors)}
      (let [updates (select-keys verification-result [:verified-statement :bibdata :notes])
            new-graph (-> graph
                          (update-in [:external-refs ref-id]
                                     merge
                                     {:verification-status status}
                                     updates)
                          (graph/increment-version)
                          (graph/update-last-modified))]
        {:ok new-graph}))))
