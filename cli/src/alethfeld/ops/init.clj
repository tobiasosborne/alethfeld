(ns alethfeld.ops.init
  "Init operation - creates a new semantic proof graph."
  (:require [alethfeld.config :as config]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as validators]))

;; =============================================================================
;; Graph Initialization
;; =============================================================================

(defn generate-graph-id
  "Generate a unique graph ID."
  []
  (str "graph-" (config/generate-uuid-prefix) "-" (config/generate-uuid-prefix)))

(defn init-graph
  "Create a new semantic proof graph for a theorem.

   Arguments:
   - theorem-statement: LaTeX string describing the theorem to prove
   - opts: Optional map with:
     - :graph-id - Custom graph ID (generated if not provided)
     - :proof-mode - One of :strict-mathematics, :formal-physics, :algebraic-derivation
     - :max-tokens - Context budget limit (default 100000)

   Returns {:ok graph} with a valid, empty proof graph."
  [theorem-statement & {:keys [graph-id proof-mode max-tokens]
                        :or {proof-mode :strict-mathematics
                             max-tokens config/default-max-tokens}}]
  (let [gid (or graph-id (generate-graph-id))
        now (config/current-iso8601)

        graph {:graph-id gid
               :version 1
               :theorem {:id :theorem
                         :statement theorem-statement
                         :content-hash (config/compute-content-hash theorem-statement)}
               :nodes {}
               :symbols {}
               :external-refs {}
               :lemmas {}
               :obligations []
               :archived-nodes {}
               :metadata {:created-at now
                          :last-modified now
                          :proof-mode proof-mode
                          :iteration-counts {:verification {}
                                             :expansion {}
                                             :strategy 0}
                          :context-budget {:max-tokens max-tokens
                                           :current-estimate 0}}}

        ;; Validate against schema
        validation (schema/validate-schema graph)]

    (if (:valid validation)
      (do
        ;; Assert full graph invariants (schema + semantics)
        (validators/assert-valid-graph! graph "init-graph postcondition")
        {:ok graph})
      {:error [{:type :schema-validation
                :errors (:errors validation)
                :message "Generated graph fails schema validation"}]})))

;; =============================================================================
;; Template Graphs
;; =============================================================================

(defn init-with-assumptions
  "Create a graph with initial assumption nodes.

   Arguments:
   - theorem-statement: The theorem to prove
   - assumptions: Vector of {:label :A1 :statement \"...\"}

   Returns {:ok graph} with assumption nodes added."
  [theorem-statement assumptions & opts]
  (let [result (apply init-graph theorem-statement opts)]
    (if (:error result)
      result
      (let [graph (:ok result)
            ;; Add assumption nodes
            graph (reduce
                   (fn [g {:keys [label statement]}]
                     (let [node-id (keyword (str "0-" (name label)))
                           content-hash (config/compute-content-hash statement)
                           node {:id node-id
                                 :type :assumption
                                 :statement statement
                                 :content-hash content-hash
                                 :dependencies #{}
                                 :scope #{}
                                 :justification :assumption
                                 :status :verified
                                 :taint :clean
                                 :depth 0
                                 :parent nil
                                 :display-order (.indexOf (vec assumptions) {:label label :statement statement})
                                 :assumption-label label
                                 :provenance (config/default-provenance :orchestrator)}]
                       (assoc-in g [:nodes node-id] node)))
                   graph
                   assumptions)]
        ;; Assert graph invariants are maintained
        (validators/assert-valid-graph! graph "init-with-assumptions postcondition")
        {:ok graph}))))
