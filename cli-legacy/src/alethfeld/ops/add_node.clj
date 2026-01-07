(ns alethfeld.ops.add-node
  "AddNode operation - adds a new node to a semantic proof graph."
  (:require [alethfeld.config :as config]
            [alethfeld.schema :as schema]
            [alethfeld.graph :as graph]
            [alethfeld.validators :as validators]
            [clojure.set :as set]))

;; =============================================================================
;; Precondition Checks
;; =============================================================================

(defn- check-id-unique
  "Check that node ID doesn't already exist."
  [graph node-id]
  (when (graph/get-node graph node-id)
    {:type :duplicate-id
     :node-id node-id
     :message (str "Node " node-id " already exists in graph")}))

(defn- check-dependencies-exist
  "Check that all dependencies exist in graph."
  [graph dependencies]
  (let [existing (graph/node-ids graph)
        missing (set/difference dependencies existing)]
    (when (seq missing)
      {:type :missing-dependencies
       :missing missing
       :message (str "Dependencies not found: " (pr-str missing))})))

(defn- check-scope-valid
  "Check that scope is subset of valid scope."
  [graph node-id scope dependencies]
  ;; To compute valid scope, we need ancestors. Since the node isn't added yet,
  ;; we compute what ancestors would be if the node were added.
  (let [nodes (:nodes graph)
        ;; All transitive ancestors through proposed dependencies
        all-ancestors (reduce (fn [acc dep]
                                (set/union acc (graph/get-ancestors graph dep) #{dep}))
                              #{}
                              dependencies)
        ;; Local-assumes among ancestors
        assumes (->> all-ancestors
                     (filter #(= :local-assume (get-in nodes [% :type])))
                     set)
        ;; Find discharged assumptions among ancestors
        discharged (->> all-ancestors
                        (filter #(= :local-discharge (get-in nodes [% :type])))
                        (map #(get-in nodes [% :discharges]))
                        (remove nil?)
                        set)
        valid-scope (set/difference assumes discharged)
        invalid (set/difference scope valid-scope)]
    (when (seq invalid)
      {:type :invalid-scope
       :invalid-entries invalid
       :valid-scope valid-scope
       :message (str "Invalid scope entries: " (pr-str invalid)
                     ". Valid scope: " (pr-str valid-scope))})))

(defn- check-no-cycle
  "Check that adding the node wouldn't create a cycle."
  [graph node-id dependencies]
  (when (graph/would-create-cycle? graph node-id dependencies)
    {:type :would-create-cycle
     :node-id node-id
     :dependencies dependencies
     :message (str "Adding node " node-id " with dependencies " (pr-str dependencies)
                   " would create a cycle")}))

(defn- check-type-specific-fields
  "Check that type-specific required fields are present."
  [node]
  (let [node-type (:type node)]
    (cond
      (and (= :local-assume node-type) (not (:introduces node)))
      {:type :missing-introduces
       :node-id (:id node)
       :message "Node type :local-assume requires :introduces field"}

      (and (= :local-discharge node-type) (not (:discharges node)))
      {:type :missing-discharges
       :node-id (:id node)
       :message "Node type :local-discharge requires :discharges field"}

      (and (= :lemma-ref node-type) (not (:lemma-id node)))
      {:type :missing-lemma-id
       :node-id (:id node)
       :message "Node type :lemma-ref requires :lemma-id field"}

      (and (= :external-ref node-type) (not (:external-id node)))
      {:type :missing-external-id
       :node-id (:id node)
       :message "Node type :external-ref requires :external-id field"}

      :else nil)))

(defn- check-discharge-target
  "For local-discharge, check that the target is a valid local-assume in scope."
  [graph node]
  (when (= :local-discharge (:type node))
    (let [target (:discharges node)
          target-node (graph/get-node graph target)]
      (cond
        (nil? target-node)
        {:type :discharge-target-not-found
         :node-id (:id node)
         :target target
         :message (str "Discharge target " target " not found")}

        (not= :local-assume (:type target-node))
        {:type :discharge-target-not-local-assume
         :node-id (:id node)
         :target target
         :message (str "Discharge target " target " is not a :local-assume")}

        :else nil))))

(defn validate-preconditions
  "Run all precondition checks. Returns nil if all pass, or a vector of errors."
  [graph node]
  (let [node-id (:id node)
        deps (:dependencies node)
        scope (:scope node)
        errors (remove nil?
                       [(check-id-unique graph node-id)
                        (check-dependencies-exist graph deps)
                        (check-scope-valid graph node-id scope deps)
                        (check-no-cycle graph node-id deps)
                        (check-type-specific-fields node)
                        (check-discharge-target graph node)])]
    (when (seq errors)
      (vec errors))))

;; =============================================================================
;; Node Completion
;; =============================================================================

(defn- compute-node-taint
  "Compute taint for a new node based on its dependencies."
  [graph node]
  (let [deps (:dependencies node)
        dep-taints (map #(get-in graph [:nodes % :taint]) deps)]
    (if (some #{:tainted :self-admitted} dep-taints)
      :tainted
      :clean)))

(defn complete-node
  "Fill in computed and defaulted fields for a node."
  [graph node]
  (let [statement (:statement node)
        taint (compute-node-taint graph node)
        status (or (:status node) :proposed)
        ;; If status is :admitted, override taint
        final-taint (if (= :admitted status) :self-admitted taint)
        content-hash (config/compute-content-hash statement)
        provenance (or (:provenance node) (config/default-provenance :prover))]
    (assoc node
           :content-hash content-hash
           :taint final-taint
           :status status
           :provenance provenance)))

;; =============================================================================
;; Main Operation
;; =============================================================================

(defn add-node
  "Add a node to the graph.

   Input node must have: :id, :type, :statement, :dependencies, :scope,
                         :justification, :depth, :display-order
   Optional input: :parent, :content-hash, :status, :taint, :provenance
   Type-specific: :introduces, :discharges, :lemma-id, :external-id, :assumption-label

   Computed fields: :content-hash, :taint, :status (defaults to :proposed)

   Returns {:ok new-graph} or {:error errors}"
  [graph node]
  ;; First validate the partial node schema
  (let [schema-result (schema/validate-partial-node node)]
    (if (not (:valid schema-result))
      {:error [{:type :schema-validation
                :errors (:errors schema-result)
                :message "Node fails schema validation"}]}

      ;; Then check semantic preconditions
      (if-let [errors (validate-preconditions graph node)]
        {:error errors}

        ;; Complete the node and add it
        (let [completed-node (complete-node graph node)
              new-graph (-> graph
                            (assoc-in [:nodes (:id node)] completed-node)
                            (graph/increment-version)
                            (graph/update-last-modified)
                            (graph/update-context-budget)
                            (graph/invalidate-caches))]
          ;; Assert graph invariants are maintained
          (validators/assert-valid-graph! new-graph "add-node postcondition")
          {:ok new-graph})))))

(defn generate-node-id
  "Generate a new node ID with format :<depth>-<6-hex>."
  [depth]
  (config/generate-node-id depth))
