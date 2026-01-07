(ns alethfeld.ops.extract-lemma
  "ExtractLemma operation - extracts a verified subgraph as an independent lemma."
  (:require [alethfeld.config :as config]
            [alethfeld.graph :as graph]
            [alethfeld.validators :as validators]
            [clojure.set :as set]))

;; =============================================================================
;; Precondition Checks (using graph/check-independence)
;; =============================================================================

(defn validate-preconditions
  "Validate that the extraction can proceed.
   Uses graph/check-independence for the core checks."
  [g root-id node-ids-set]
  (graph/check-independence g root-id node-ids-set))

;; =============================================================================
;; Lemma Creation
;; =============================================================================

(defn- collect-extraction-nodes
  "If node-ids is provided, use it. Otherwise, compute the minimal extraction set:
   the root node plus all its transitive ancestors, excluding assumption nodes
   (which remain as external dependencies)."
  [g root-id node-ids]
  (if (seq node-ids)
    (set node-ids)
    ;; Minimal extraction: root + all ancestors except assumptions
    (let [nodes (:nodes g)
          all-ancestors (conj (graph/get-ancestors g root-id) root-id)]
      ;; Exclude :assumption nodes - they're external dependencies
      (set (remove #(= :assumption (get-in nodes [% :type])) all-ancestors)))))

(defn- compute-lemma-statement
  "Compute the lemma statement from the root node and its assumptions."
  [g root-id extracted-nodes]
  (let [root-node (graph/get-node g root-id)
        root-statement (:statement root-node)

        ;; Find all assumptions (global and local) that are external dependencies
        nodes (:nodes g)
        external-deps (reduce (fn [acc nid]
                                (let [node (get nodes nid)
                                      deps (:dependencies node #{})
                                      ext (set/difference deps extracted-nodes)]
                                  (into acc ext)))
                              #{}
                              extracted-nodes)

        ;; Filter to assumptions
        assumption-deps (->> external-deps
                             (filter #(#{:assumption :local-assume}
                                       (get-in nodes [% :type])))
                             (map #(get-in nodes [% :statement]))
                             (remove nil?))]

    ;; Build lemma statement
    (if (seq assumption-deps)
      (str "If " (clojure.string/join " and " assumption-deps)
           ", then " root-statement)
      root-statement)))

(defn- compute-lemma-taint
  "Compute taint for the extracted lemma based on its nodes."
  [g extracted-nodes]
  (let [nodes (:nodes g)
        taints (map #(get-in nodes [% :taint]) extracted-nodes)]
    (cond
      (some #{:tainted} taints) :tainted
      (some #{:self-admitted} taints) :tainted  ; tainted because depends on admitted
      :else :clean)))

(defn- create-lemma-entry
  "Create the lemma entry for the graph's :lemmas map."
  [g root-id extracted-nodes lemma-name]
  (let [root-node (graph/get-node g root-id)
        statement (compute-lemma-statement g root-id extracted-nodes)
        taint (compute-lemma-taint g extracted-nodes)]
    {:id lemma-name
     :name lemma-name
     :statement statement
     :content-hash (config/compute-content-hash statement)
     :root-node root-id
     :status (if (= :clean taint) :proven :tainted)
     :taint taint
     :extracted-nodes extracted-nodes
     :proof-graph-id nil}))

;; =============================================================================
;; Graph Update
;; =============================================================================

(defn- add-lemma-ref-node
  "Add a lemma-ref node that replaces the extracted subgraph root."
  [g root-id lemma-name extracted-nodes]
  (let [root-node (graph/get-node g root-id)

        ;; Find external nodes that depend on the root (outside extraction set)
        external-dependents (set/difference (graph/get-direct-dependents g root-id)
                                            extracted-nodes)

        ;; Generate ID for the lemma-ref node
        lemma-ref-id (keyword (str "lemma-ref-" (config/generate-uuid-prefix)))

        ;; Create the lemma-ref node
        lemma-ref-node {:id lemma-ref-id
                        :type :lemma-ref
                        :statement (:statement root-node)
                        :content-hash (config/compute-content-hash (:statement root-node))
                        :dependencies #{}  ; Lemma-ref has no dependencies in the graph
                        :scope #{}
                        :justification :lemma-application
                        :status :verified
                        :taint (compute-lemma-taint g extracted-nodes)
                        :depth (:depth root-node)
                        :parent (:parent root-node)
                        :display-order (:display-order root-node)
                        :lemma-id lemma-name
                        :provenance (config/default-provenance :extraction)}

        ;; Rewrite dependencies: nodes that depended on root now depend on lemma-ref
        g (reduce (fn [g' dep-id]
                    (let [old-deps (get-in g' [:nodes dep-id :dependencies])]
                      (assoc-in g' [:nodes dep-id :dependencies]
                                (-> old-deps (disj root-id) (conj lemma-ref-id)))))
                  g
                  external-dependents)]

    ;; Add the lemma-ref node
    (assoc-in g [:nodes lemma-ref-id] lemma-ref-node)))

(defn- archive-extracted-nodes
  "Move extracted nodes to archived-nodes."
  [g extracted-nodes]
  (let [nodes (:nodes g)
        to-archive (select-keys nodes extracted-nodes)]
    (-> g
        (update :archived-nodes merge to-archive)
        (update :nodes #(apply dissoc % extracted-nodes)))))

;; =============================================================================
;; Main Operation
;; =============================================================================

(defn extract-lemma
  "Extract a verified subgraph as an independent lemma.

   Arguments:
   - graph: The semantic proof graph
   - root-id: The root node of the extraction (will become the lemma conclusion)
   - lemma-name: Name for the new lemma (e.g., \"L1-fourier\")
   - node-ids: (optional) Explicit set of node IDs to extract. If not provided,
               extracts root-id and all its ancestors.

   Operations:
   1. Validates extraction preconditions (using graph/check-independence)
   2. Creates a lemma entry in :lemmas
   3. Replaces extracted nodes with a single :lemma-ref node
   4. Archives the extracted nodes

   Returns {:ok new-graph :lemma lemma-entry} or {:error errors}"
  ([graph root-id lemma-name]
   (extract-lemma graph root-id lemma-name nil))
  ([graph root-id lemma-name node-ids]
   (let [extracted-nodes (collect-extraction-nodes graph root-id node-ids)

         ;; Validate preconditions
         validation (validate-preconditions graph root-id extracted-nodes)]

     (if-not (:valid validation)
       {:error (:errors validation)}

       ;; All good, proceed with extraction
       (let [;; Create lemma entry
             lemma-entry (create-lemma-entry graph root-id extracted-nodes lemma-name)

             ;; Add lemma-ref node (must happen before archiving)
             graph (add-lemma-ref-node graph root-id lemma-name extracted-nodes)

             ;; Archive extracted nodes
             graph (archive-extracted-nodes graph extracted-nodes)

             ;; Add lemma to graph
             graph (assoc-in graph [:lemmas lemma-name] lemma-entry)

             ;; Update version and metadata
             graph (-> graph
                       (graph/increment-version)
                       (graph/update-last-modified)
                       (graph/update-context-budget)
                       (graph/invalidate-caches))]

         ;; Assert graph invariants are maintained
         (validators/assert-valid-graph! graph "extract-lemma postcondition")
         {:ok graph
          :lemma lemma-entry})))))

;; =============================================================================
;; Lemma ID Generation
;; =============================================================================

(defn generate-lemma-name
  "Generate a unique lemma name with format L<n>-<6-hex>."
  [graph prefix]
  (let [existing-count (count (:lemmas graph))
        suffix (config/generate-uuid-prefix)]
    (str (or prefix "L") (inc existing-count) "-" suffix)))
