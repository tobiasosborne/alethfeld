(ns alethfeld.graph
  "Pure query functions for semantic proof graphs.
   All functions are stateless and never mutate the input graph."
  (:require [clojure.set :as set]
            [alethfeld.config :as config]))

;; =============================================================================
;; Node Queries
;; =============================================================================

(defn node-ids
  "Get the set of all node IDs in the graph."
  [graph]
  (set (keys (:nodes graph))))

(defn get-node
  "Get a node by ID, or nil if not found."
  [graph node-id]
  (get-in graph [:nodes node-id]))

(defn nodes-of-type
  "Get all nodes of a specific type."
  [graph type]
  (->> (:nodes graph)
       (filter (fn [[_ node]] (= type (:type node))))
       (into {})))

(defn nodes-with-status
  "Get all nodes with a specific status."
  [graph status]
  (->> (:nodes graph)
       (filter (fn [[_ node]] (= status (:status node))))
       (into {})))

;; =============================================================================
;; Dependency Graph Queries
;; =============================================================================

(defn- build-reverse-deps
  "Build a reverse dependency map (dependents by node ID).
   Caches result in graph metadata for reuse."
  [graph]
  (if-let [cached (get-in (meta graph) [:_reverse-deps])]
    cached
    (let [dependents (reduce (fn [acc [nid node]]
                               (reduce (fn [a dep]
                                         (update a dep (fnil conj #{}) nid))
                                       acc
                                       (:dependencies node)))
                             {}
                             (:nodes graph))]
      dependents)))

(defn- get-reverse-deps
  "Get or build the reverse dependency map, with caching via metadata."
  [graph]
  (or (get-in (meta graph) [:_reverse-deps])
      (build-reverse-deps graph)))

(defn get-ancestors
   "Get all transitive dependencies of a node (ancestors in the DAG).
    Does not include the node itself."
   [graph node-id]
  (let [nodes (:nodes graph)]
    (loop [stack [node-id]
           visited #{}]
      (if (empty? stack)
        (disj visited node-id)
        (let [current (peek stack)
              stack (pop stack)]
          (if (contains? visited current)
            (recur stack visited)
            (let [deps (get-in nodes [current :dependencies] #{})]
              (recur (into stack deps) (conj visited current)))))))))

(defn get-descendants
  "Get all nodes that transitively depend on this node.
   Does not include the node itself."
  [graph node-id]
  (let [dependents (get-reverse-deps graph)]
    (loop [stack [node-id]
           visited #{}]
      (if (empty? stack)
        (disj visited node-id)
        (let [current (peek stack)
              stack (pop stack)]
          (if (contains? visited current)
            (recur stack visited)
            (let [deps (get dependents current #{})]
              (recur (into stack deps) (conj visited current)))))))))

(defn get-direct-dependents
  "Get nodes that directly depend on this node (one hop)."
  [graph node-id]
  (->> (:nodes graph)
       (filter (fn [[_ node]]
                 (contains? (:dependencies node) node-id)))
       (map first)
       set))

(defn topological-sort
  "Sort node IDs in topological order (dependencies first).

   Arities:
   - (topological-sort graph) - Sort all nodes
   - (topological-sort graph node-ids) - Sort only specified nodes
   - (topological-sort graph :targets target-ids) - Partial sort for targets only

   Options (keyword args in 3rd arity):
   - :targets - Set of target node IDs. Computes closure (ancestors + targets)
                and sorts only those nodes. More efficient for single-node queries.

   Returns a vector of node IDs."
  ([graph]
   (topological-sort graph (node-ids graph)))
  ([graph node-ids-to-sort]
   (let [nodes (:nodes graph)
         node-set (set node-ids-to-sort)
         ;; Filter to only nodes we're sorting
         relevant-deps (fn [nid]
                         (set/intersection (get-in nodes [nid :dependencies] #{})
                                           node-set))]
     (loop [remaining node-set
            result []
            in-degree (into {} (map (fn [nid]
                                      [nid (count (relevant-deps nid))])
                                    node-set))]
       (if (empty? remaining)
         result
         (let [zero-in (first (filter #(zero? (get in-degree % 0)) remaining))]
           (if zero-in
             (let [dependents (->> remaining
                                   (filter #(contains? (relevant-deps %) zero-in)))]
               (recur (disj remaining zero-in)
                      (conj result zero-in)
                      (reduce (fn [d n] (update d n dec)) in-degree dependents)))
             ;; Cycle detected - return partial result
             result))))))
  ([graph _ & {:keys [targets]}]
   ;; Partial mode: compute only the closure needed for target nodes
   ;; This avoids computing in-degrees for the entire graph
   (when (seq targets)
     (let [target-set (set targets)
           ;; Compute closure: targets + all ancestors of targets
           closure (reduce (fn [acc target]
                             (into (conj acc target)
                                   (get-ancestors graph target)))
                           #{}
                           target-set)]
       ;; Sort only the closure
       (topological-sort graph closure)))))

;; =============================================================================
;; Scope Queries
;; =============================================================================

(defn compute-valid-scope
  "Compute which local-assume nodes are validly in scope for a node."
  [graph node-id]
  (let [nodes (:nodes graph)
        ancestors (get-ancestors graph node-id)
        ;; Find local-assume nodes among ancestors
        assumes (->> ancestors
                     (filter #(= :local-assume (get-in nodes [% :type])))
                     set)
        ;; Find discharged assumptions among ancestors
        discharged (->> ancestors
                        (filter #(= :local-discharge (get-in nodes [% :type])))
                        (map #(get-in nodes [% :discharges]))
                        (remove nil?)
                        set)]
    (set/difference assumes discharged)))

(defn compute-all-scopes
  "Compute valid scopes for all nodes in a single topological pass.
   Returns a map of {node-id -> scope-set}.
   More efficient than calling compute-valid-scope for each node individually."
  [graph]
  (let [nodes (:nodes graph)
        sorted (topological-sort graph)
        ;; Build ancestors map incrementally in topo order
        ;; Each node's ancestors = deps + all their ancestors
        ancestors-map (reduce
                       (fn [acc nid]
                         (let [deps (get-in nodes [nid :dependencies] #{})
                               ancs (reduce (fn [a d]
                                              (set/union a (get acc d #{}) #{d}))
                                            #{}
                                            deps)]
                           (assoc acc nid ancs)))
                       {}
                       sorted)]
    ;; Compute scope for each node using precomputed ancestors
    (reduce (fn [acc nid]
              (let [ancestors (get ancestors-map nid #{})
                    assumes (->> ancestors
                                 (filter #(= :local-assume (get-in nodes [% :type])))
                                 set)
                    discharged (->> ancestors
                                    (filter #(= :local-discharge (get-in nodes [% :type])))
                                    (map #(get-in nodes [% :discharges]))
                                    (remove nil?)
                                    set)]
                (assoc acc nid (set/difference assumes discharged))))
            {}
            sorted)))

(defn active-assumptions
  "Get all active assumptions (global and local) in scope for a node."
  [graph node-id]
  (let [nodes (:nodes graph)
        ancestors (get-ancestors graph node-id)
        ;; Global assumptions
        global-assumes (->> (:nodes graph)
                            (filter (fn [[_ node]] (= :assumption (:type node))))
                            (map first)
                            (filter #(contains? ancestors %))
                            set)
        ;; Local assumptions in scope
        local-scope (compute-valid-scope graph node-id)]
    (set/union global-assumes local-scope)))

;; =============================================================================
;; Taint Queries
;; =============================================================================

(defn compute-taint
  "Compute the expected taint for a node based on its status and dependencies.
   Special handling for lemma-ref nodes: their taint is based on the lemma's taint."
  [graph node-id]
  (let [node (get-node graph node-id)
        status (:status node)
        node-type (:type node)]
    (cond
      (= :admitted status) :self-admitted
      (= :rejected status) :tainted
      ;; Lemma-ref nodes inherit taint from the referenced lemma
      (= :lemma-ref node-type)
      (let [lemma-id (:lemma-id node)
            lemma (get-in graph [:lemmas lemma-id])]
        (if (and lemma (#{:tainted :self-admitted} (:taint lemma)))
          :tainted
          :clean))
      :else
      (let [deps (:dependencies node)
            dep-taints (map #(get-in graph [:nodes % :taint]) deps)]
        (if (some #{:tainted :self-admitted} dep-taints)
          :tainted
          :clean)))))

(defn tainted-nodes
  "Get all nodes that are tainted (either self-admitted or propagated)."
  [graph]
  (->> (:nodes graph)
       (filter (fn [[_ node]]
                 (#{:tainted :self-admitted} (:taint node))))
       (into {})))

(defn recompute-all-taints
  "Recompute taint values for all nodes in topological order.
   Returns the graph with updated taint values."
  [graph]
  (let [sorted-ids (topological-sort graph)]
    (reduce (fn [g nid]
              (let [new-taint (compute-taint g nid)]
                (assoc-in g [:nodes nid :taint] new-taint)))
            graph
            sorted-ids)))

;; =============================================================================
;; Independence Check (for lemma extraction)
;; =============================================================================

(defn check-independence
  "Check if a set of nodes can be extracted as an independent lemma.
   Returns {:valid true} or {:valid false :errors [...]}."
  [graph root-id node-ids-set]
  (let [nodes (:nodes graph)
        all-node-ids (node-ids graph)
        errors (atom [])]

    ;; Check 1: Root must be in the set
    (when-not (contains? node-ids-set root-id)
      (swap! errors conj {:type :root-not-in-set
                          :message (str "Root node " root-id " not in extraction set")}))

    ;; Check 2: All nodes in set must exist
    (doseq [nid node-ids-set]
      (when-not (contains? all-node-ids nid)
        (swap! errors conj {:type :node-not-found
                            :node-id nid
                            :message (str "Node " nid " not found in graph")})))

    ;; Check 3: All nodes must be verified or admitted (admitted results in tainted lemma)
    (doseq [nid node-ids-set]
      (let [node (get nodes nid)]
        (when (and node (not (#{:verified :admitted} (:status node))))
          (swap! errors conj {:type :node-not-verified
                              :node-id nid
                              :status (:status node)
                              :message (str "Node " nid " has status " (:status node) ", must be :verified or :admitted")}))))

    ;; Check 4: Only root can be depended on from outside
    (doseq [nid node-ids-set]
      (when (not= nid root-id)
        (let [external-dependents (set/difference (get-direct-dependents graph nid)
                                                   node-ids-set)]
          (when (seq external-dependents)
            (swap! errors conj {:type :external-dependency-on-non-root
                                :node-id nid
                                :external-dependents external-dependents
                                :message (str "Node " nid " has external dependents: " external-dependents)})))))

    ;; Check 5: Internal dependencies must be satisfied
    (doseq [nid node-ids-set]
      (let [node (get nodes nid)
            deps (:dependencies node #{})
            external-deps (set/difference deps node-ids-set)]
        (doseq [ext-dep external-deps]
          (let [ext-node (get nodes ext-dep)]
            (when ext-node
              (when-not (#{:assumption :verified :lemma-ref}
                         (if (= :verified (:status ext-node))
                           :verified
                           (:type ext-node)))
                (swap! errors conj {:type :invalid-external-dep
                                    :node-id nid
                                    :external-dep ext-dep
                                    :message (str "Node " nid " depends on " ext-dep " which is not a valid external dependency")})))))))

    ;; Check 6: Scope must be balanced (local-assume has matching discharge in set)
    (let [local-assumes (->> node-ids-set
                             (filter #(= :local-assume (get-in nodes [% :type])))
                             set)
          discharges (->> node-ids-set
                          (filter #(= :local-discharge (get-in nodes [% :type])))
                          (map #(get-in nodes [% :discharges]))
                          set)]
      (let [unbalanced (set/difference local-assumes discharges)]
        (doseq [la unbalanced]
          (swap! errors conj {:type :unbalanced-scope
                              :local-assume la
                              :message (str "Local-assume " la " has no matching discharge in extraction set")}))))

    (if (empty? @errors)
      {:valid true}
      {:valid false :errors @errors})))

;; =============================================================================
;; Token Estimation
;; =============================================================================

(defn estimate-node-tokens
  "Estimate token count for a single node."
  [node]
  (let [statement-chars (count (or (:statement node) ""))
        base-overhead 50]  ; ID, type, status, etc.
    (int (+ base-overhead (* statement-chars config/tokens-per-char)))))

(defn estimate-graph-tokens
  "Estimate total token count for a graph."
  [graph]
  (let [node-tokens (reduce + 0 (map estimate-node-tokens (vals (:nodes graph))))
        lemma-tokens (* 100 (count (:lemmas graph)))
        ref-tokens (* 150 (count (:external-refs graph)))
        overhead 500]
    (+ node-tokens lemma-tokens ref-tokens overhead)))

(defn update-context-budget
  "Update the context budget estimate in the graph."
  [graph]
  (assoc-in graph [:metadata :context-budget :current-estimate]
            (estimate-graph-tokens graph)))

;; =============================================================================
;; Cache Management
;; =============================================================================

(defn invalidate-caches
  "Invalidate cached reverse dependencies when graph structure changes.
   Returns a new graph with caches cleared."
  [graph]
  (vary-meta graph dissoc :_reverse-deps))

;; =============================================================================
;; Graph Modification Helpers
;; =============================================================================

(defn increment-version
  "Increment the graph version number."
  [graph]
  (update graph :version inc))

(defn update-last-modified
  "Update the last-modified timestamp."
  [graph]
  (assoc-in graph [:metadata :last-modified] (config/current-iso8601)))

(defn would-create-cycle?
  "Check if adding a node with given dependencies would create a cycle."
  [graph new-node-id dependencies]
  (let [nodes (:nodes graph)
        ;; Temporarily add the node
        temp-graph (assoc-in graph [:nodes new-node-id]
                             {:dependencies dependencies})]
    ;; Check if any dependency is a descendant of the new node
    (let [descendants (get-descendants temp-graph new-node-id)]
      (boolean (some descendants dependencies)))))
