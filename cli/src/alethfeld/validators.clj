(ns alethfeld.validators
  "Semantic validators for proof graphs beyond schema validation.
    Checks referential integrity, acyclicity, scope validity, and taint correctness."
   (:require [clojure.set :as set]
             [clojure.string :as str]
             [alethfeld.graph :as g]
             [alethfeld.schema :as schema]))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn node-ids
  "Get the set of all node IDs in the graph."
  [graph]
  (set (keys (:nodes graph))))

;; =============================================================================
;; Referential Integrity
;; =============================================================================

(defn check-dependency-refs
  "Check that all :dependencies reference existing nodes."
  [graph]
  (let [ids (node-ids graph)
        errors (for [[node-id node] (:nodes graph)
                     dep-id (:dependencies node)
                     :when (not (contains? ids dep-id))]
                 {:type :missing-dependency
                  :node-id node-id
                  :missing-ref dep-id
                  :message (str "Node " node-id " depends on non-existent node " dep-id)})]
    (vec errors)))

(defn check-parent-refs
  "Check that all :parent references point to existing nodes."
  [graph]
  (let [ids (node-ids graph)
        errors (for [[node-id node] (:nodes graph)
                     :let [parent (:parent node)]
                     :when (and parent (not (contains? ids parent)))]
                 {:type :missing-parent
                  :node-id node-id
                  :missing-ref parent
                  :message (str "Node " node-id " has non-existent parent " parent)})]
    (vec errors)))

(defn check-lemma-refs
  "Check that :lemma-ref nodes reference existing lemmas."
  [graph]
  (let [lemma-ids (set (keys (:lemmas graph)))
        errors (for [[node-id node] (:nodes graph)
                     :when (= :lemma-ref (:type node))
                     :let [lemma-id (:lemma-id node)]
                     :when (not (contains? lemma-ids lemma-id))]
                 {:type :missing-lemma
                  :node-id node-id
                  :missing-ref lemma-id
                  :message (str "Node " node-id " references non-existent lemma " lemma-id)})]
    (vec errors)))

(defn check-external-refs
  "Check that :external-ref nodes reference existing external-refs."
  [graph]
  (let [ext-ids (set (keys (:external-refs graph)))
        errors (for [[node-id node] (:nodes graph)
                     :when (= :external-ref (:type node))
                     :let [ext-id (:external-id node)]
                     :when (not (contains? ext-ids ext-id))]
                 {:type :missing-external-ref
                  :node-id node-id
                  :missing-ref ext-id
                  :message (str "Node " node-id " references non-existent external-ref " ext-id)})]
    (vec errors)))

(defn check-symbol-refs
  "Check that symbol :introduced-at references existing nodes."
  [graph]
  (let [ids (node-ids graph)
        errors (for [[sym-id sym] (:symbols graph)
                     :let [intro-at (:introduced-at sym)]
                     :when (not (contains? ids intro-at))]
                 {:type :missing-symbol-intro
                  :symbol-id sym-id
                  :missing-ref intro-at
                  :message (str "Symbol " sym-id " introduced at non-existent node " intro-at)})]
    (vec errors)))

(defn check-lemma-root-refs
  "Check that lemma :root-node references exist in archived-nodes."
  [graph]
  (let [archived-ids (set (keys (:archived-nodes graph)))
        all-ids (set/union archived-ids (node-ids graph))
        errors (for [[lemma-id lemma] (:lemmas graph)
                     :let [root (:root-node lemma)]
                     :when (not (contains? all-ids root))]
                 {:type :missing-lemma-root
                  :lemma-id lemma-id
                  :missing-ref root
                  :message (str "Lemma " lemma-id " has non-existent root-node " root)})]
    (vec errors)))

(defn check-referential-integrity
  "Run all referential integrity checks."
  [graph]
  (concat
   (check-dependency-refs graph)
   (check-parent-refs graph)
   (check-lemma-refs graph)
   (check-external-refs graph)
   (check-symbol-refs graph)
   (check-lemma-root-refs graph)))

;; =============================================================================
;; Acyclicity
;; =============================================================================

(defn- dfs-visit
  "Perform DFS visit on a node, returning updated state.
   State is {:color map, :parent map, :cycle nil-or-vec}.
   Colors: :white (unvisited), :gray (in-progress), :black (done)."
  [nodes node state]
  (let [{:keys [color parent]} state
        node-color (get color node :white)]
    (case node-color
      :black state  ; Already fully processed
      :gray  state  ; Back edge detected elsewhere
      :white
      (let [state (assoc-in state [:color node] :gray)
            deps (get-in nodes [node :dependencies] #{})
            valid-deps (filter #(contains? nodes %) deps)]
        ;; Check for back edges (cycle detection)
        (if-let [gray-dep (first (filter #(= :gray (get (:color state) %)) valid-deps))]
          ;; Found cycle - reconstruct path
          (let [cycle-path (loop [path [gray-dep node]
                                  curr (get parent node)]
                             (if (or (nil? curr) (= curr gray-dep))
                               (conj path gray-dep)
                               (recur (conj path curr) (get parent curr))))]
            (assoc state :cycle (vec (reverse (butlast cycle-path)))))
          ;; No cycle yet - visit unvisited deps
          (let [white-deps (filter #(= :white (get (:color state) % :white)) valid-deps)
                state (reduce (fn [s d] (assoc-in s [:parent d] node)) state white-deps)
                state (reduce (fn [s d]
                                (if (:cycle s)
                                  s  ; Stop if cycle found
                                  (dfs-visit nodes d s)))
                              state white-deps)]
            (if (:cycle state)
              state
              (assoc-in state [:color node] :black))))))))

(defn find-cycle
  "Find a cycle in the dependency graph using DFS with coloring.
   Returns nil if no cycle, or a vector of node IDs forming the cycle."
  [graph]
  (let [nodes (:nodes graph)]
    (when (seq nodes)
      (let [initial-state {:color (zipmap (keys nodes) (repeat :white))
                           :parent {}
                           :cycle nil}
            final-state (reduce (fn [state node]
                                  (if (:cycle state)
                                    (reduced state)  ; Stop early if cycle found
                                    (if (= :white (get (:color state) node))
                                      (dfs-visit nodes node state)
                                      state)))
                                initial-state
                                (keys nodes))]
        (:cycle final-state)))))

(defn check-acyclicity
  "Check that the dependency graph has no cycles."
  [graph]
  (if-let [cycle (find-cycle graph)]
    [{:type :dependency-cycle
      :cycle cycle
      :message (str "Dependency cycle detected: " (str/join " -> " cycle))}]
    []))

;; =============================================================================
;; Scope Validation
;; =============================================================================

(defn check-scope-validity
  "Check that all nodes have valid :scope entries.
   Uses batch scope computation for O(n) instead of O(n²) performance."
  [graph]
  (let [all-scopes (g/compute-all-scopes graph)
        errors (for [[node-id node] (:nodes graph)
                     :let [actual-scope (:scope node)
                           valid-scope (get all-scopes node-id #{})
                           invalid-entries (set/difference actual-scope valid-scope)]
                     :when (seq invalid-entries)]
                 {:type :invalid-scope
                  :node-id node-id
                  :invalid-entries invalid-entries
                  :message (str "Node " node-id " has invalid scope entries: " invalid-entries)})]
    (vec errors)))

(defn check-discharge-validity
  "Check that :local-discharge nodes discharge valid in-scope ancestors."
  [graph]
  (let [nodes (:nodes graph)
        all-scopes (g/compute-all-scopes graph)
        errors (for [[node-id node] nodes
                     :when (= :local-discharge (:type node))
                     :let [target (:discharges node)
                           ancestors (g/get-ancestors graph node-id)
                           in-scope (get all-scopes node-id #{})]]
                 (cond
                   (not (contains? ancestors target))
                   {:type :discharge-not-ancestor
                    :node-id node-id
                    :target target
                    :message (str "Node " node-id " discharges " target " which is not an ancestor")}

                   (not (contains? in-scope target))
                   {:type :discharge-out-of-scope
                    :node-id node-id
                    :target target
                    :message (str "Node " node-id " discharges " target " which is not in scope")}

                   :else nil))]
    (vec (remove nil? errors))))

(defn check-scopes
  "Run all scope validation checks."
  [graph]
  (concat
   (check-scope-validity graph)
   (check-discharge-validity graph)))

;; =============================================================================
;; Taint Validation
;; =============================================================================

(defn check-taint-correctness
  "Check that all nodes have correctly computed :taint values."
  [graph]
  (let [errors (for [[node-id node] (:nodes graph)
                     :let [actual-taint (:taint node)
                           expected-taint (g/compute-taint graph node-id)]
                     :when (not= actual-taint expected-taint)]
                 {:type :incorrect-taint
                  :node-id node-id
                  :actual actual-taint
                  :expected expected-taint
                  :message (str "Node " node-id " has taint " actual-taint " but should be " expected-taint)})]
    (vec errors)))

;; =============================================================================
;; Combined Validation
;; =============================================================================

(defn validate-semantics
  "Run all semantic validations on a graph.
   Returns {:valid true} or {:valid false :errors [...]}."
  [graph]
  (let [errors (concat
                (check-referential-integrity graph)
                (check-acyclicity graph)
                (check-scopes graph)
                (check-taint-correctness graph))]
    (if (empty? errors)
      {:valid true}
      {:valid false :errors (vec errors)})))

;; =============================================================================
;; Graph Invariant Predicates
;; =============================================================================

(defn valid-graph?
  "Check if a graph satisfies all invariants (schema + semantics).
   Returns true if valid, false otherwise.

   For use in assertions within mutation functions to catch
   invariant violations at the source."
  [graph]
  (and (:valid (schema/validate-schema graph))
       (:valid (validate-semantics graph))))

(defn validate-graph
  "Full graph validation combining schema and semantic checks.
   Returns {:valid true} or {:valid false :schema-errors [...] :semantic-errors [...]}.

   Use this when you need detailed error information.
   Use valid-graph? when you just need a boolean."
  [graph]
  (let [schema-result (schema/validate-schema graph)
        semantic-result (validate-semantics graph)]
    (if (and (:valid schema-result) (:valid semantic-result))
      {:valid true}
      {:valid false
       :schema-errors (when-not (:valid schema-result) (:errors schema-result))
       :semantic-errors (when-not (:valid semantic-result) (:errors semantic-result))})))

(defn assert-valid-graph!
  "Assert that a graph satisfies all invariants, throwing with details on failure.

   For use in mutation functions:
   (assert-valid-graph! new-graph \"add-node postcondition\")

   Throws AssertionError with detailed validation errors if invalid."
  ([graph]
   (assert-valid-graph! graph "graph invariant"))
  ([graph context]
   (let [result (validate-graph graph)]
     (when-not (:valid result)
       (throw (AssertionError.
               (str context " violated: "
                    (when-let [se (:schema-errors result)]
                      (str "schema errors: " (pr-str se) " "))
                    (when-let [ve (:semantic-errors result)]
                      (str "semantic errors: " (pr-str ve))))))))))
