(ns alethfeld.dag
  "DAG validation functions for mote graphs.

   These functions validate the structural integrity of mote collections,
   checking parent-child relationships, detecting cycles in the assumption
   graph, validating references, and ensuring proposal atomicity."
  (:require [clojure.set :as set]))

;; -----------------------------------------------------------------------------
;; Internal Helpers
;; -----------------------------------------------------------------------------

(defn- internal-refs
  "Extract internal reference IDs from a mote's assumptions."
  [mote]
  (->> (:assumptions mote)
       (filter #(= :internal (:type %)))
       (map :ref)))

(defn- dependency-refs
  "Extract dependency reference IDs from a mote's :depends-on."
  [mote]
  (map :ref (:depends-on mote)))

;; -----------------------------------------------------------------------------
;; Parent-Child Validation
;; -----------------------------------------------------------------------------

(defn validate-parent-child
  "Validate bidirectional parent-child consistency.

   Checks:
   - Every child listed in a parent's :children must exist
   - Every child must have the correct :parent pointing back
   - Every mote claiming a :parent must be listed in that parent's :children

   Returns nil if valid, or an error map describing the first inconsistency:
   - {:type :phantom-child :parent-id ... :child-id ...} - parent lists non-existent child
   - {:type :mismatched-parent :child-id ... :expected-parent ... :actual-parent ...}
   - {:type :orphan-child :child-id ... :claimed-parent ...} - child claims parent but not listed"
  [motes]
  (or
   ;; Check 1: Every child listed by a parent must exist and point back
   (some
    (fn [[parent-id parent-mote]]
      (some
       (fn [child-id]
         (if-let [child-mote (get motes child-id)]
           ;; Child exists - check it points back
           (when (not= (:parent child-mote) parent-id)
             {:type :mismatched-parent
              :child-id child-id
              :expected-parent parent-id
              :actual-parent (:parent child-mote)})
           ;; Child doesn't exist
           {:type :phantom-child
            :parent-id parent-id
            :child-id child-id}))
       (:children parent-mote)))
    motes)

   ;; Check 2: Every mote claiming a parent must be listed in that parent's children
   ;; Exceptions:
   ;; - Proposed motes: tracked in the proposal structure until approved
   ;; - Rejected motes: archived after proposal rejection, never added to :children
   (some
    (fn [[mote-id mote]]
      (when-not (#{:proposed :rejected} (:status mote))  ; Skip proposed/rejected
        (when-let [claimed-parent (:parent mote)]
          (when-let [parent-mote (get motes claimed-parent)]
            (when-not (some #{mote-id} (:children parent-mote))
              {:type :orphan-child
               :child-id mote-id
               :claimed-parent claimed-parent})))))
    motes)))

;; -----------------------------------------------------------------------------
;; Cycle Detection (DFS)
;; -----------------------------------------------------------------------------

(defn find-cycles
  "Detect cycles in the reference/dependency graph using DFS.

   Edges are formed from:
   - Internal refs (assumptions with :type :internal)
   - Dependencies (:depends-on references)

   Returns nil if no cycles exist, or a vector of mote IDs forming a cycle path.
   The cycle path includes all nodes in the cycle."
  [motes]
  (when (seq motes)
    (let [;; Build adjacency list from internal refs AND dependencies
          adjacency (into {}
                         (map (fn [[id mote]]
                                [id (vec (concat (internal-refs mote)
                                                 (dependency-refs mote)))])
                              motes))

          ;; DFS state: :white = unvisited, :gray = in current path, :black = done
          color (atom (zipmap (keys motes) (repeat :white)))

          ;; DFS visit function - returns cycle path if found, nil otherwise
          ;; path includes the current node at the end
          dfs-visit
          (fn dfs-visit [node path]
            (swap! color assoc node :gray)
            (let [current-path (conj path node)
                  neighbors (get adjacency node [])]
              (or
               ;; Check each neighbor
               (some
                (fn [neighbor]
                  (case (get @color neighbor :white)
                    :gray  ; Found back edge - cycle!
                    (let [;; Find where the cycle starts in the path
                          cycle-start-idx (.indexOf current-path neighbor)]
                      (if (>= cycle-start-idx 0)
                        ;; Return the cycle portion plus back to the start
                        (conj (vec (drop cycle-start-idx current-path)) neighbor)
                        ;; Fallback: neighbor is gray but not in path (shouldn't happen)
                        [node neighbor node]))

                    :white ; Unvisited - recurse
                    (dfs-visit neighbor current-path)

                    :black ; Already processed - no cycle here
                    nil))
                neighbors)

               ;; Done with this node
               (do
                 (swap! color assoc node :black)
                 nil))))]

      ;; Run DFS from each unvisited node
      (some
       (fn [node]
         (when (= :white (get @color node))
           (dfs-visit node [])))
       (keys motes)))))

;; -----------------------------------------------------------------------------
;; Reference Validation
;; -----------------------------------------------------------------------------

(defn validate-refs
  "Validate that all internal refs and dependencies point to existing motes.

   Checks:
   - Internal refs (assumptions with :type :internal)
   - Dependencies (:depends-on references)

   External refs are not validated (they point outside the project).

   Returns nil if all refs are valid, or a vector of broken ref descriptors:
   [{:mote-id \"1\" :ref \"missing-id\" :ref-type :assumption|:dependency} ...]"
  [motes]
  (let [existing-ids (set (keys motes))
        broken-assumption-refs
        (for [[mote-id mote] motes
              ref-id (internal-refs mote)
              :when (not (contains? existing-ids ref-id))]
          {:mote-id mote-id :ref ref-id :ref-type :assumption})
        broken-dependency-refs
        (for [[mote-id mote] motes
              ref-id (dependency-refs mote)
              :when (not (contains? existing-ids ref-id))]
          {:mote-id mote-id :ref ref-id :ref-type :dependency})
        broken-refs (concat broken-assumption-refs broken-dependency-refs)]
    (when (seq broken-refs)
      (vec broken-refs))))

;; -----------------------------------------------------------------------------
;; Proposal Atomicity Validation
;; -----------------------------------------------------------------------------

(defn validate-proposal-atomicity
  "Validate that all children in a proposal share the same fate (atomicity).

   Checks:
   - All proposal children must exist
   - All proposal children must have the same status

   Returns nil if valid, or an error map:
   - {:type :missing-proposal-child :parent-id ... :missing-child ...}
   - {:type :atomicity-violation :parent-id ... :children-statuses {...}}"
  [motes]
  (some
   (fn [[parent-id parent-mote]]
     (when-let [proposal (:proposal parent-mote)]
       (let [proposal-children (:children proposal)
             child-motes (map #(get motes %) proposal-children)]
         (cond
           ;; Check for missing children
           (some nil? child-motes)
           (let [missing (first (filter #(nil? (get motes %)) proposal-children))]
             {:type :missing-proposal-child
              :parent-id parent-id
              :missing-child missing})

           ;; Check status consistency
           :else
           (let [statuses (map :status child-motes)
                 status-set (set statuses)]
             (when (> (count status-set) 1)
               {:type :atomicity-violation
                :parent-id parent-id
                :children-statuses (zipmap proposal-children statuses)}))))))
   motes))

;; -----------------------------------------------------------------------------
;; Comprehensive Graph Validation
;; -----------------------------------------------------------------------------

(defn validate-mote-graph
  "Run all validations on a mote collection.

   Returns a result map:
   {:valid? true/false
    :errors [...]}

   Each error includes a :category key (:parent-child, :cycle, :broken-refs, :atomicity)
   along with the specific error details."
  [motes]
  (let [;; Run each validation once and capture results
        pc-err (validate-parent-child motes)
        cycle-err (find-cycles motes)
        refs-err (validate-refs motes)
        atomicity-err (validate-proposal-atomicity motes)

        ;; Build errors list only for failed validations
        errors (cond-> []
                 pc-err
                 (conj {:category :parent-child :error pc-err})

                 cycle-err
                 (conj {:category :cycle :cycle cycle-err})

                 refs-err
                 (conj {:category :broken-refs :broken-refs refs-err})

                 atomicity-err
                 (conj {:category :atomicity :error atomicity-err}))]
    {:valid? (empty? errors)
     :errors errors}))
