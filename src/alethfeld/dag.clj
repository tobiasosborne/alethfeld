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

   Returns nil if valid, or a vector of ALL error maps describing inconsistencies:
   - {:type :phantom-child :parent-id ... :child-id ...} - parent lists non-existent child
   - {:type :mismatched-parent :child-id ... :expected-parent ... :actual-parent ...}
   - {:type :orphan-child :child-id ... :claimed-parent ...} - child claims parent but not listed"
  [motes]
  (let [;; Check 1: Every child listed by a parent must exist and point back
        parent-child-errors
        (for [[parent-id parent-mote] motes
              child-id (:children parent-mote)
              :let [child-mote (get motes child-id)]
              :when (or (nil? child-mote)
                        (not= (:parent child-mote) parent-id))]
          (if child-mote
            ;; Child exists but points to wrong parent
            {:type :mismatched-parent
             :child-id child-id
             :expected-parent parent-id
             :actual-parent (:parent child-mote)}
            ;; Child doesn't exist
            {:type :phantom-child
             :parent-id parent-id
             :child-id child-id}))

        ;; Check 2: Every mote claiming a parent must be listed in that parent's children
        ;; Exceptions:
        ;; - Proposed motes: tracked in the proposal structure until approved
        ;; - Rejected motes: archived after proposal rejection, never added to :children
        orphan-errors
        (for [[mote-id mote] motes
              :when (not (#{:proposed :rejected} (:status mote)))  ; Skip proposed/rejected
              :let [claimed-parent (:parent mote)
                    parent-mote (when claimed-parent (get motes claimed-parent))]
              :when (and claimed-parent
                         parent-mote
                         (not (some #{mote-id} (:children parent-mote))))]
          {:type :orphan-child
           :child-id mote-id
           :claimed-parent claimed-parent})

        all-errors (concat parent-child-errors orphan-errors)]
    (when (seq all-errors)
      (vec all-errors))))

;; -----------------------------------------------------------------------------
;; Cycle Detection (DFS)
;; -----------------------------------------------------------------------------

;; Implementation Note: Local Mutable State in a Pure Function
;;
;; The find-cycles function uses a local atom for DFS state tracking. While this
;; module emphasizes pure DAG validation, this use of mutation is intentional
;; and acceptable for the following reasons:
;;
;; 1. **Why three-color DFS?**
;;    The standard algorithm for cycle detection in directed graphs. The three
;;    colors represent node states during traversal:
;;    - :white = unvisited node
;;    - :gray  = currently on the DFS stack (in the active path)
;;    - :black = fully processed (all descendants explored)
;;    A back edge to a :gray node indicates a cycle, as we've found a path from
;;    a node back to one of its ancestors.
;;
;; 2. **Why mutable state (atom)?**
;;    The color map must be shared across all DFS branches to correctly detect
;;    cycles. Pure functional alternatives (threading state through recursion,
;;    using a loop/recur with accumulated state) add significant complexity
;;    without benefit. The atom provides O(1) lookups and updates, matching
;;    the theoretical O(V+E) complexity of the algorithm.
;;
;; 3. **Why this is still "pure" from the caller's perspective:**
;;    - The atom is locally scoped within the function body
;;    - No mutation escapes: the atom is created, used, and discarded
;;    - The function is referentially transparent: same input always produces
;;      the same output, with no observable side effects
;;    - This is analogous to using a local mutable array in an otherwise pure
;;      algorithm - an implementation detail hidden behind a pure interface

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
          ;; Helper to find index of element in vector using Clojure idioms
          find-index (fn [coll item]
                       (first (keep-indexed (fn [idx x] (when (= x item) idx)) coll)))

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
                          cycle-start-idx (find-index current-path neighbor)]
                      (if (some? cycle-start-idx)
                        ;; Return the cycle portion plus back to the start
                        (conj (vec (drop cycle-start-idx current-path)) neighbor)
                        ;; This should never happen: neighbor is gray but not in path
                        ;; indicates a bug in the algorithm
                        (throw (ex-info "Cycle detection logic error: gray node not found in path"
                                       {:node node
                                        :neighbor neighbor
                                        :path current-path
                                        :color-state @color}))))

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

(defn- expected-child-status
  "Return the expected child status based on proposal status."
  [proposal-status]
  (case proposal-status
    :pending :proposed
    :approved :fixed
    :rejected :rejected
    ;; Default for unknown status
    nil))

(defn validate-proposal-atomicity
  "Validate that all children in a proposal share the same fate (atomicity).

   Checks:
   - All proposal children must exist
   - All proposal children must have the same status
   - All proposal children must have the expected status based on proposal state:
     - :pending proposal → children should have :proposed status
     - :approved proposal → children should have :fixed status
     - :rejected proposal → children should have :rejected status

   Returns nil if valid, or a vector of ALL error maps:
   - {:type :missing-proposal-child :parent-id ... :missing-child ...}
   - {:type :atomicity-violation :parent-id ... :children-statuses {...}}
   - {:type :non-proposed-children :parent-id ... :expected-status ... :children-statuses {...}}"
  [motes]
  (let [errors
        (for [[parent-id parent-mote] motes
              :let [proposal (:proposal parent-mote)]
              :when proposal
              :let [proposal-children (:children proposal)
                    child-motes (map #(get motes %) proposal-children)
                    missing-children (filter #(nil? (get motes %)) proposal-children)]
              :when (or (seq missing-children)
                        (let [statuses (map :status child-motes)
                              status-set (set statuses)
                              proposal-status (:status proposal)
                              expected (expected-child-status proposal-status)]
                          (or (> (count status-set) 1)
                              (and expected
                                   (seq status-set)
                                   (not= (first status-set) expected)))))]
          ;; Generate error for this proposal
          (if (seq missing-children)
            ;; Report all missing children
            (for [missing missing-children]
              {:type :missing-proposal-child
               :parent-id parent-id
               :missing-child missing})
            ;; Check status consistency
            (let [statuses (map :status child-motes)
                  status-set (set statuses)
                  proposal-status (:status proposal)
                  expected (expected-child-status proposal-status)]
              (cond
                ;; Check for mixed statuses among children
                (> (count status-set) 1)
                [{:type :atomicity-violation
                  :parent-id parent-id
                  :children-statuses (zipmap proposal-children statuses)}]

                ;; Check for wrong expected status
                (and expected
                     (seq status-set)
                     (not= (first status-set) expected))
                [{:type :non-proposed-children
                  :parent-id parent-id
                  :expected-status expected
                  :children-statuses (zipmap proposal-children statuses)}]))))
        ;; Flatten nested errors (missing children produces a seq per proposal)
        flat-errors (flatten errors)]
    (when (seq flat-errors)
      (vec flat-errors))))

;; -----------------------------------------------------------------------------
;; Comprehensive Graph Validation
;; -----------------------------------------------------------------------------

(defn validate-mote-graph
  "Run all validations on a mote collection.

   Returns a result map:
   {:valid? true/false
    :errors [...]}

   Each error includes a :category key (:parent-child, :cycle, :broken-refs, :atomicity)
   along with the specific error details.

   Error details are stored in category-specific keys:
   - :parent-child - includes :error (first error for backward compat) and :all-errors (vector)
   - :cycle - includes :cycle (vector of mote IDs forming cycle path)
   - :broken-refs - includes :broken-refs (vector of broken reference descriptors)
   - :atomicity - includes :error (first error for backward compat) and :all-errors (vector)"
  [motes]
  (let [;; Run each validation once and capture results
        pc-err (validate-parent-child motes)
        cycle-err (find-cycles motes)
        refs-err (validate-refs motes)
        atomicity-err (validate-proposal-atomicity motes)

        ;; Build errors list only for failed validations
        ;; Include both :error (first, for backward compat) and :all-errors (all)
        errors (cond-> []
                 pc-err
                 (conj {:category :parent-child
                        :error (first pc-err)       ; backward compat
                        :all-errors pc-err})        ; new: all errors

                 cycle-err
                 (conj {:category :cycle :cycle cycle-err})

                 refs-err
                 (conj {:category :broken-refs :broken-refs refs-err})

                 atomicity-err
                 (conj {:category :atomicity
                        :error (first atomicity-err)  ; backward compat
                        :all-errors atomicity-err}))] ; new: all errors
    {:valid? (empty? errors)
     :errors errors}))
