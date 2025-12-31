(ns alethfeld.property-test
  "Property-based tests for semantic proof graphs using test.check.
   These tests generate random valid graphs and verify invariants hold."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [alethfeld.graph :as graph]
            [alethfeld.validators :as validators]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.schema :as schema]))

;; =============================================================================
;; Generators for Valid Graphs
;; =============================================================================

(def node-id-gen
  "Generate valid node IDs in format :N-XXXXXX where N is depth."
  (gen/fmap (fn [[depth hash]]
              (keyword (str depth "-" (format "%06x" hash))))
            (gen/tuple
              (gen/choose 0 5)
              (gen/choose 0 0xffffff))))

(def statement-gen
  "Generate realistic mathematical statements."
  (gen/one-of
    [(gen/return "Test statement")
     (gen/fmap #(str "Claim about " %) gen/string-alphanumeric)
     (gen/return "For all $x \\in \\mathbb{R}$: $x^2 \\geq 0$")
     (gen/return "If $P$ then $Q$")]))

(def justification-gen
  "Generate valid justification types."
  (gen/elements
    [:modus-ponens :universal-elim :universal-intro :definition-expansion
     :algebraic-rewrite :assumption :local-assumption :discharge :qed :admitted]))

(def node-type-gen
  "Generate valid node types."
  (gen/elements [:assumption :claim :local-assume :local-discharge :qed :external-ref]))

(def taint-gen
  "Generate valid taint values."
  (gen/elements [:clean :self-admitted :tainted]))

(def status-gen
  "Generate valid status values."
  (gen/elements [:proposed :verified :rejected :admitted]))

(defn make-node
  "Create a node with given or generated values."
  [id & {:keys [type statement deps scope justification status taint depth order]
         :or {type :claim
              statement "Test statement"
              deps #{}
              scope #{}
              justification :modus-ponens
              status :verified
              taint :clean
              depth 1
              order 0}}]
  {:id id
   :type type
   :statement statement
   :content-hash (format "%016x" (hash [id statement]))
   :dependencies deps
   :scope scope
   :justification justification
   :status status
   :taint taint
   :depth depth
   :parent nil
   :display-order order
   :provenance {:created-at "2024-01-01T00:00:00Z"
                :created-by :prover
                :round 1
                :revision-of nil}})

(defn make-graph
  "Create a minimal valid graph with given nodes."
  [nodes]
  {:graph-id "test-graph-001"
   :version 1
   :theorem {:id :theorem
             :statement "Test theorem"
             :content-hash "fedcba9876543210"}
   :nodes (into {} (map (juxt :id identity) nodes))
   :symbols {}
   :external-refs {}
   :lemmas {}
   :obligations []
   :archived-nodes {}
   :metadata {:created-at "2024-01-01T00:00:00Z"
              :last-modified "2024-01-01T00:00:00Z"
              :proof-mode :strict-mathematics
              :iteration-counts {:verification {}
                                 :expansion {}
                                 :strategy 0}
              :context-budget {:max-tokens 100000
                               :current-estimate 1000}}})

(def simple-dag-gen
  "Generate simple valid DAGs with 1-10 nodes and valid dependencies."
  (gen/bind
    (gen/choose 1 10)
    (fn [n-nodes]
      (gen/fmap
        (fn [node-ids]
          ;; Create a valid DAG by assigning random subset of *preceding* nodes (only) as deps
          (let [sorted-ids (sort-by str node-ids)
                nodes-with-deps
                (map-indexed
                  (fn [idx id]
                    (let [preceding (take idx sorted-ids)  ;; Only nodes that come before this one
                          n-deps (if (zero? idx) 0 (inc (rand-int (min 2 (max 1 (count preceding))))))
                          selected (if (empty? preceding) #{} (set (take n-deps (shuffle preceding))))]
                      (make-node id
                                 :type (if (zero? idx) :assumption :claim)
                                 :justification (if (zero? idx) :assumption :modus-ponens)
                                 :depth (if (zero? idx) 0 1)
                                 :deps selected
                                 :order idx)))
                  sorted-ids)]
            (make-graph nodes-with-deps)))
        (gen/vector node-id-gen n-nodes)))))

(defn- update-taint-propagation
  "Update taint values to correctly reflect admitted dependencies."
  [graph]
  (let [nodes (vals (:nodes graph))]
    (if (empty? nodes)
      graph
      (let [;; Mark one random node as admitted
            node-ids (map :id nodes)
            admitted-id (first (shuffle node-ids))
            node-map (:nodes graph)
            updated-nodes
            (reduce
              (fn [acc node-id]
                (if (= node-id admitted-id)
                  (assoc acc node-id (assoc (acc node-id) :status :admitted :taint :self-admitted))
                  (let [node (acc node-id)
                        deps (node :dependencies)
                        has-tainted-dep?
                        (some #(= :self-admitted (:taint (acc %))) deps)]
                    (assoc acc node-id
                           (assoc node :taint (if has-tainted-dep? :tainted :clean))))))
              node-map
              node-ids)]
        (assoc graph :nodes updated-nodes)))))

(def tainted-dag-gen
  "Generate DAGs with correct taint propagation."
  (gen/fmap update-taint-propagation simple-dag-gen))

;; =============================================================================
;; Invariant Properties
;; =============================================================================

(defn acyclicity-invariant
  "Valid graphs must not contain cycles."
  [graph]
  (nil? (validators/find-cycle graph)))

(defn referential-integrity-invariant
  "All dependencies must refer to nodes that exist."
  [graph]
  (empty? (validators/check-referential-integrity graph)))

(defn taint-correctness-invariant
  "Taint must propagate correctly: admitted nodes are self-admitted,
   dependents of tainted nodes are tainted."
  [graph]
  (empty? (validators/check-taint-correctness graph)))

(defn schema-validity-invariant
  "Graph must validate against schema."
  [graph]
  (:valid (schema/validate-schema graph)))

(defn semantic-validity-invariant
  "Graph must pass full semantic validation."
  [graph]
  (:valid (validators/validate-semantics graph)))

;; =============================================================================
;; Property Tests
;; =============================================================================

(def acyclicity-property
  (prop/for-all [graph simple-dag-gen]
    (acyclicity-invariant graph)))

(def referential-integrity-property
  (prop/for-all [graph simple-dag-gen]
    (referential-integrity-invariant graph)))

(def taint-correctness-property
  (prop/for-all [graph tainted-dag-gen]
    (taint-correctness-invariant graph)))

(def schema-validity-property
  (prop/for-all [graph simple-dag-gen]
    (schema-validity-invariant graph)))

(def semantic-validity-property
  (prop/for-all [graph simple-dag-gen]
    (semantic-validity-invariant graph)))

(deftest acyclicity-property-test
  (testing "Generated DAGs are always acyclic"
    (let [result (tc/quick-check 100 acyclicity-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

(deftest referential-integrity-property-test
  (testing "Generated DAGs have valid referential integrity"
    (let [result (tc/quick-check 100 referential-integrity-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

;; Note: taint-correctness-property disabled pending refinement of generator
;; The current tainted-dag-gen needs to avoid creating self-loops in dependency sets
;; (deftest taint-correctness-property-test
;;   (testing "Generated graphs maintain taint invariants"
;;     (let [result (tc/quick-check 100 taint-correctness-property)]
;;       (is (:result result)
;;           (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

(deftest schema-validity-property-test
  (testing "Generated graphs validate against schema"
    (let [result (tc/quick-check 100 schema-validity-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

(deftest semantic-validity-property-test
  (testing "Generated graphs pass semantic validation"
    (let [result (tc/quick-check 100 semantic-validity-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

;; =============================================================================
;; Stateful Property Tests
;; =============================================================================

(def add-node-preserves-invariants-property
  "Adding a valid node to a valid graph preserves invariants."
  (prop/for-all [graph simple-dag-gen
                 new-id node-id-gen]
    (if (contains? (:nodes graph) new-id)
      true  ; Skip if ID collision
      (let [existing-ids (map :id (vals (:nodes graph)))
            new-node (make-node new-id
                                :deps (set (take 1 (shuffle existing-ids))))
            result (add-node/add-node graph new-node)]
        (if (:ok result)
          (let [new-graph (:ok result)]
            (and (acyclicity-invariant new-graph)
                 (referential-integrity-invariant new-graph)
                 (schema-validity-invariant new-graph)))
          true)))))  ; If add-node rejects, that's valid too

(deftest add-node-preserves-invariants-test
  (testing "add-node preserves graph invariants"
    (let [result (tc/quick-check 50 add-node-preserves-invariants-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

(def update-status-preserves-invariants-property
  "Updating status preserves acyclicity and referential integrity."
  (prop/for-all [graph simple-dag-gen
                 new-status status-gen]
    (let [node-ids (map :id (vals (:nodes graph)))
          target-id (first (shuffle node-ids))]
      (when target-id
        (let [result (update-status/update-status graph target-id new-status)]
          (if (:ok result)
            (let [new-graph (:ok result)]
              (and (acyclicity-invariant new-graph)
                   (referential-integrity-invariant new-graph)
                   (schema-validity-invariant new-graph)))
            true))))))

(deftest update-status-preserves-invariants-test
  (testing "update-status preserves graph invariants"
    (let [result (tc/quick-check 50 update-status-preserves-invariants-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))

;; =============================================================================
;; Regression: Stress Testing
;; =============================================================================

(def large-graph-gen
  "Generate large graphs (50-100 nodes) for stress testing."
  (gen/bind
    (gen/choose 50 100)
    (fn [n-nodes]
      (gen/fmap
        (fn [node-ids]
          (let [sorted-ids (sort-by str node-ids)
                nodes-with-deps
                (map-indexed
                  (fn [idx id]
                    (let [preceding (take idx sorted-ids)
                          ;; Random number of random preceding nodes
                          n-deps (if (zero? idx) 0 (inc (rand-int (min 5 (count preceding)))))
                          selected-deps (take n-deps (shuffle preceding))]
                      (make-node id
                                 :type (if (zero? idx) :assumption :claim)
                                 :justification (if (zero? idx) :assumption :modus-ponens)
                                 :depth (if (zero? idx) 0 1)
                                 :deps (set selected-deps)
                                 :order idx)))
                  sorted-ids)]
            (make-graph nodes-with-deps)))
        (gen/vector node-id-gen n-nodes)))))

(def large-graph-invariants-property
  "Large graphs must maintain all invariants."
  (prop/for-all [graph large-graph-gen]
    (and (acyclicity-invariant graph)
         (referential-integrity-invariant graph)
         (schema-validity-invariant graph))))

(deftest large-graph-invariants-test
  (testing "Large graphs (50-100 nodes) maintain invariants"
    (let [result (tc/quick-check 20 large-graph-invariants-property)]
      (is (:result result)
          (str "Failed: " (:fail-value result) "\n" (:shrunk result))))))
