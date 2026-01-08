(ns alethfeld.fixtures
  "Test fixtures for semantic proof graph validation tests.

   This is the authoritative source for test helper functions.
   All test files should require this namespace for make-node, make-graph, etc.")

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn make-node
  "Create a complete node with all fields filled in.
   Use this for creating test graphs directly (not via add-node).

   Options:
   - :type - Node type (default :claim)
   - :statement - Statement text (default \"Test statement\")
   - :deps - Set of dependency IDs (default #{})
   - :scope - Set of in-scope assumption IDs (default #{})
   - :justification - Justification type (default :modus-ponens)
   - :status - Node status (default :verified)
   - :taint - Taint value (default :clean)
   - :depth - Lamport depth (default 1)
   - :parent - Parent node ID (default nil)
   - :order - Display order (default 0)
   - :content-hash - Content hash (default fixed, or :dynamic for hash of [id statement])
   - :introduces - For local-assume nodes
   - :discharges - For local-discharge nodes
   - :lemma-id - For lemma-ref nodes
   - :external-id - For external-ref nodes
   - :assumption-label - Label for assumptions"
  [id & {:keys [type statement deps scope justification status taint depth parent order
                content-hash introduces discharges lemma-id external-id assumption-label]
         :or {type :claim
              statement "Test statement"
              deps #{}
              scope #{}
              justification :modus-ponens
              status :verified
              taint :clean
              depth 1
              parent nil
              order 0
              content-hash nil}}]
  (let [hash-value (case content-hash
                     :dynamic (format "%016x" (hash [id statement]))
                     nil "0123456789abcdef"
                     content-hash)]
    (cond-> {:id id
             :type type
             :statement statement
             :content-hash hash-value
             :dependencies deps
             :scope scope
             :justification justification
             :status status
             :taint taint
             :depth depth
             :parent parent
             :display-order order
             :provenance {:created-at "2024-01-01T00:00:00Z"
                          :created-by :prover
                          :round 1
                          :revision-of nil}}
      introduces (assoc :introduces introduces)
      discharges (assoc :discharges discharges)
      lemma-id (assoc :lemma-id lemma-id)
      external-id (assoc :external-id external-id)
      assumption-label (assoc :assumption-label assumption-label))))

(defn make-partial-node
  "Create a partial node for use with add-node/add-node.
   Does not include status, taint, content-hash, or provenance
   (those are filled in by the add-node operation).

   Options:
   - :type - Node type (default :claim)
   - :statement - Statement text (default \"Test statement\")
   - :deps - Set of dependency IDs (default #{})
   - :scope - Set of in-scope assumption IDs (default #{})
   - :justification - Justification type (default :modus-ponens)
   - :depth - Lamport depth (default 1)
   - :order - Display order (default 0)
   - :introduces - For local-assume nodes
   - :discharges - For local-discharge nodes
   - :external-id - For external-ref nodes"
  [id & {:keys [type statement deps scope justification depth order
                introduces discharges external-id]
         :or {type :claim
              statement "Test statement"
              deps #{}
              scope #{}
              justification :modus-ponens
              depth 1
              order 0}}]
  (cond-> {:id id
           :type type
           :statement statement
           :dependencies deps
           :scope scope
           :justification justification
           :depth depth
           :display-order order}
    introduces (assoc :introduces introduces)
    discharges (assoc :discharges discharges)
    external-id (assoc :external-id external-id)))

(defn make-graph
  "Create a minimal valid graph with given nodes."
  [nodes & {:keys [symbols external-refs lemmas archived-nodes]
            :or {symbols {}
                 external-refs {}
                 lemmas {}
                 archived-nodes {}}}]
  {:graph-id "test-graph-001"
   :version 1
   :theorem {:id :theorem
             :statement "Test theorem"
             :content-hash "fedcba9876543210"}
   :nodes (into {} (map (juxt :id identity) nodes))
   :symbols symbols
   :external-refs external-refs
   :lemmas lemmas
   :obligations []
   :archived-nodes archived-nodes
   :metadata {:created-at "2024-01-01T00:00:00Z"
              :last-modified "2024-01-01T00:00:00Z"
              :proof-mode :strict-mathematics
              :iteration-counts {:verification {}
                                 :expansion {}
                                 :strategy 0}
              :context-budget {:max-tokens 100000
                               :current-estimate 1000}}})

;; =============================================================================
;; Valid Graph Fixtures
;; =============================================================================

(def minimal-valid-graph
  "Minimal valid graph with just an assumption node."
  (make-graph [(make-node :1-abc123
                          :type :assumption
                          :justification :assumption
                          :depth 0)]))

(def linear-chain-graph
  "Valid graph with linear dependency chain A -> B -> C."
  (make-graph [(make-node :1-aaa111
                          :type :assumption
                          :justification :assumption
                          :depth 0)
               (make-node :1-bbb222
                          :deps #{:1-aaa111}
                          :order 1)
               (make-node :1-ccc333
                          :deps #{:1-bbb222}
                          :order 2)]))

(def diamond-graph
  "Valid diamond pattern: A -> B,C -> D."
  (make-graph [(make-node :1-aaa111
                          :type :assumption
                          :justification :assumption
                          :depth 0)
               (make-node :1-bbb222
                          :deps #{:1-aaa111}
                          :order 1)
               (make-node :1-ccc333
                          :deps #{:1-aaa111}
                          :order 2)
               (make-node :1-ddd444
                          :deps #{:1-bbb222 :1-ccc333}
                          :order 3)]))

(def scoped-graph
  "Graph with local-assume and local-discharge."
  (make-graph [(make-node :1-aaa111
                          :type :assumption
                          :justification :assumption
                          :depth 0)
               (make-node :1-bbb222
                          :type :local-assume
                          :justification :local-assumption
                          :introduces "P"
                          :deps #{:1-aaa111}
                          :order 1)
               (make-node :1-ccc333
                          :deps #{:1-bbb222}
                          :scope #{:1-bbb222}
                          :order 2)
               (make-node :1-ddd444
                          :type :local-discharge
                          :justification :discharge
                          :discharges :1-bbb222
                          :deps #{:1-ccc333}
                          :scope #{:1-bbb222}
                          :order 3)]))

(def empty-nodes-graph
  "Graph with empty :nodes map."
  (make-graph []))

;; =============================================================================
;; Invalid Graph Fixtures - Schema Violations
;; =============================================================================

(def invalid-node-type-graph
  "Graph with invalid node type."
  (make-graph [(assoc (make-node :1-bad001) :type :invalid-type)]))

(def invalid-status-graph
  "Graph with invalid status."
  (make-graph [(assoc (make-node :1-bad001) :status :unknown-status)]))

;; =============================================================================
;; Invalid Graph Fixtures - Referential Integrity
;; =============================================================================

(def missing-dependency-graph
  "Graph where node references non-existent dependency."
  (make-graph [(make-node :1-aaa111
                          :deps #{:1-nonexistent})]))

;; =============================================================================
;; Invalid Graph Fixtures - Cycles
;; =============================================================================

(def self-loop-graph
  "Graph with self-referential dependency."
  (make-graph [(make-node :1-aaa111
                          :deps #{:1-aaa111})]))

(def direct-cycle-graph
  "Graph with direct A->B->A cycle."
  (make-graph [(make-node :1-aaa111
                          :deps #{:1-bbb222})
               (make-node :1-bbb222
                          :deps #{:1-aaa111})]))

;; =============================================================================
;; Invalid Graph Fixtures - Taint Violations
;; =============================================================================

(def incorrect-taint-admitted-graph
  "Graph where admitted node has wrong taint."
  (make-graph [(make-node :1-aaa111
                          :status :admitted
                          :taint :clean)]))  ; should be :self-admitted

(def incorrect-taint-chain-graph
  "Graph where taint doesn't propagate correctly."
  (make-graph [(make-node :1-aaa111
                          :status :admitted
                          :taint :self-admitted)
               (make-node :1-bbb222
                          :deps #{:1-aaa111}
                          :taint :clean)]))  ; should be :tainted
