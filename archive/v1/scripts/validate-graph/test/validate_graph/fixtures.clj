(ns validate-graph.fixtures
  "Test fixtures for semantic proof graph validation tests.")

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn make-node
  "Create a node with defaults filled in."
  [id & {:keys [type statement deps scope justification status taint depth parent order
                introduces discharges lemma-id external-id assumption-label]
         :or {type :claim
              statement "Test statement"
              deps #{}
              scope #{}
              justification :modus-ponens
              status :verified
              taint :clean
              depth 1
              parent nil
              order 0}}]
  (cond-> {:id id
           :type type
           :statement statement
           :content-hash "0123456789abcdef"
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
    assumption-label (assoc :assumption-label assumption-label)))

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

(def all-node-types-graph
  "Graph with all node types represented."
  (make-graph [(make-node :0-assume1
                          :type :assumption
                          :justification :assumption
                          :depth 0
                          :assumption-label :A1)
               (make-node :1-def001
                          :type :definition
                          :justification :definition-expansion
                          :deps #{:0-assume1})
               (make-node :1-claim1
                          :type :claim
                          :deps #{:1-def001}
                          :order 1)
               (make-node :1-locass
                          :type :local-assume
                          :justification :local-assumption
                          :introduces "Q"
                          :deps #{:1-claim1}
                          :order 2)
               (make-node :2-inner1
                          :type :claim
                          :deps #{:1-locass}
                          :scope #{:1-locass}
                          :depth 2
                          :parent :1-locass)
               (make-node :1-disch1
                          :type :local-discharge
                          :justification :discharge
                          :discharges :1-locass
                          :deps #{:2-inner1}
                          :scope #{:1-locass}
                          :order 3)
               (make-node :1-qed001
                          :type :qed
                          :justification :qed
                          :deps #{:1-disch1}
                          :order 4)]
              :external-refs {"ext-001" {:id "ext-001"
                                         :doi "10.1234/test"
                                         :claimed-statement "External claim"
                                         :verification-status :verified}}
              :lemmas {"lem-001" {:id "lem-001"
                                  :name "Test Lemma"
                                  :statement "Lemma statement"
                                  :content-hash "1234567890abcdef"
                                  :root-node :archived-root
                                  :status :proven
                                  :taint :clean
                                  :extracted-nodes #{:archived-root}
                                  :proof-graph-id nil}}
              :archived-nodes {:archived-root (make-node :archived-root)}))

(def all-justifications-graph
  "Graph demonstrating various justification types."
  (make-graph [(make-node :1-j01 :justification :assumption :type :assumption :depth 0)
               (make-node :1-j02 :justification :substitution :deps #{:1-j01})
               (make-node :1-j03 :justification :modus-ponens :deps #{:1-j02})
               (make-node :1-j04 :justification :universal-elim :deps #{:1-j03})
               (make-node :1-j05 :justification :universal-intro :deps #{:1-j04})
               (make-node :1-j06 :justification :existential-intro :deps #{:1-j05})
               (make-node :1-j07 :justification :equality-rewrite :deps #{:1-j06})
               (make-node :1-j08 :justification :algebraic-rewrite :deps #{:1-j07})
               (make-node :1-j09 :justification :conjunction-intro :deps #{:1-j08})
               (make-node :1-j10 :justification :conjunction-elim :deps #{:1-j09})
               (make-node :1-j11 :justification :disjunction-intro :deps #{:1-j10})
               (make-node :1-j12 :justification :implication-intro :deps #{:1-j11})
               (make-node :1-j13 :justification :case-split :deps #{:1-j12})
               (make-node :1-j14 :justification :induction-base :deps #{:1-j13})
               (make-node :1-j15 :justification :induction-step :deps #{:1-j14})
               (make-node :1-j16 :justification :contradiction :deps #{:1-j15})]))

;; =============================================================================
;; Invalid Graph Fixtures - Schema Violations
;; =============================================================================

(def invalid-node-type-graph
  "Graph with invalid node type."
  (make-graph [(assoc (make-node :1-bad001) :type :invalid-type)]))

(def invalid-justification-graph
  "Graph with invalid justification."
  (make-graph [(assoc (make-node :1-bad001) :justification :not-a-justification)]))

(def invalid-status-graph
  "Graph with invalid status."
  (make-graph [(assoc (make-node :1-bad001) :status :unknown-status)]))

(def invalid-taint-graph
  "Graph with invalid taint value."
  (make-graph [(assoc (make-node :1-bad001) :taint :maybe-tainted)]))

(def missing-statement-graph
  "Graph with node missing required :statement field."
  (make-graph [(dissoc (make-node :1-bad001) :statement)]))

(def missing-id-graph
  "Graph with node missing required :id field."
  (make-graph [(dissoc (make-node :1-bad001) :id)]))

(def wrong-deps-type-graph
  "Graph with :dependencies as vector instead of set."
  (make-graph [(assoc (make-node :1-bad001) :dependencies [:1-other])]))

(def negative-depth-graph
  "Graph with negative depth."
  (make-graph [(assoc (make-node :1-bad001) :depth -1)]))

(def invalid-content-hash-graph
  "Graph with invalid content hash format."
  (make-graph [(assoc (make-node :1-bad001) :content-hash "not-a-valid-hash")]))

(def invalid-proof-mode-graph
  "Graph with invalid proof mode."
  (assoc-in (make-graph [(make-node :1-ok001)])
            [:metadata :proof-mode] :invalid-mode))

;; =============================================================================
;; Invalid Graph Fixtures - Referential Integrity
;; =============================================================================

(def missing-dependency-graph
  "Graph where node references non-existent dependency."
  (make-graph [(make-node :1-aaa111
                          :deps #{:1-nonexistent})]))

(def missing-parent-graph
  "Graph where node references non-existent parent."
  (make-graph [(make-node :1-aaa111
                          :parent :1-nonexistent)]))

(def missing-lemma-ref-graph
  "Graph with lemma-ref to non-existent lemma."
  (make-graph [(make-node :1-aaa111
                          :type :lemma-ref
                          :justification :lemma-application
                          :lemma-id "nonexistent-lemma")]))

(def missing-external-ref-graph
  "Graph with external-ref to non-existent external."
  (make-graph [(make-node :1-aaa111
                          :type :external-ref
                          :justification :external-application
                          :external-id "nonexistent-external")]))

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

(def triangle-cycle-graph
  "Graph with A->B->C->A cycle."
  (make-graph [(make-node :1-aaa111
                          :deps #{:1-ccc333})
               (make-node :1-bbb222
                          :deps #{:1-aaa111})
               (make-node :1-ccc333
                          :deps #{:1-bbb222})]))

(def long-cycle-graph
  "Graph with 5-node cycle."
  (make-graph [(make-node :1-n1 :deps #{:1-n5})
               (make-node :1-n2 :deps #{:1-n1})
               (make-node :1-n3 :deps #{:1-n2})
               (make-node :1-n4 :deps #{:1-n3})
               (make-node :1-n5 :deps #{:1-n4})]))

;; =============================================================================
;; Invalid Graph Fixtures - Scope Violations
;; =============================================================================

(def invalid-scope-non-ancestor-graph
  "Graph where scope contains non-ancestor local-assume."
  (make-graph [(make-node :1-aaa111
                          :type :local-assume
                          :justification :local-assumption
                          :introduces "P")
               (make-node :1-bbb222
                          :scope #{:1-aaa111}  ; :1-aaa111 is not an ancestor
                          )]))

(def invalid-scope-discharged-graph
  "Graph where scope contains already-discharged assumption."
  (make-graph [(make-node :1-aaa111
                          :type :assumption
                          :justification :assumption
                          :depth 0)
               (make-node :1-bbb222
                          :type :local-assume
                          :justification :local-assumption
                          :introduces "P"
                          :deps #{:1-aaa111})
               (make-node :1-ccc333
                          :type :local-discharge
                          :justification :discharge
                          :discharges :1-bbb222
                          :deps #{:1-bbb222}
                          :scope #{:1-bbb222})
               (make-node :1-ddd444
                          :deps #{:1-ccc333}
                          :scope #{:1-bbb222})]))  ; :1-bbb222 was discharged

(def invalid-discharge-not-ancestor-graph
  "Graph where discharge targets non-ancestor."
  (make-graph [(make-node :1-aaa111
                          :type :local-assume
                          :justification :local-assumption
                          :introduces "P")
               (make-node :1-bbb222
                          :type :local-discharge
                          :justification :discharge
                          :discharges :1-aaa111)]))  ; :1-aaa111 is not ancestor

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

(def incorrect-taint-rejected-graph
  "Graph where rejected node has wrong taint."
  (make-graph [(make-node :1-aaa111
                          :status :rejected
                          :taint :clean)]))  ; should be :tainted

;; =============================================================================
;; Edge Case Fixtures
;; =============================================================================

(def empty-nodes-graph
  "Graph with empty :nodes map."
  (make-graph []))

(def deeply-nested-graph
  "Graph with deep nesting (10 levels)."
  (make-graph
   (for [i (range 10)]
     (make-node (keyword (str "1-depth" i))
                :depth i
                :deps (if (zero? i) #{} #{(keyword (str "1-depth" (dec i)))})
                :parent (when (pos? i) (keyword (str "1-depth" (dec i))))
                :type (if (zero? i) :assumption :claim)
                :justification (if (zero? i) :assumption :modus-ponens)))))

(def wide-graph
  "Graph with many siblings at same level."
  (make-graph
   (cons (make-node :1-root
                    :type :assumption
                    :justification :assumption
                    :depth 0)
         (for [i (range 20)]
           (make-node (keyword (str "1-sibling" i))
                      :deps #{:1-root}
                      :order i)))))

(def unicode-statement-graph
  "Graph with Unicode in statements."
  (make-graph [(make-node :1-unicode
                          :statement "Let \\alpha \\in \\mathbb{R} and \\forall x \\in X: \\|x\\| \\leq \\epsilon")]))

(def long-statement-graph
  "Graph with very long statement."
  (make-graph [(make-node :1-long
                          :statement (apply str (repeat 1000 "This is a very long statement. ")))]))
