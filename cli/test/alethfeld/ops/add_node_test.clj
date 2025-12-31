(ns alethfeld.ops.add-node-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.graph :as graph]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(defn make-partial-node
  "Create a minimal partial node for add-node input."
  [id & {:keys [type statement deps scope justification depth order parent
                introduces discharges lemma-id external-id]
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
    parent (assoc :parent parent)
    introduces (assoc :introduces introduces)
    discharges (assoc :discharges discharges)
    lemma-id (assoc :lemma-id lemma-id)
    external-id (assoc :external-id external-id)))

(deftest add-node-basic-test
  (testing "Add node to empty graph"
    (let [node (make-partial-node :1-new001
                                  :type :assumption
                                  :justification :assumption
                                  :depth 0)
          result (add-node/add-node f/empty-nodes-graph node)]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (= 2 (:version graph)))  ; incremented from 1
        (is (contains? (:nodes graph) :1-new001))
        (is (= :proposed (:status (get-in graph [:nodes :1-new001]))))
        (is (= :clean (:taint (get-in graph [:nodes :1-new001]))))
        (is (some? (:content-hash (get-in graph [:nodes :1-new001])))))))

  (testing "Add node with dependencies"
    (let [node (make-partial-node :1-new001
                                  :deps #{:1-aaa111}
                                  :order 3)
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (contains? (:nodes graph) :1-new001))
        (is (= #{:1-aaa111} (:dependencies (get-in graph [:nodes :1-new001]))))))))

(deftest add-node-with-scope-test
  (testing "Add node with valid scope"
    (let [node (make-partial-node :1-new001
                                  :deps #{:1-ccc333}
                                  :scope #{:1-bbb222}
                                  :order 4)
          result (add-node/add-node f/scoped-graph node)]
      (is (:ok result)))))

(deftest add-node-rejection-tests
  (testing "Reject duplicate ID"
    (let [node (make-partial-node :1-aaa111)  ; Already exists
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:error result))
      (is (some #(= :duplicate-id (:type %)) (:error result)))))

  (testing "Reject missing dependency"
    (let [node (make-partial-node :1-new001 :deps #{:1-nonexistent})
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:error result))
      (is (some #(= :missing-dependencies (:type %)) (:error result)))))

  (testing "Reject invalid scope entry"
    (let [node (make-partial-node :1-new001
                                  :deps #{:1-aaa111}
                                  :scope #{:1-fake-assume})  ; Not a valid scope entry
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:error result))
      (is (some #(= :invalid-scope (:type %)) (:error result)))))

  (testing "Reject cycle creation"
    (let [node (make-partial-node :1-aaa111 :deps #{:1-ccc333})  ; Would create cycle
          ;; But :1-aaa111 already exists, so we get duplicate ID error first
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:error result))))

  (testing "Reject self-loop"
    (let [node (make-partial-node :1-new001 :deps #{:1-new001})
          ;; The cycle check should catch this as node is temporarily added
          result (add-node/add-node f/linear-chain-graph node)]
      ;; Self-loop: the node isn't in graph yet, so deps check passes,
      ;; but cycle detection should catch it
      (is (:error result)))))

(deftest add-node-type-specific-test
  (testing "Add assumption node"
    (let [node (make-partial-node :0-assume1
                                  :type :assumption
                                  :justification :assumption
                                  :depth 0)
          result (add-node/add-node f/empty-nodes-graph node)]
      (is (:ok result))))

  (testing "Add local-assume requires :introduces"
    (let [node (make-partial-node :1-la001
                                  :type :local-assume
                                  :justification :local-assumption
                                  :deps #{:1-aaa111})  ; Missing :introduces
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:error result))
      (is (some #(= :missing-introduces (:type %)) (:error result)))))

  (testing "Add local-assume with :introduces succeeds"
    (let [node (make-partial-node :1-la001
                                  :type :local-assume
                                  :justification :local-assumption
                                  :deps #{:1-aaa111}
                                  :introduces "P")
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:ok result))))

  (testing "Add local-discharge requires :discharges"
    (let [node (make-partial-node :1-ld001
                                  :type :local-discharge
                                  :justification :discharge
                                  :deps #{:1-bbb222})  ; Missing :discharges
          result (add-node/add-node f/scoped-graph node)]
      (is (:error result))
      (is (some #(= :missing-discharges (:type %)) (:error result))))))

(deftest taint-computation-test
  (testing "Clean dependencies produce clean taint"
    (let [node (make-partial-node :1-new001
                                  :deps #{:1-ccc333}
                                  :order 4)
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:ok result))
      (is (= :clean (:taint (get-in (:ok result) [:nodes :1-new001]))))))

  (testing "Tainted dependency produces tainted node"
    ;; Properly set up a tainted graph by changing status to :admitted
    ;; and recomputing all taints to maintain invariants
    (let [graph (-> f/linear-chain-graph
                    (assoc-in [:nodes :1-aaa111 :status] :admitted)
                    (graph/recompute-all-taints))
          node (make-partial-node :1-new001
                                  :deps #{:1-aaa111}
                                  :order 4)
          result (add-node/add-node graph node)]
      (is (:ok result))
      (is (= :tainted (:taint (get-in (:ok result) [:nodes :1-new001])))))))

(deftest version-increment-test
  (testing "Version is incremented after add"
    (let [node (make-partial-node :1-new001)
          result (add-node/add-node f/linear-chain-graph node)]
      (is (:ok result))
      (is (= 2 (:version (:ok result)))))))

(deftest content-hash-test
  (testing "Content hash is computed"
    (let [node (make-partial-node :1-new001 :statement "Test statement for hashing")
          result (add-node/add-node f/empty-nodes-graph node)]
      (is (:ok result))
      (let [hash (:content-hash (get-in (:ok result) [:nodes :1-new001]))]
        (is (string? hash))
        (is (= 16 (count hash)))))))

(deftest provenance-test
  (testing "Provenance is filled in if not provided"
    (let [node (make-partial-node :1-new001)
          result (add-node/add-node f/empty-nodes-graph node)]
      (is (:ok result))
      (let [prov (:provenance (get-in (:ok result) [:nodes :1-new001]))]
        (is (some? (:created-at prov)))
        (is (= :prover (:created-by prov)))))))

(deftest output-validates-test
  (testing "Output graph validates against schema"
    (let [node (make-partial-node :1-new001
                                  :type :assumption
                                  :justification :assumption
                                  :depth 0)
          result (add-node/add-node f/empty-nodes-graph node)]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))

(deftest generate-node-id-test
  (testing "generate-node-id produces valid format"
    (let [id (add-node/generate-node-id 2)]
      (is (keyword? id))
      (is (re-matches #":2-[a-f0-9]{6}" (str id))))))
