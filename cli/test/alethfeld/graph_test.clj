(ns alethfeld.graph-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.graph :as g]
            [alethfeld.validators :as v]  ; For check-scope-validity test
            [alethfeld.fixtures :as f]))

(deftest node-queries-test
  (testing "node-ids returns all IDs"
    (is (= #{:1-abc123} (g/node-ids f/minimal-valid-graph)))
    (is (= #{:1-aaa111 :1-bbb222 :1-ccc333} (g/node-ids f/linear-chain-graph))))

  (testing "get-node returns node or nil"
    (is (= :assumption (:type (g/get-node f/minimal-valid-graph :1-abc123))))
    (is (nil? (g/get-node f/minimal-valid-graph :nonexistent))))

  (testing "nodes-of-type filters correctly"
    (let [claims (g/nodes-of-type f/linear-chain-graph :claim)]
      (is (= 2 (count claims)))
      (is (every? #(= :claim (:type %)) (vals claims))))))

(deftest ancestor-descendant-test
  (testing "get-ancestors in linear chain"
    (is (empty? (g/get-ancestors f/linear-chain-graph :1-aaa111)))
    (is (= #{:1-aaa111} (g/get-ancestors f/linear-chain-graph :1-bbb222)))
    (is (= #{:1-aaa111 :1-bbb222} (g/get-ancestors f/linear-chain-graph :1-ccc333))))

  (testing "get-ancestors in diamond"
    (is (= #{:1-aaa111 :1-bbb222 :1-ccc333}
           (g/get-ancestors f/diamond-graph :1-ddd444))))

  (testing "get-descendants in linear chain"
    (is (= #{:1-bbb222 :1-ccc333} (g/get-descendants f/linear-chain-graph :1-aaa111)))
    (is (= #{:1-ccc333} (g/get-descendants f/linear-chain-graph :1-bbb222)))
    (is (empty? (g/get-descendants f/linear-chain-graph :1-ccc333))))

  (testing "get-direct-dependents"
    (is (= #{:1-bbb222} (g/get-direct-dependents f/linear-chain-graph :1-aaa111)))
    (is (= #{:1-bbb222 :1-ccc333} (g/get-direct-dependents f/diamond-graph :1-aaa111)))))

(deftest get-ancestors-usage-in-validators-test
  (testing "get-ancestors is used correctly by validators"
    ;; Verify that compute-valid-scope still works correctly
    (let [scope (g/compute-valid-scope f/scoped-graph :1-ccc333)]
      (is (contains? scope :1-bbb222)))
    ;; Verify validators still work correctly after dedup
    (let [result (v/check-scope-validity f/scoped-graph)]
      ;; Result should be a sequence of errors (empty if valid)
      (is (vector? result))
      ;; For our fixture, scope validation should pass
      (is (empty? result)))))

(deftest topological-sort-test
  (testing "Linear chain sorted correctly"
    (let [sorted (g/topological-sort f/linear-chain-graph)]
      (is (= [:1-aaa111 :1-bbb222 :1-ccc333] sorted))))

  (testing "Diamond sorted correctly (deps before dependents)"
    (let [sorted (g/topological-sort f/diamond-graph)]
      (is (< (.indexOf sorted :1-aaa111)
             (.indexOf sorted :1-bbb222)))
      (is (< (.indexOf sorted :1-aaa111)
             (.indexOf sorted :1-ccc333)))
      (is (< (.indexOf sorted :1-bbb222)
             (.indexOf sorted :1-ddd444)))
      (is (< (.indexOf sorted :1-ccc333)
             (.indexOf sorted :1-ddd444))))))

(deftest topological-sort-partial-test
  (testing "Partial sort for single target in linear chain"
    ;; Target :1-bbb222 should include itself and ancestor :1-aaa111
    (let [sorted (g/topological-sort f/linear-chain-graph nil :targets #{:1-bbb222})]
      (is (= 2 (count sorted)))
      (is (= [:1-aaa111 :1-bbb222] sorted))))

  (testing "Partial sort for leaf in linear chain"
    ;; Target :1-ccc333 should include all ancestors
    (let [sorted (g/topological-sort f/linear-chain-graph nil :targets #{:1-ccc333})]
      (is (= [:1-aaa111 :1-bbb222 :1-ccc333] sorted))))

  (testing "Partial sort for root node returns just root"
    (let [sorted (g/topological-sort f/linear-chain-graph nil :targets #{:1-aaa111})]
      (is (= [:1-aaa111] sorted))))

  (testing "Partial sort for diamond target"
    ;; Target :1-ddd444 needs all four nodes
    (let [sorted (g/topological-sort f/diamond-graph nil :targets #{:1-ddd444})]
      (is (= 4 (count sorted)))
      ;; Verify order constraints
      (is (< (.indexOf sorted :1-aaa111)
             (.indexOf sorted :1-ddd444)))
      (is (< (.indexOf sorted :1-bbb222)
             (.indexOf sorted :1-ddd444)))
      (is (< (.indexOf sorted :1-ccc333)
             (.indexOf sorted :1-ddd444)))))

  (testing "Partial sort for middle diamond nodes"
    ;; Target :1-bbb222 and :1-ccc333 - both depend on :1-aaa111
    (let [sorted (g/topological-sort f/diamond-graph nil :targets #{:1-bbb222 :1-ccc333})]
      (is (= 3 (count sorted)))
      (is (some #{:1-aaa111} sorted))
      (is (some #{:1-bbb222} sorted))
      (is (some #{:1-ccc333} sorted))
      ;; :1-ddd444 should NOT be included
      (is (not (some #{:1-ddd444} sorted)))))

  (testing "Partial sort with empty targets returns nil"
    (is (nil? (g/topological-sort f/linear-chain-graph nil :targets #{}))))

  (testing "Partial sort matches full sort when all nodes targeted"
    (let [full-sorted (g/topological-sort f/diamond-graph)
          partial-sorted (g/topological-sort f/diamond-graph nil
                                              :targets #{:1-aaa111 :1-bbb222 :1-ccc333 :1-ddd444})]
      ;; Same nodes, same order constraints (though order may differ for parallel nodes)
      (is (= (set full-sorted) (set partial-sorted)))
      (is (= (count full-sorted) (count partial-sorted))))))

(deftest scope-queries-test
  (testing "compute-valid-scope for node in scope"
    (let [scope (g/compute-valid-scope f/scoped-graph :1-ccc333)]
      (is (contains? scope :1-bbb222))))

  (testing "compute-valid-scope after discharge"
    (let [graph f/scoped-graph
          ;; Add a node after discharge
          after-discharge (assoc-in graph [:nodes :1-eee555]
                                    (f/make-node :1-eee555 :deps #{:1-ddd444} :order 4))]
      (let [scope (g/compute-valid-scope after-discharge :1-eee555)]
        (is (empty? scope)))))

  (testing "active-assumptions includes globals"
    (let [assumptions (g/active-assumptions f/linear-chain-graph :1-ccc333)]
      (is (contains? assumptions :1-aaa111)))))

(deftest taint-queries-test
   (testing "compute-taint for clean node"
     (is (= :clean (g/compute-taint f/minimal-valid-graph :1-abc123))))

   (testing "compute-taint for admitted node"
     (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :admitted)]
       (is (= :self-admitted (g/compute-taint graph :1-abc123)))))

   (testing "compute-taint propagation"
     (let [graph (-> f/linear-chain-graph
                     (assoc-in [:nodes :1-aaa111 :status] :admitted)
                     (assoc-in [:nodes :1-aaa111 :taint] :self-admitted))]
       (is (= :tainted (g/compute-taint graph :1-bbb222)))))

   (testing "tainted-nodes returns only tainted"
     (let [tainted (g/tainted-nodes f/incorrect-taint-chain-graph)]
       (is (contains? tainted :1-aaa111))
       (is (not (contains? tainted :1-bbb222)))))) ; Bug in fixture, but tests the function

(deftest compute-taint-usage-in-validators-test
  (testing "compute-taint is used correctly by validators"
    ;; Verify that check-taint-correctness still works correctly after dedup
    (let [result (v/check-taint-correctness f/minimal-valid-graph)]
      ;; Result should be a sequence of errors (empty if valid)
      (is (vector? result))
      ;; For our fixture, taint validation should pass
      (is (empty? result)))))

(deftest independence-check-test
  (testing "Valid single node extraction"
    (let [result (g/check-independence f/minimal-valid-graph :1-abc123 #{:1-abc123})]
      (is (:valid result))))

  (testing "Root not in set"
    (let [result (g/check-independence f/linear-chain-graph :1-aaa111 #{:1-bbb222})]
      (is (not (:valid result)))
      (is (some #(= :root-not-in-set (:type %)) (:errors result)))))

  (testing "Non-verified node rejection"
    (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :proposed)
          result (g/check-independence graph :1-abc123 #{:1-abc123})]
      (is (not (:valid result)))
      (is (some #(= :node-not-verified (:type %)) (:errors result))))))

(deftest token-estimation-test
  (testing "estimate-node-tokens returns positive"
    (let [node (f/make-node :test :statement "Test statement")]
      (is (pos? (g/estimate-node-tokens node)))))

  (testing "estimate-graph-tokens returns positive"
    (is (pos? (g/estimate-graph-tokens f/minimal-valid-graph)))
    (is (pos? (g/estimate-graph-tokens f/linear-chain-graph)))))

(deftest cycle-detection-test
  (testing "would-create-cycle? detects back-edge"
    ;; Adding a new node that depends on :1-ccc333 but is depended on by :1-aaa111 would create cycle
    ;; First add node that :1-aaa111 depends on
    (let [graph (assoc-in f/linear-chain-graph [:nodes :1-aaa111 :dependencies] #{:1-new})]
      (is (g/would-create-cycle? graph :1-new #{:1-ccc333}))))

  (testing "would-create-cycle? detects indirect cycle"
    ;; Adding :1-aaa111 -> :1-ccc333 would create cycle since :1-ccc333 depends on :1-aaa111
    (is (g/would-create-cycle? f/linear-chain-graph :1-aaa111 #{:1-ccc333})))

  (testing "would-create-cycle? allows valid addition"
    (is (not (g/would-create-cycle? f/linear-chain-graph :1-new #{:1-ccc333})))))

(deftest reverse-deps-cache-test
  (testing "Reverse dependencies work correctly"
    ;; Verify get-descendants still works with cache optimization
    (let [desc1 (g/get-descendants f/linear-chain-graph :1-aaa111)]
      ;; Second call uses cached version
      (let [desc2 (g/get-descendants f/linear-chain-graph :1-aaa111)]
        (is (= desc1 desc2)))))

  (testing "Cache is invalidated after modification"
    ;; Build initial cache and verify invalidation
    (let [graph1 f/linear-chain-graph
          desc-before (g/get-descendants graph1 :1-aaa111)
          ;; Invalidate cache
          graph2 (g/invalidate-caches graph1)
          desc-after (g/get-descendants graph2 :1-aaa111)]
      ;; Should still give same result even after cache invalidation
      (is (= desc-before desc-after)))))

(deftest compute-all-scopes-test
  (testing "Batch scope computation matches individual calls"
    ;; For each test fixture, verify compute-all-scopes matches compute-valid-scope
    (doseq [graph [f/minimal-valid-graph f/linear-chain-graph f/diamond-graph f/scoped-graph]]
      (let [all-scopes (g/compute-all-scopes graph)
            individual-scopes (into {} (for [nid (g/node-ids graph)]
                                         [nid (g/compute-valid-scope graph nid)]))]
        (is (= all-scopes individual-scopes)
            (str "Scopes should match for graph with nodes: " (g/node-ids graph))))))

  (testing "Batch scope for scoped graph"
    (let [all-scopes (g/compute-all-scopes f/scoped-graph)]
      ;; :1-ccc333 should have :1-bbb222 in scope (local-assume before discharge)
      (is (contains? (get all-scopes :1-ccc333) :1-bbb222))
      ;; After discharge, :1-bbb222 should be out of scope
      ;; Add a node after the discharge and verify scope is empty
      (let [after-discharge (assoc-in f/scoped-graph [:nodes :1-eee555]
                                      (f/make-node :1-eee555 :deps #{:1-ddd444} :order 4))
            all-scopes-after (g/compute-all-scopes after-discharge)]
        (is (empty? (get all-scopes-after :1-eee555))))))

  (testing "Batch scope returns empty set for nodes without scope"
    (let [all-scopes (g/compute-all-scopes f/linear-chain-graph)]
      ;; Linear chain has no local-assume nodes, so all scopes should be empty
      (doseq [nid (g/node-ids f/linear-chain-graph)]
        (is (empty? (get all-scopes nid)))))))
