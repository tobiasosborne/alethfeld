(ns alethfeld.ops.delete-node-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.delete-node :as delete-node]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(deftest delete-node-basic-test
  (testing "Delete leaf node (no dependents)"
    (let [result (delete-node/delete-node f/linear-chain-graph :1-ccc333)]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (not (contains? (:nodes graph) :1-ccc333)))
        (is (contains? (:archived-nodes graph) :1-ccc333)))))

  (testing "Archived node preserves all fields"
    (let [result (delete-node/delete-node f/linear-chain-graph :1-ccc333)]
      (is (:ok result))
      (let [archived (get-in (:ok result) [:archived-nodes :1-ccc333])
            original (get-in f/linear-chain-graph [:nodes :1-ccc333])]
        (is (= (:id original) (:id archived)))
        (is (= (:statement original) (:statement archived)))
        (is (= (:dependencies original) (:dependencies archived)))))))

(deftest delete-node-rejection-test
  (testing "Reject delete of node with dependents"
    (let [result (delete-node/delete-node f/linear-chain-graph :1-aaa111)]
      (is (:error result))
      (is (some #(= :has-dependents (:type %)) (:error result)))))

  (testing "Reject delete of non-existent node"
    (let [result (delete-node/delete-node f/linear-chain-graph :nonexistent)]
      (is (:error result))
      (is (some #(= :node-not-found (:type %)) (:error result))))))

(deftest delete-chain-test
  (testing "Can delete nodes in reverse dependency order"
    (let [;; Delete :1-ccc333 first (leaf)
          result1 (delete-node/delete-node f/linear-chain-graph :1-ccc333)
          _ (is (:ok result1))
          graph1 (:ok result1)

          ;; Now :1-bbb222 is a leaf
          result2 (delete-node/delete-node graph1 :1-bbb222)
          _ (is (:ok result2))
          graph2 (:ok result2)

          ;; Now :1-aaa111 is a leaf
          result3 (delete-node/delete-node graph2 :1-aaa111)]
      (is (:ok result3))
      (is (empty? (:nodes (:ok result3))))
      (is (= 3 (count (:archived-nodes (:ok result3))))))))

(deftest version-increment-test
  (testing "Version incremented after delete"
    (let [result (delete-node/delete-node f/linear-chain-graph :1-ccc333)]
      (is (:ok result))
      (is (= 2 (:version (:ok result)))))))

(deftest output-validates-test
  (testing "Output graph validates against schema"
    (let [result (delete-node/delete-node f/linear-chain-graph :1-ccc333)]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))
