(ns alethfeld.ops.recompute-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.graph :as graph]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; Recompute Taint Tests
;; =============================================================================

(deftest recompute-all-taints-test
  (testing "Recompute updates tainted nodes"
    (let [;; Create graph with incorrect taint
          broken-graph (assoc-in f/linear-chain-graph
                                 [:nodes :1-aaa111 :taint] :self-admitted)
          recomputed (graph/recompute-all-taints broken-graph)]
      ;; All nodes should have clean taint (since all are :verified)
      (doseq [[nid node] (:nodes recomputed)]
        (is (= :clean (:taint node)) (str "Node " nid " should be clean")))))

  (testing "Taint propagates from admitted"
    (let [;; Create graph with admitted node
          graph-with-admitted (-> f/linear-chain-graph
                                  (assoc-in [:nodes :1-aaa111 :status] :admitted)
                                  (assoc-in [:nodes :1-aaa111 :taint] :self-admitted))
          recomputed (graph/recompute-all-taints graph-with-admitted)]
      ;; First node should be self-admitted
      (is (= :self-admitted (:taint (get-in recomputed [:nodes :1-aaa111]))))
      ;; Dependent nodes should be tainted
      (is (= :tainted (:taint (get-in recomputed [:nodes :1-bbb222]))))
      (is (= :tainted (:taint (get-in recomputed [:nodes :1-ccc333])))))))

(deftest compute-taint-test
  (testing "Clean node produces clean taint"
    (let [g f/linear-chain-graph]
      (is (= :clean (graph/compute-taint g :1-ccc333)))))

  (testing "Admitted node produces self-admitted"
    (let [g (assoc-in f/linear-chain-graph [:nodes :1-aaa111 :status] :admitted)]
      (is (= :self-admitted (graph/compute-taint g :1-aaa111)))))

  (testing "Node depending on admitted produces tainted"
    (let [g (-> f/linear-chain-graph
                (assoc-in [:nodes :1-aaa111 :status] :admitted)
                (assoc-in [:nodes :1-aaa111 :taint] :self-admitted))]
      (is (= :tainted (graph/compute-taint g :1-bbb222))))))
