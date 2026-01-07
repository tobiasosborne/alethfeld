(ns alethfeld.ops.update-status-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(deftest update-status-basic-test
  (testing "Update proposed to verified"
    (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :proposed)
          result (update-status/update-status graph :1-abc123 :verified)]
      (is (:ok result))
      (is (= :verified (:status (get-in (:ok result) [:nodes :1-abc123]))))))

  (testing "Update proposed to rejected"
    (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :proposed)
          result (update-status/update-status graph :1-abc123 :rejected)]
      (is (:ok result))
      (is (= :rejected (:status (get-in (:ok result) [:nodes :1-abc123]))))
      (is (= :tainted (:taint (get-in (:ok result) [:nodes :1-abc123])))))))

(deftest update-status-admitted-test
  (testing "Update proposed to admitted adds obligation"
    (let [graph (assoc-in f/minimal-valid-graph [:nodes :1-abc123 :status] :proposed)
          result (update-status/update-status graph :1-abc123 :admitted)]
      (is (:ok result))
      (let [new-graph (:ok result)]
        (is (= :admitted (:status (get-in new-graph [:nodes :1-abc123]))))
        (is (= :self-admitted (:taint (get-in new-graph [:nodes :1-abc123]))))
        (is (= 1 (count (:obligations new-graph))))
        (is (= :1-abc123 (:node-id (first (:obligations new-graph))))))))

  (testing "Update admitted to verified removes obligation"
    (let [graph (-> f/minimal-valid-graph
                    (assoc-in [:nodes :1-abc123 :status] :admitted)
                    (assoc-in [:nodes :1-abc123 :taint] :self-admitted)
                    (assoc :obligations [{:node-id :1-abc123
                                          :claim "Test"
                                          :context {:assumptions [] :scope []}}]))
          result (update-status/update-status graph :1-abc123 :verified)]
      (is (:ok result))
      (let [new-graph (:ok result)]
        (is (= :verified (:status (get-in new-graph [:nodes :1-abc123]))))
        (is (empty? (:obligations new-graph)))))))

(deftest update-status-rejection-test
  (testing "Reject invalid status"
    (let [result (update-status/update-status f/minimal-valid-graph :1-abc123 :invalid)]
      (is (:error result))
      (is (some #(= :invalid-status (:type %)) (:error result)))))

  (testing "Reject non-existent node"
    (let [result (update-status/update-status f/minimal-valid-graph :nonexistent :verified)]
      (is (:error result))
      (is (some #(= :node-not-found (:type %)) (:error result))))))

(deftest taint-propagation-test
  (testing "Admit node propagates taint to dependents"
    (let [result (update-status/update-status f/linear-chain-graph :1-aaa111 :admitted)]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (= :self-admitted (:taint (get-in graph [:nodes :1-aaa111]))))
        (is (= :tainted (:taint (get-in graph [:nodes :1-bbb222]))))
        (is (= :tainted (:taint (get-in graph [:nodes :1-ccc333])))))))

  (testing "Diamond pattern taint propagation"
    (let [result (update-status/update-status f/diamond-graph :1-aaa111 :admitted)]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (= :self-admitted (:taint (get-in graph [:nodes :1-aaa111]))))
        (is (= :tainted (:taint (get-in graph [:nodes :1-bbb222]))))
        (is (= :tainted (:taint (get-in graph [:nodes :1-ccc333]))))
        (is (= :tainted (:taint (get-in graph [:nodes :1-ddd444]))))))))

(deftest version-increment-test
  (testing "Version incremented after status update"
    (let [result (update-status/update-status f/minimal-valid-graph :1-abc123 :verified)]
      (is (:ok result))
      (is (= 2 (:version (:ok result)))))))

(deftest output-validates-test
  (testing "Output graph validates against schema"
    (let [result (update-status/update-status f/minimal-valid-graph :1-abc123 :admitted)]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))
