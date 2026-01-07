(ns alethfeld.schema-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(deftest validate-schema-test
  (testing "Valid graphs pass schema validation"
    (is (:valid (schema/validate-schema f/minimal-valid-graph)))
    (is (:valid (schema/validate-schema f/linear-chain-graph)))
    (is (:valid (schema/validate-schema f/diamond-graph)))
    (is (:valid (schema/validate-schema f/scoped-graph)))
    (is (:valid (schema/validate-schema f/empty-nodes-graph))))

  (testing "Invalid node type fails schema validation"
    (let [result (schema/validate-schema f/invalid-node-type-graph)]
      (is (not (:valid result)))
      (is (some? (:errors result)))))

  (testing "Invalid status fails schema validation"
    (let [result (schema/validate-schema f/invalid-status-graph)]
      (is (not (:valid result)))
      (is (some? (:errors result))))))

(deftest validate-partial-node-test
  (testing "Partial node validation accepts minimal input"
    (let [partial {:id :1-test
                   :type :claim
                   :statement "Test"
                   :dependencies #{}
                   :scope #{}
                   :justification :modus-ponens
                   :depth 1
                   :display-order 0}]
      (is (:valid (schema/validate-partial-node partial)))))

  (testing "Partial node validation rejects missing fields"
    (let [partial {:id :1-test
                   :type :claim}]  ; Missing required fields
      (is (not (:valid (schema/validate-partial-node partial)))))))
