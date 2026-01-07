(ns alethfeld.ops.replace-node-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.replace-node :as replace-node]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(defn make-partial-node [id & opts]
  (apply f/make-node id opts))

(defn make-rejected-graph []
  "Create a graph with a rejected node that has dependents."
  (f/make-graph [(f/make-node :1-aaa111
                              :type :assumption
                              :justification :assumption
                              :depth 0)
                 (f/make-node :1-bbb222
                              :deps #{:1-aaa111}
                              :status :rejected
                              :taint :tainted)
                 (f/make-node :1-ccc333
                              :deps #{:1-bbb222}
                              :taint :tainted)]))

(deftest replace-node-basic-test
  (testing "Replace rejected node successfully"
    (let [graph (make-rejected-graph)
          new-node {:id :1-bbb333
                    :type :claim
                    :statement "Revised claim"
                    :dependencies #{:1-aaa111}
                    :scope #{}
                    :justification :modus-ponens
                    :depth 1
                    :display-order 1}
          result (replace-node/replace-node graph :1-bbb222 new-node)]
      (is (:ok result))
      (let [g (:ok result)]
        ;; Old node archived
        (is (contains? (:archived-nodes g) :1-bbb222))
        ;; New node added
        (is (contains? (:nodes g) :1-bbb333))
        ;; Provenance set
        (is (= :1-bbb222 (get-in g [:nodes :1-bbb333 :provenance :revision-of])))
        ;; Dependent rewritten
        (is (contains? (get-in g [:nodes :1-ccc333 :dependencies]) :1-bbb333))
        (is (not (contains? (get-in g [:nodes :1-ccc333 :dependencies]) :1-bbb222)))))))

(deftest replace-node-rejection-test
  (testing "Reject replace of non-rejected node"
    (let [result (replace-node/replace-node f/linear-chain-graph :1-bbb222
                                            {:id :1-new
                                             :type :claim
                                             :statement "New"
                                             :dependencies #{}
                                             :scope #{}
                                             :justification :modus-ponens
                                             :depth 1
                                             :display-order 0})]
      (is (:error result))
      (is (some #(= :not-rejected (:type %)) (:error result)))))

  (testing "Reject replace of non-existent node"
    (let [result (replace-node/replace-node f/linear-chain-graph :nonexistent
                                            {:id :1-new
                                             :type :claim
                                             :statement "New"
                                             :dependencies #{}
                                             :scope #{}
                                             :justification :modus-ponens
                                             :depth 1
                                             :display-order 0})]
      (is (:error result))
      (is (some #(= :node-not-found (:type %)) (:error result))))))

(deftest replace-node-schema-validation-test
  (testing "Output validates against schema"
    (let [graph (make-rejected-graph)
          new-node {:id :1-bbb333
                    :type :claim
                    :statement "Revised claim"
                    :dependencies #{:1-aaa111}
                    :scope #{}
                    :justification :modus-ponens
                    :depth 1
                    :display-order 1}
          result (replace-node/replace-node graph :1-bbb222 new-node)]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))
