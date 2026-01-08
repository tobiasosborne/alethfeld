(ns alethfeld.ops.init-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.init :as init]
            [alethfeld.schema :as schema]))

;; =============================================================================
;; Basic Initialization Tests
;; =============================================================================

(deftest init-graph-basic-test
  (testing "Create minimal valid graph"
    (let [result (init/init-graph "For all $n$, $n^2 \\geq 0$")]
      (is (:ok result))
      (let [graph (:ok result)]
        (is (string? (:graph-id graph)))
        (is (= 1 (:version graph)))
        (is (= "For all $n$, $n^2 \\geq 0$" (get-in graph [:theorem :statement])))
        (is (= {} (:nodes graph)))
        (is (= {} (:lemmas graph)))
        (is (= {} (:external-refs graph)))
        (is (= :strict-mathematics (get-in graph [:metadata :proof-mode]))))))

  (testing "Custom graph ID"
    (let [result (init/init-graph "Theorem" :graph-id "my-proof-001")]
      (is (:ok result))
      (is (= "my-proof-001" (:graph-id (:ok result))))))

  (testing "Custom proof mode"
    (let [result (init/init-graph "Theorem" :proof-mode :formal-physics)]
      (is (:ok result))
      (is (= :formal-physics (get-in (:ok result) [:metadata :proof-mode])))))

  (testing "Custom max tokens"
    (let [result (init/init-graph "Theorem" :max-tokens 50000)]
      (is (:ok result))
      (is (= 50000 (get-in (:ok result) [:metadata :context-budget :max-tokens]))))))

;; =============================================================================
;; Schema Validation Tests
;; =============================================================================

(deftest init-graph-schema-test
  (testing "Generated graph validates against schema"
    (let [result (init/init-graph "Test theorem")]
      (is (:ok result))
      (is (:valid (schema/validate-schema (:ok result)))))))

;; =============================================================================
;; Content Hash Tests
;; =============================================================================

(deftest init-graph-content-hash-test
  (testing "Theorem has content hash"
    (let [result (init/init-graph "Test theorem")]
      (is (:ok result))
      (let [hash (get-in (:ok result) [:theorem :content-hash])]
        (is (string? hash))
        (is (= 16 (count hash)))))))

;; =============================================================================
;; Init With Assumptions Tests
;; =============================================================================

(deftest init-with-assumptions-test
  (testing "Create graph with assumption nodes"
    (let [assumptions [{:label :A1 :statement "Let $f$ be continuous"}
                       {:label :A2 :statement "Let $g$ be continuous"}]
          result (init/init-with-assumptions "Composition is continuous" assumptions)]
      (is (:ok result))
      (let [graph (:ok result)
            nodes (:nodes graph)]
        (is (= 2 (count nodes)))
        (is (contains? nodes :0-A1))
        (is (contains? nodes :0-A2))
        (is (= :assumption (:type (get nodes :0-A1))))
        (is (= :verified (:status (get nodes :0-A1))))
        (is (= "Let $f$ be continuous" (:statement (get nodes :0-A1))))))))

;; =============================================================================
;; Graph ID Generation Tests
;; =============================================================================

(deftest generate-graph-id-test
  (testing "Generate unique graph ID"
    (let [id1 (init/generate-graph-id)
          id2 (init/generate-graph-id)]
      (is (string? id1))
      (is (re-matches #"graph-[a-f0-9]{6}-[a-f0-9]{6}" id1))
      (is (not= id1 id2)))))
