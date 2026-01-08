(ns alethfeld.dag-test
  "Tests for alethfeld.dag namespace - DAG validation functions."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.dag :as dag]
            [alethfeld.mote :as m]))

;; -----------------------------------------------------------------------------
;; Test Fixtures - Helper Functions
;; -----------------------------------------------------------------------------

(defn- make-test-mote
  "Create a simple test mote with minimal required fields."
  [id & {:keys [parent children assumptions status proposal]
         :or {children [] assumptions [] status :fixed}}]
  (cond-> (m/make-mote id (str "Claim for " id) "test-agent"
                       :children children
                       :assumptions assumptions
                       :status status)
    parent (assoc :parent parent)
    proposal (assoc :proposal proposal)))

(defn- motes->map
  "Convert a sequence of motes into a map keyed by id."
  [motes]
  (into {} (map (juxt :id identity) motes)))

;; -----------------------------------------------------------------------------
;; validate-parent-child Tests
;; -----------------------------------------------------------------------------

(deftest validate-parent-child-test
  (testing "valid parent-child relationships pass"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"])
                  (make-test-mote "1.1" :parent "1")
                  (make-test-mote "1.2" :parent "1")])]
      (is (nil? (dag/validate-parent-child motes)))))

  (testing "empty motes collection passes"
    (is (nil? (dag/validate-parent-child {}))))

  (testing "single root mote passes"
    (let [motes (motes->map [(make-test-mote "1")])]
      (is (nil? (dag/validate-parent-child motes)))))

  (testing "deeply nested valid structure passes"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])
                  (make-test-mote "1.1" :parent "1" :children ["1.1.1"])
                  (make-test-mote "1.1.1" :parent "1.1" :children ["1.1.1.1"])
                  (make-test-mote "1.1.1.1" :parent "1.1.1")])]
      (is (nil? (dag/validate-parent-child motes)))))

  (testing "orphan child detected - child claims parent that doesn't list it"
    (let [motes (motes->map
                 [(make-test-mote "1" :children [])  ; Does not list 1.1 as child
                  (make-test-mote "1.1" :parent "1")])]  ; Claims 1 as parent
      (let [result (dag/validate-parent-child motes)]
        (is (some? result))
        (is (= :orphan-child (:type result)))
        (is (= "1.1" (:child-id result)))
        (is (= "1" (:claimed-parent result))))))

  (testing "phantom child detected - parent lists non-existent child"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])])]  ; Lists 1.1 but it doesn't exist
      (let [result (dag/validate-parent-child motes)]
        (is (some? result))
        (is (= :phantom-child (:type result)))
        (is (= "1" (:parent-id result)))
        (is (= "1.1" (:child-id result))))))

  (testing "mismatched parent detected - child exists but has wrong/no parent"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])
                  (make-test-mote "1.1")])]  ; No parent field
      (let [result (dag/validate-parent-child motes)]
        (is (some? result))
        (is (= :mismatched-parent (:type result)))
        (is (= "1.1" (:child-id result)))
        (is (= "1" (:expected-parent result)))
        (is (nil? (:actual-parent result))))))

  (testing "wrong parent detected"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])
                  (make-test-mote "2")
                  (make-test-mote "1.1" :parent "2")])]  ; Claims different parent
      (let [result (dag/validate-parent-child motes)]
        (is (some? result))
        (is (= :mismatched-parent (:type result)))
        (is (= "1.1" (:child-id result)))
        (is (= "1" (:expected-parent result)))
        (is (= "2" (:actual-parent result)))))))

;; -----------------------------------------------------------------------------
;; find-cycles Tests
;; -----------------------------------------------------------------------------

(deftest find-cycles-test
  (testing "no cycles in valid DAG"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2")])]
      (is (nil? (dag/find-cycles motes)))))

  (testing "empty motes collection has no cycles"
    (is (nil? (dag/find-cycles {}))))

  (testing "self-referencing cycle detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "1"}])])]  ; References itself
      (let [result (dag/find-cycles motes)]
        (is (vector? result))
        (is (some #(= "1" %) result)))))

  (testing "simple two-node cycle detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "1"}])])]
      (let [result (dag/find-cycles motes)]
        (is (vector? result))
        (is (>= (count result) 2))
        (is (some #(= "1" %) result))
        (is (some #(= "2" %) result)))))

  (testing "three-node cycle detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "3"}])
                  (make-test-mote "3"
                    :assumptions [{:type :internal :ref "1"}])])]
      (let [result (dag/find-cycles motes)]
        (is (vector? result))
        (is (>= (count result) 2)))))

  (testing "external refs do not contribute to cycles"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :external :ref "arXiv:123"}
                                  {:type :internal :ref "2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :external :ref "DOI:456"}])])]
      (is (nil? (dag/find-cycles motes)))))

  (testing "cycle in larger graph detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "3"}])
                  (make-test-mote "3"
                    :assumptions [{:type :internal :ref "4"}])
                  (make-test-mote "4"
                    :assumptions [{:type :internal :ref "2"}])  ; Cycle: 2->3->4->2
                  (make-test-mote "5")])]  ; Isolated node
      (let [result (dag/find-cycles motes)]
        (is (vector? result))
        (is (some #(contains? #{"2" "3" "4"} %) result))))))

;; -----------------------------------------------------------------------------
;; validate-refs Tests
;; -----------------------------------------------------------------------------

(deftest validate-refs-test
  (testing "valid refs pass"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2")])]
      (is (nil? (dag/validate-refs motes)))))

  (testing "empty motes collection passes"
    (is (nil? (dag/validate-refs {}))))

  (testing "mote with no assumptions passes"
    (let [motes (motes->map [(make-test-mote "1")])]
      (is (nil? (dag/validate-refs motes)))))

  (testing "external refs are not validated"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :external :ref "arXiv:nonexistent"}])])]
      (is (nil? (dag/validate-refs motes)))))

  (testing "broken internal ref detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "nonexistent"}])])]
      (let [result (dag/validate-refs motes)]
        (is (vector? result))
        (is (= 1 (count result)))
        (is (= "1" (:mote-id (first result))))
        (is (= "nonexistent" (:ref (first result)))))))

  (testing "multiple broken refs detected"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "missing1"}
                                  {:type :internal :ref "missing2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "missing3"}])])]
      (let [result (dag/validate-refs motes)]
        (is (vector? result))
        (is (= 3 (count result))))))

  (testing "mixed valid and broken refs reports only broken ones"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}
                                  {:type :internal :ref "missing"}])
                  (make-test-mote "2")])]
      (let [result (dag/validate-refs motes)]
        (is (vector? result))
        (is (= 1 (count result)))
        (is (= "missing" (:ref (first result))))))))

;; -----------------------------------------------------------------------------
;; validate-proposal-atomicity Tests
;; -----------------------------------------------------------------------------

(deftest validate-proposal-atomicity-test
  (testing "motes without proposals pass"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"])
                  (make-test-mote "1.1" :parent "1")
                  (make-test-mote "1.2" :parent "1")])]
      (is (nil? (dag/validate-proposal-atomicity motes)))))

  (testing "empty motes collection passes"
    (is (nil? (dag/validate-proposal-atomicity {}))))

  (testing "proposal with all children same status passes"
    (let [proposal (m/make-proposal "proposer" ["1.1" "1.2"])
          motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"]
                                  :proposal proposal)
                  (make-test-mote "1.1" :parent "1" :status :proposed)
                  (make-test-mote "1.2" :parent "1" :status :proposed)])]
      (is (nil? (dag/validate-proposal-atomicity motes)))))

  (testing "approved proposal with all children fixed passes"
    (let [proposal (assoc (m/make-proposal "proposer" ["1.1" "1.2"])
                          :status :approved)
          motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"]
                                  :proposal proposal)
                  (make-test-mote "1.1" :parent "1" :status :fixed)
                  (make-test-mote "1.2" :parent "1" :status :fixed)])]
      (is (nil? (dag/validate-proposal-atomicity motes)))))

  (testing "rejected proposal with all children rejected passes"
    (let [proposal (assoc (m/make-proposal "proposer" ["1.1" "1.2"])
                          :status :rejected)
          motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"]
                                  :proposal proposal)
                  (make-test-mote "1.1" :parent "1" :status :rejected)
                  (make-test-mote "1.2" :parent "1" :status :rejected)])]
      (is (nil? (dag/validate-proposal-atomicity motes)))))

  (testing "proposal with mixed child statuses violates atomicity"
    (let [proposal (m/make-proposal "proposer" ["1.1" "1.2"])
          motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"]
                                  :proposal proposal)
                  (make-test-mote "1.1" :parent "1" :status :fixed)
                  (make-test-mote "1.2" :parent "1" :status :proposed)])]
      (let [result (dag/validate-proposal-atomicity motes)]
        (is (some? result))
        (is (= :atomicity-violation (:type result)))
        (is (= "1" (:parent-id result)))
        (is (some? (:children-statuses result))))))

  (testing "proposal with missing child detected"
    (let [proposal (m/make-proposal "proposer" ["1.1" "1.2"])
          motes (motes->map
                 [(make-test-mote "1" :children ["1.1" "1.2"]
                                  :proposal proposal)
                  (make-test-mote "1.1" :parent "1" :status :proposed)])]
      ;; Missing 1.2 - this should be caught
      (let [result (dag/validate-proposal-atomicity motes)]
        (is (some? result))
        (is (= :missing-proposal-child (:type result)))))))

;; -----------------------------------------------------------------------------
;; validate-mote-graph Tests
;; -----------------------------------------------------------------------------

(deftest validate-mote-graph-test
  (testing "valid graph returns valid result"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])
                  (make-test-mote "1.1" :parent "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2")])]
      (let [result (dag/validate-mote-graph motes)]
        (is (:valid? result))
        (is (empty? (:errors result))))))

  (testing "empty motes collection is valid"
    (let [result (dag/validate-mote-graph {})]
      (is (:valid? result))
      (is (empty? (:errors result)))))

  (testing "multiple validation failures collected"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])  ; 1.1 claims different parent
                  (make-test-mote "1.1" :parent "2"      ; Wrong parent
                    :assumptions [{:type :internal :ref "missing"}])  ; Broken ref
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "2"}])])]  ; Self-cycle
      (let [result (dag/validate-mote-graph motes)]
        (is (not (:valid? result)))
        (is (pos? (count (:errors result)))))))

  (testing "result contains categorized errors"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "missing"}])])]
      (let [result (dag/validate-mote-graph motes)]
        (is (not (:valid? result)))
        (is (some #(= :broken-refs (:category %)) (:errors result))))))

  (testing "parent-child errors are included"
    (let [motes (motes->map
                 [(make-test-mote "1" :children ["1.1"])])]  ; Missing child
      (let [result (dag/validate-mote-graph motes)]
        (is (not (:valid? result)))
        (is (some #(= :parent-child (:category %)) (:errors result))))))

  (testing "cycle errors are included"
    (let [motes (motes->map
                 [(make-test-mote "1"
                    :assumptions [{:type :internal :ref "2"}])
                  (make-test-mote "2"
                    :assumptions [{:type :internal :ref "1"}])])]
      (let [result (dag/validate-mote-graph motes)]
        (is (not (:valid? result)))
        (is (some #(= :cycle (:category %)) (:errors result)))))))
