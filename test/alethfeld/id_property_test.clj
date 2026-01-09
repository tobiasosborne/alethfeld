(ns alethfeld.id-property-test
  "Property-based tests for alethfeld.id and alethfeld.path namespaces.

   These tests verify invariants across many generated test cases,
   simulating property-based testing without test.check."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.id :as id]
            [alethfeld.path :as path]))

;; -----------------------------------------------------------------------------
;; Test Data Generators
;; -----------------------------------------------------------------------------

(defn- gen-id-components
  "Generate a vector of positive integer components of given length."
  [length]
  (vec (repeatedly length #(inc (rand-int 100)))))

(defn- gen-valid-id
  "Generate a valid mote ID string with 1 to max-depth components."
  [max-depth]
  (let [depth (inc (rand-int max-depth))
        components (gen-id-components depth)]
    (id/format-id components)))

(defn- gen-valid-ids
  "Generate n valid mote IDs."
  [n max-depth]
  (repeatedly n #(gen-valid-id max-depth)))

(defn- gen-deep-id
  "Generate a valid ID with exactly the specified depth."
  [depth]
  (id/format-id (gen-id-components depth)))

(defn- gen-parent-child-pair
  "Generate a parent ID and a valid child ID."
  [max-parent-depth]
  (let [parent (gen-valid-id max-parent-depth)
        child-num (inc (rand-int 100))]
    [parent (id/child-id parent child-num)]))

;; -----------------------------------------------------------------------------
;; Property: Round-trip (mote-id->path -> path->mote-id)
;; -----------------------------------------------------------------------------

(deftest round-trip-property-test
  (testing "Round-trip: mote-id->path then path->mote-id returns original ID"
    (let [statuses [:fixed :verified :refuted :contested :proposed :rejected]
          test-ids (gen-valid-ids 100 5)]
      (doseq [id test-ids
              status statuses]
        (let [path (path/mote-id->path id status)
              recovered-id (path/path->mote-id path)]
          (is (= id recovered-id)
              (format "Round-trip failed: id=%s status=%s path=%s"
                      id status path))))))

  (testing "Round-trip with deeply nested IDs"
    (let [deep-ids (repeatedly 20 #(gen-deep-id (+ 5 (rand-int 6))))
          statuses [:fixed :proposed :rejected]]
      (doseq [id deep-ids
              status statuses]
        (let [path (path/mote-id->path id status)
              recovered-id (path/path->mote-id path)]
          (is (= id recovered-id)
              (format "Deep round-trip failed: id=%s depth=%d"
                      id (id/id-depth id)))))))

  (testing "Round-trip with root IDs"
    (let [root-ids (map str (range 1 51))
          statuses [:fixed :proposed :rejected]]
      (doseq [id root-ids
              status statuses]
        (let [path (path/mote-id->path id status)
              recovered-id (path/path->mote-id path)]
          (is (= id recovered-id)
              (format "Root round-trip failed: id=%s status=%s" id status)))))))

;; -----------------------------------------------------------------------------
;; Property: parent-id/child-id consistency
;; -----------------------------------------------------------------------------

(deftest parent-child-consistency-property-test
  (testing "child-id creates valid child of parent"
    (let [pairs (repeatedly 100 #(gen-parent-child-pair 4))]
      (doseq [[parent child] pairs]
        (is (= parent (id/parent-id child))
            (format "parent-id of child should equal original parent: parent=%s child=%s"
                    parent child))
        (is (id/is-ancestor? parent child)
            (format "parent should be ancestor of child: parent=%s child=%s"
                    parent child)))))

  (testing "child-id adds exactly one level of depth"
    (let [test-ids (gen-valid-ids 50 5)]
      (doseq [parent test-ids
              :let [child-num (inc (rand-int 100))
                    child (id/child-id parent child-num)]]
        (is (= (inc (id/id-depth parent)) (id/id-depth child))
            (format "child depth should be parent depth + 1: parent=%s child=%s"
                    parent child)))))

  (testing "parent-id reduces depth by exactly one"
    (let [non-root-ids (->> (gen-valid-ids 100 6)
                            (filter #(> (id/id-depth %) 1)))]
      (doseq [id non-root-ids
              :let [parent (id/parent-id id)]]
        (is (some? parent)
            (format "non-root should have parent: id=%s" id))
        (is (= (dec (id/id-depth id)) (id/id-depth parent))
            (format "parent depth should be id depth - 1: id=%s parent=%s"
                    id parent)))))

  (testing "root IDs have no parent"
    (let [root-ids (map str (range 1 101))]
      (doseq [id root-ids]
        (is (nil? (id/parent-id id))
            (format "root ID should have no parent: id=%s" id))))))

;; -----------------------------------------------------------------------------
;; Property: ancestor-ids contains parent-id
;; -----------------------------------------------------------------------------

(deftest ancestor-contains-parent-property-test
  (testing "ancestor-ids contains parent-id for non-root IDs"
    (let [non-root-ids (->> (gen-valid-ids 100 6)
                            (filter #(> (id/id-depth %) 1)))]
      (doseq [id non-root-ids
              :let [parent (id/parent-id id)
                    ancestors (id/ancestor-ids id)]]
        (is (some #{parent} ancestors)
            (format "ancestors should contain parent: id=%s parent=%s ancestors=%s"
                    id parent ancestors))
        (is (= parent (first ancestors))
            (format "first ancestor should be immediate parent: id=%s parent=%s first-ancestor=%s"
                    id parent (first ancestors))))))

  (testing "ancestor-ids returns empty for root IDs"
    (let [root-ids (map str (range 1 101))]
      (doseq [id root-ids]
        (is (= [] (id/ancestor-ids id))
            (format "root should have no ancestors: id=%s" id)))))

  (testing "all ancestors are actually ancestors via is-ancestor?"
    (let [deep-ids (repeatedly 50 #(gen-deep-id (+ 3 (rand-int 4))))]
      (doseq [id deep-ids
              :let [ancestors (id/ancestor-ids id)]]
        (doseq [anc ancestors]
          (is (id/is-ancestor? anc id)
              (format "is-ancestor? should return true for listed ancestor: id=%s anc=%s"
                      id anc)))))))

;; -----------------------------------------------------------------------------
;; Property: id-depth matches ancestor count + 1
;; -----------------------------------------------------------------------------

(deftest depth-matches-ancestor-count-property-test
  (testing "id-depth equals ancestor count + 1"
    (let [test-ids (gen-valid-ids 100 8)]
      (doseq [id test-ids
              :let [depth (id/id-depth id)
                    ancestors (id/ancestor-ids id)]]
        (is (= depth (inc (count ancestors)))
            (format "depth should equal ancestors + 1: id=%s depth=%d ancestors=%d"
                    id depth (count ancestors))))))

  (testing "depth property holds for all depths 1-10"
    (doseq [expected-depth (range 1 11)
            :let [id (gen-deep-id expected-depth)
                  actual-depth (id/id-depth id)
                  ancestor-count (count (id/ancestor-ids id))]]
      (is (= expected-depth actual-depth)
          (format "generated id should have expected depth: id=%s expected=%d actual=%d"
                  id expected-depth actual-depth))
      (is (= expected-depth (inc ancestor-count))
          (format "depth should be ancestors + 1: depth=%d ancestors=%d"
                  expected-depth ancestor-count)))))

;; -----------------------------------------------------------------------------
;; Property: format-id/parse-id round-trip
;; -----------------------------------------------------------------------------

(deftest format-parse-round-trip-property-test
  (testing "format-id then parse-id returns original components"
    (doseq [length (range 1 11)
            _ (range 10)
            :let [components (gen-id-components length)
                  formatted (id/format-id components)
                  parsed (id/parse-id formatted)]]
      (is (= components parsed)
          (format "format->parse round-trip failed: components=%s formatted=%s parsed=%s"
                  components formatted parsed))))

  (testing "parse-id then format-id returns original string"
    (let [test-ids (gen-valid-ids 100 8)]
      (doseq [id test-ids
              :let [parsed (id/parse-id id)
                    formatted (id/format-id parsed)]]
        (is (= id formatted)
            (format "parse->format round-trip failed: id=%s parsed=%s formatted=%s"
                    id parsed formatted))))))

;; -----------------------------------------------------------------------------
;; Property: ancestor chain is ordered and complete
;; -----------------------------------------------------------------------------

(deftest ancestor-chain-completeness-property-test
  (testing "ancestor chain is complete (no gaps)"
    (let [deep-ids (repeatedly 50 #(gen-deep-id (+ 4 (rand-int 5))))]
      (doseq [id deep-ids
              :let [ancestors (id/ancestor-ids id)]]
        ;; Each ancestor should be the parent of the next
        (doseq [[closer farther] (partition 2 1 ancestors)]
          (is (= closer (id/child-id farther (last (id/parse-id closer))))
              (format "ancestor chain should be complete: id=%s closer=%s farther=%s"
                      id closer farther))))))

  (testing "ancestor chain depths decrease by 1 each step"
    (let [deep-ids (repeatedly 30 #(gen-deep-id (+ 5 (rand-int 4))))]
      (doseq [id deep-ids
              :let [ancestors (id/ancestor-ids id)
                    depths (map id/id-depth ancestors)]]
        (when (seq depths)
          (is (apply > depths)
              (format "ancestor depths should strictly decrease: id=%s depths=%s"
                      id (vec depths)))
          (is (= 1 (last depths))
              (format "last ancestor should have depth 1 (root): id=%s ancestors=%s"
                      id ancestors)))))))

;; -----------------------------------------------------------------------------
;; Property: is-ancestor? transitivity
;; -----------------------------------------------------------------------------

(deftest ancestor-transitivity-property-test
  (testing "is-ancestor? is transitive"
    (let [deep-ids (repeatedly 30 #(gen-deep-id (+ 4 (rand-int 4))))]
      (doseq [id deep-ids
              :let [ancestors (id/ancestor-ids id)]]
        ;; If A is ancestor of B and B is ancestor of C, then A is ancestor of C
        (doseq [i (range (count ancestors))
                j (range i (count ancestors))
                :let [closer (nth ancestors i)
                      farther (nth ancestors j)]]
          (when (id/is-ancestor? farther closer)
            (is (id/is-ancestor? farther id)
                (format "transitivity: if %s is ancestor of %s, and %s is ancestor of %s, then %s is ancestor of %s"
                        farther closer closer id farther id)))))))

  (testing "is-ancestor? is not reflexive"
    (let [test-ids (gen-valid-ids 50 5)]
      (doseq [id test-ids]
        (is (not (id/is-ancestor? id id))
            (format "is-ancestor? should not be reflexive: id=%s" id))))))

;; -----------------------------------------------------------------------------
;; Property: root-id is consistent
;; -----------------------------------------------------------------------------

(deftest root-id-consistency-property-test
  (testing "root-id returns depth-1 ID"
    (let [test-ids (gen-valid-ids 100 8)]
      (doseq [id test-ids
              :let [root (id/root-id id)]]
        (is (= 1 (id/id-depth root))
            (format "root should have depth 1: id=%s root=%s" id root)))))

  (testing "root-id is in ancestor chain (or equals id for roots)"
    (let [test-ids (gen-valid-ids 50 6)]
      (doseq [id test-ids
              :let [root (id/root-id id)
                    ancestors (id/ancestor-ids id)]]
        (if (= 1 (id/id-depth id))
          (is (= id root)
              (format "root of root should equal itself: id=%s root=%s" id root))
          (is (some #{root} ancestors)
              (format "root should be in ancestors: id=%s root=%s ancestors=%s"
                      id root ancestors))))))

  (testing "all IDs in a subtree share the same root"
    (let [root-num (inc (rand-int 100))
          root (str root-num)
          ;; Generate children of this root
          children (for [_ (range 20)
                         :let [depth (inc (rand-int 5))
                               components (cons root-num (gen-id-components depth))]]
                     (id/format-id (vec components)))]
      (doseq [child children]
        (is (= root (id/root-id child))
            (format "all descendants should share root: root=%s child=%s"
                    root child))))))

;; -----------------------------------------------------------------------------
;; Property: common-ancestor is symmetric and meaningful
;; -----------------------------------------------------------------------------

(deftest common-ancestor-properties-test
  (testing "common-ancestor is symmetric"
    (let [pairs (for [_ (range 50)]
                  [(gen-valid-id 5) (gen-valid-id 5)])]
      (doseq [[id1 id2] pairs
              :let [ca1 (id/common-ancestor id1 id2)
                    ca2 (id/common-ancestor id2 id1)]]
        (is (= ca1 ca2)
            (format "common-ancestor should be symmetric: id1=%s id2=%s ca1=%s ca2=%s"
                    id1 id2 ca1 ca2)))))

  (testing "common-ancestor is ancestor of both (when exists)"
    (let [;; Generate pairs with same root to ensure common ancestor exists
          pairs (for [_ (range 30)
                      :let [root-num (inc (rand-int 100))
                            id1 (id/format-id (cons root-num (gen-id-components (rand-int 4))))
                            id2 (id/format-id (cons root-num (gen-id-components (rand-int 4))))]]
                  [id1 id2])]
      (doseq [[id1 id2] pairs
              :let [ca (id/common-ancestor id1 id2)]]
        (is (some? ca)
            (format "common ancestor should exist for same-root IDs: id1=%s id2=%s" id1 id2))
        (when (and ca (not= ca id1))
          (is (id/is-ancestor? ca id1)
              (format "common ancestor should be ancestor of id1: ca=%s id1=%s" ca id1)))
        (when (and ca (not= ca id2))
          (is (id/is-ancestor? ca id2)
              (format "common ancestor should be ancestor of id2: ca=%s id2=%s" ca id2))))))

  (testing "common-ancestor of id with itself is the id"
    (let [test-ids (gen-valid-ids 50 5)]
      (doseq [id test-ids]
        (is (= id (id/common-ancestor id id))
            (format "common-ancestor of id with itself should be id: id=%s" id))))))

;; -----------------------------------------------------------------------------
;; Property: sibling relationships
;; -----------------------------------------------------------------------------

(deftest sibling-property-test
  (testing "children of same parent are siblings"
    (let [parents (gen-valid-ids 30 4)]
      (doseq [parent parents
              :let [child1 (id/child-id parent (inc (rand-int 50)))
                    child2 (id/child-id parent (+ 51 (rand-int 50)))]]
        (is (id/is-sibling? child1 child2)
            (format "children of same parent should be siblings: parent=%s c1=%s c2=%s"
                    parent child1 child2)))))

  (testing "is-sibling? is symmetric"
    (let [pairs (for [_ (range 30)
                      :let [parent (gen-valid-id 4)
                            c1 (id/child-id parent (inc (rand-int 50)))
                            c2 (id/child-id parent (+ 51 (rand-int 50)))]]
                  [c1 c2])]
      (doseq [[c1 c2] pairs]
        (is (= (id/is-sibling? c1 c2) (id/is-sibling? c2 c1))
            (format "is-sibling? should be symmetric: c1=%s c2=%s" c1 c2)))))

  (testing "is-sibling? is not reflexive"
    (let [test-ids (gen-valid-ids 50 5)]
      (doseq [id test-ids]
        (is (not (id/is-sibling? id id))
            (format "is-sibling? should not be reflexive: id=%s" id)))))

  (testing "root IDs are never siblings"
    (let [root-pairs (for [i (range 1 21)
                           j (range (inc i) 21)]
                       [(str i) (str j)])]
      (doseq [[r1 r2] root-pairs]
        (is (not (id/is-sibling? r1 r2))
            (format "root IDs should not be siblings: r1=%s r2=%s" r1 r2))))))
