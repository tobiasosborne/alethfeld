(ns alethfeld.id-test
  "Tests for alethfeld.id namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.id :as id]))

;; -----------------------------------------------------------------------------
;; Parsing Tests
;; -----------------------------------------------------------------------------

(deftest parse-id-test
  (testing "parse-id with valid IDs"
    (is (= [1] (id/parse-id "1")))
    (is (= [1 2] (id/parse-id "1.2")))
    (is (= [1 2 3] (id/parse-id "1.2.3")))
    (is (= [10 20 30] (id/parse-id "10.20.30")))
    (is (= [1 2 3 4 5] (id/parse-id "1.2.3.4.5"))))

  (testing "parse-id with invalid IDs"
    (is (nil? (id/parse-id "")))
    (is (nil? (id/parse-id nil)))
    (is (nil? (id/parse-id "abc")))
    (is (nil? (id/parse-id "1.2.a")))
    (is (nil? (id/parse-id ".1")))
    (is (nil? (id/parse-id "1.")))
    (is (nil? (id/parse-id "1..2")))
    (is (nil? (id/parse-id " 1.2")))
    (is (nil? (id/parse-id "1.2 ")))))

(deftest valid-id?-test
  (testing "valid-id? returns true for valid IDs"
    (is (true? (id/valid-id? "1")))
    (is (true? (id/valid-id? "1.2.3"))))

  (testing "valid-id? returns false for invalid IDs"
    (is (false? (id/valid-id? "")))
    (is (false? (id/valid-id? nil)))
    (is (false? (id/valid-id? "abc")))))

(deftest format-id-test
  (testing "format-id converts components to string"
    (is (= "1" (id/format-id [1])))
    (is (= "1.2" (id/format-id [1 2])))
    (is (= "1.2.3" (id/format-id [1 2 3])))))

;; -----------------------------------------------------------------------------
;; Navigation Tests
;; -----------------------------------------------------------------------------

(deftest id-depth-test
  (testing "id-depth returns component count"
    (is (= 1 (id/id-depth "1")))
    (is (= 2 (id/id-depth "1.2")))
    (is (= 3 (id/id-depth "1.2.3")))
    (is (= 5 (id/id-depth "1.2.3.4.5"))))

  (testing "id-depth returns nil for invalid IDs"
    (is (nil? (id/id-depth "")))))

(deftest root-id-test
  (testing "root-id returns first component"
    (is (= "1" (id/root-id "1")))
    (is (= "1" (id/root-id "1.2")))
    (is (= "1" (id/root-id "1.2.3")))
    (is (= "5" (id/root-id "5.1.2"))))

  (testing "root-id returns nil for invalid IDs"
    (is (nil? (id/root-id "")))))

(deftest parent-id-test
  (testing "parent-id returns parent for non-root"
    (is (= "1" (id/parent-id "1.2")))
    (is (= "1.2" (id/parent-id "1.2.3")))
    (is (= "1.2.3" (id/parent-id "1.2.3.4"))))

  (testing "parent-id returns nil for root"
    (is (nil? (id/parent-id "1")))
    (is (nil? (id/parent-id "5"))))

  (testing "parent-id returns nil for invalid IDs"
    (is (nil? (id/parent-id "")))))

(deftest child-id-test
  (testing "child-id appends component"
    (is (= "1.1" (id/child-id "1" 1)))
    (is (= "1.2" (id/child-id "1" 2)))
    (is (= "1.2.3" (id/child-id "1.2" 3)))
    (is (= "1.2.3.10" (id/child-id "1.2.3" 10))))

  (testing "child-id returns nil for invalid inputs"
    (is (nil? (id/child-id "" 1)))
    (is (nil? (id/child-id "1" 0)))
    (is (nil? (id/child-id "1" -1)))
    (is (nil? (id/child-id "1" nil)))))

(deftest next-child-id-test
  (testing "next-child-id with no existing children"
    (is (= "1.1" (id/next-child-id "1" [])))
    (is (= "1.2.1" (id/next-child-id "1.2" []))))

  (testing "next-child-id with existing children"
    (is (= "1.3" (id/next-child-id "1" ["1.1" "1.2"])))
    (is (= "1.4" (id/next-child-id "1" ["1.1" "1.2" "1.3"]))))

  (testing "next-child-id does not fill gaps"
    (is (= "1.4" (id/next-child-id "1" ["1.1" "1.3"])))
    (is (= "1.6" (id/next-child-id "1" ["1.1" "1.5"]))))

  (testing "next-child-id ignores non-direct children"
    (is (= "1.3" (id/next-child-id "1" ["1.1" "1.2" "1.1.1" "1.2.1"]))))

  (testing "next-child-id returns nil for invalid parent"
    (is (nil? (id/next-child-id "" [])))))

;; -----------------------------------------------------------------------------
;; Ancestry Tests
;; -----------------------------------------------------------------------------

(deftest is-ancestor?-test
  (testing "is-ancestor? with direct ancestors"
    (is (true? (id/is-ancestor? "1" "1.2")))
    (is (true? (id/is-ancestor? "1.2" "1.2.3"))))

  (testing "is-ancestor? with indirect ancestors"
    (is (true? (id/is-ancestor? "1" "1.2.3")))
    (is (true? (id/is-ancestor? "1" "1.2.3.4.5"))))

  (testing "is-ancestor? returns false for same ID"
    (is (false? (id/is-ancestor? "1" "1")))
    (is (false? (id/is-ancestor? "1.2.3" "1.2.3"))))

  (testing "is-ancestor? returns false for non-ancestors"
    (is (false? (id/is-ancestor? "1.2" "1.3")))
    (is (false? (id/is-ancestor? "2" "1.2")))
    (is (false? (id/is-ancestor? "1.2.3" "1.2"))))

  (testing "is-ancestor? returns nil for invalid IDs"
    (is (nil? (id/is-ancestor? "" "1.2")))
    (is (nil? (id/is-ancestor? "1" "")))))

(deftest is-descendant?-test
  (testing "is-descendant? is inverse of is-ancestor?"
    (is (true? (id/is-descendant? "1.2" "1")))
    (is (true? (id/is-descendant? "1.2.3" "1")))
    (is (false? (id/is-descendant? "1" "1.2")))))

(deftest is-sibling?-test
  (testing "is-sibling? with actual siblings"
    (is (true? (id/is-sibling? "1.1" "1.2")))
    (is (true? (id/is-sibling? "1.2.1" "1.2.2"))))

  (testing "is-sibling? returns false for same ID"
    (is (false? (id/is-sibling? "1.1" "1.1"))))

  (testing "is-sibling? returns false for non-siblings"
    (is (false? (id/is-sibling? "1.1" "2.1")))
    (is (false? (id/is-sibling? "1.1" "1.1.1"))))

  (testing "is-sibling? returns false for roots"
    (is (false? (id/is-sibling? "1" "2")))))

(deftest ancestor-ids-test
  (testing "ancestors returns empty for roots"
    (is (= [] (id/ancestor-ids "1")))
    (is (= [] (id/ancestor-ids "5"))))

  (testing "ancestors returns parent chain"
    (is (= ["1"] (id/ancestor-ids "1.2")))
    (is (= ["1.2" "1"] (id/ancestor-ids "1.2.3")))
    (is (= ["1.2.3" "1.2" "1"] (id/ancestor-ids "1.2.3.4"))))

  (testing "ancestors returns nil for invalid IDs"
    (is (nil? (id/ancestor-ids "")))))

(deftest common-ancestor-test
  (testing "common-ancestor finds deepest shared ancestor"
    (is (= "1.2" (id/common-ancestor "1.2.3" "1.2.4")))
    (is (= "1" (id/common-ancestor "1.2" "1.3")))
    (is (= "1" (id/common-ancestor "1.2.3" "1.4.5"))))

  (testing "common-ancestor with one being ancestor of other"
    (is (= "1" (id/common-ancestor "1" "1.2")))
    (is (= "1.2" (id/common-ancestor "1.2" "1.2.3"))))

  (testing "common-ancestor returns nil for different roots"
    (is (nil? (id/common-ancestor "1" "2")))
    (is (nil? (id/common-ancestor "1.2" "2.3"))))

  (testing "common-ancestor for same ID"
    (is (= "1.2.3" (id/common-ancestor "1.2.3" "1.2.3")))))
