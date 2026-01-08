(ns alethfeld.cli-test
  "Tests for alethfeld.cli namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.cli :as cli]))

(deftest test-infrastructure-smoke-test
  (testing "Test infrastructure is working"
    (is (= 1 1) "Basic assertion works")))

(deftest main-function-exists
  (testing "-main function is defined"
    (is (fn? cli/-main) "-main should be a function")))
