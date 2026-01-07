(ns alethfeld.version-test
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.version :as version]))

(deftest version-test
  (testing "version is defined"
    (is (string? version/version))
    (is (= "0.1.0" version/version)))

  (testing "spec-version is defined"
    (is (string? version/spec-version))
    (is (= "2.3" version/spec-version)))

  (testing "version-string formats correctly"
    (is (= "Alethfeld CLI v0.1.0 (spec v2.3)" (version/version-string)))))
