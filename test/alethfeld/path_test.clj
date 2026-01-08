(ns alethfeld.path-test
  "Tests for alethfeld.path namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.path :as path]))

;; -----------------------------------------------------------------------------
;; Base Path Tests
;; -----------------------------------------------------------------------------

(deftest config-path-test
  (testing "config-path returns correct path"
    (is (= ".alethfeld/config.edn" (path/config-path)))))

(deftest motes-path-test
  (testing "motes-path returns correct path"
    (is (= ".alethfeld/motes" (path/motes-path)))))

(deftest proposed-path-test
  (testing "proposed-path returns correct path"
    (is (= ".alethfeld/proposed" (path/proposed-path)))))

(deftest archive-path-test
  (testing "archive-path returns correct path"
    (is (= ".alethfeld/archive" (path/archive-path)))))

;; -----------------------------------------------------------------------------
;; mote-id->path Tests
;; -----------------------------------------------------------------------------

(deftest mote-id->path-fixed-test
  (testing "mote-id->path for :fixed status"
    (is (= ".alethfeld/motes/1.edn"
           (path/mote-id->path "1" :fixed)))
    (is (= ".alethfeld/motes/1/1.2.edn"
           (path/mote-id->path "1.2" :fixed)))
    (is (= ".alethfeld/motes/1/1.2/1.2.3.edn"
           (path/mote-id->path "1.2.3" :fixed)))
    (is (= ".alethfeld/motes/1/1.2/1.2.3/1.2.3.4.edn"
           (path/mote-id->path "1.2.3.4" :fixed))))

  (testing "mote-id->path for :verified status (same as :fixed)"
    (is (= ".alethfeld/motes/1/1.2.edn"
           (path/mote-id->path "1.2" :verified))))

  (testing "mote-id->path for :refuted status (same as :fixed)"
    (is (= ".alethfeld/motes/1/1.2.edn"
           (path/mote-id->path "1.2" :refuted))))

  (testing "mote-id->path for :contested status (same as :fixed)"
    (is (= ".alethfeld/motes/1/1.2.edn"
           (path/mote-id->path "1.2" :contested)))))

(deftest mote-id->path-proposed-test
  (testing "mote-id->path for :proposed status"
    (is (= ".alethfeld/proposed/1.edn"
           (path/mote-id->path "1" :proposed)))
    (is (= ".alethfeld/proposed/1.2.edn"
           (path/mote-id->path "1.2" :proposed)))
    (is (= ".alethfeld/proposed/1.2.3.edn"
           (path/mote-id->path "1.2.3" :proposed)))))

(deftest mote-id->path-rejected-test
  (testing "mote-id->path for :rejected status"
    (is (= ".alethfeld/archive/1.edn"
           (path/mote-id->path "1" :rejected)))
    (is (= ".alethfeld/archive/1/1.2.edn"
           (path/mote-id->path "1.2" :rejected)))
    (is (= ".alethfeld/archive/1/1.2/1.2.3.edn"
           (path/mote-id->path "1.2.3" :rejected)))))

(deftest mote-id->path-invalid-test
  (testing "mote-id->path returns nil for invalid IDs"
    (is (nil? (path/mote-id->path "" :fixed)))
    (is (nil? (path/mote-id->path nil :fixed)))
    (is (nil? (path/mote-id->path "abc" :fixed)))))

;; -----------------------------------------------------------------------------
;; path->mote-id Tests
;; -----------------------------------------------------------------------------

(deftest path->mote-id-test
  (testing "path->mote-id extracts ID from motes paths"
    (is (= "1" (path/path->mote-id ".alethfeld/motes/1.edn")))
    (is (= "1.2" (path/path->mote-id ".alethfeld/motes/1/1.2.edn")))
    (is (= "1.2.3" (path/path->mote-id ".alethfeld/motes/1/1.2/1.2.3.edn"))))

  (testing "path->mote-id extracts ID from proposed paths"
    (is (= "1.2.3" (path/path->mote-id ".alethfeld/proposed/1.2.3.edn"))))

  (testing "path->mote-id extracts ID from archive paths"
    (is (= "1.2.3" (path/path->mote-id ".alethfeld/archive/1/1.2/1.2.3.edn"))))

  (testing "path->mote-id handles absolute paths"
    (is (= "1.2" (path/path->mote-id "/home/user/project/.alethfeld/motes/1/1.2.edn"))))

  (testing "path->mote-id returns nil for invalid paths"
    (is (nil? (path/path->mote-id nil)))
    (is (nil? (path/path->mote-id "")))
    (is (nil? (path/path->mote-id ".alethfeld/motes/abc.edn")))
    (is (nil? (path/path->mote-id ".alethfeld/config.edn")))))

;; -----------------------------------------------------------------------------
;; path->status Tests
;; -----------------------------------------------------------------------------

(deftest path->status-test
  (testing "path->status infers status from path"
    (is (= :fixed (path/path->status ".alethfeld/motes/1.edn")))
    (is (= :fixed (path/path->status ".alethfeld/motes/1/1.2.edn")))
    (is (= :proposed (path/path->status ".alethfeld/proposed/1.2.edn")))
    (is (= :rejected (path/path->status ".alethfeld/archive/1/1.2.edn"))))

  (testing "path->status handles absolute paths"
    (is (= :fixed (path/path->status "/abs/.alethfeld/motes/1.edn")))
    (is (= :proposed (path/path->status "/abs/.alethfeld/proposed/1.edn"))))

  (testing "path->status returns nil for unknown paths"
    (is (nil? (path/path->status nil)))
    (is (nil? (path/path->status "")))
    (is (nil? (path/path->status "/some/other/path.edn")))))

;; -----------------------------------------------------------------------------
;; Round-trip Tests
;; -----------------------------------------------------------------------------

(deftest round-trip-test
  (testing "mote-id->path and path->mote-id are inverses"
    (doseq [id ["1" "1.2" "1.2.3" "10.20.30"]
            status [:fixed :proposed :rejected]]
      (let [path (path/mote-id->path id status)
            extracted-id (path/path->mote-id path)]
        (is (= id extracted-id)
            (str "Round-trip failed for id=" id " status=" status))))))

;; -----------------------------------------------------------------------------
;; Directory Tests
;; -----------------------------------------------------------------------------

(deftest mote-dir-test
  (testing "mote-dir returns child directory"
    (is (= ".alethfeld/motes/1" (path/mote-dir "1")))
    (is (= ".alethfeld/motes/1/1.2" (path/mote-dir "1.2")))
    (is (= ".alethfeld/motes/1/1.2/1.2.3" (path/mote-dir "1.2.3"))))

  (testing "mote-dir returns nil for invalid IDs"
    (is (nil? (path/mote-dir "")))))

(deftest parent-dir-test
  (testing "parent-dir returns containing directory"
    (is (= ".alethfeld/motes" (path/parent-dir "1")))
    (is (= ".alethfeld/motes/1" (path/parent-dir "1.2")))
    (is (= ".alethfeld/motes/1/1.2" (path/parent-dir "1.2.3"))))

  (testing "parent-dir returns nil for invalid IDs"
    (is (nil? (path/parent-dir "")))))
