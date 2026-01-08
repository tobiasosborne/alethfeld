(ns alethfeld.store-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.path :as path]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-store-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- test-mote
  "Create a minimal valid mote for testing."
  [& {:keys [id claim status priority difficulty]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3}}]
  (mote/make-mote id claim "test-agent"
                  :status status
                  :priority priority
                  :difficulty difficulty))

(defn- init-test-repo
  "Initialize a test repository in the temp directory."
  []
  (store/init-repo! *temp-dir*))

;; =============================================================================
;; Config Tests
;; =============================================================================

(deftest load-config-not-exists-test
  (testing "Returns nil when config doesn't exist"
    (is (nil? (store/load-config *temp-dir*)))))

(deftest save-config-test
  (testing "Saves config to .alethfeld/config.edn"
    (let [config {:project-name "Test" :version "1.0"}]
      (store/save-config! *temp-dir* config)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/config.edn"))))))

(deftest load-config-roundtrip-test
  (testing "Config survives save/load roundtrip"
    (let [config {:project-name "My Proof"
                  :version "0.1"
                  :default-difficulty 3
                  :vote-quorum 2}]
      (store/save-config! *temp-dir* config)
      (is (= config (store/load-config *temp-dir*))))))

;; =============================================================================
;; init-repo! Tests
;; =============================================================================

(deftest init-repo-creates-structure-test
  (testing "Creates directory structure"
    (store/init-repo! *temp-dir*)
    (is (fs/directory? (str *temp-dir* "/.alethfeld")))
    (is (fs/directory? (str *temp-dir* "/.alethfeld/motes")))
    (is (fs/directory? (str *temp-dir* "/.alethfeld/proposed")))
    (is (fs/directory? (str *temp-dir* "/.alethfeld/archive")))))

(deftest init-repo-creates-config-test
  (testing "Creates config.edn with defaults"
    (let [config (store/init-repo! *temp-dir*)]
      (is (= "Unnamed Proof" (:project-name config)))
      (is (= "0.1" (:version config)))
      (is (= 3 (:default-difficulty config))))))

(deftest init-repo-custom-name-test
  (testing "Accepts custom project name"
    (let [config (store/init-repo! *temp-dir* :project-name "My Theorem")]
      (is (= "My Theorem" (:project-name config))))))

(deftest init-repo-custom-config-test
  (testing "Accepts full custom config"
    (let [custom {:project-name "Custom" :vote-quorum 5}
          config (store/init-repo! *temp-dir* :config custom)]
      (is (= "Custom" (:project-name config)))
      (is (= 5 (:vote-quorum config))))))

(deftest repo-exists-test
  (testing "repo-exists? returns false before init"
    (is (false? (store/repo-exists? *temp-dir*))))

  (testing "repo-exists? returns true after init"
    (store/init-repo! *temp-dir*)
    (is (true? (store/repo-exists? *temp-dir*)))))

;; =============================================================================
;; save-mote! Tests
;; =============================================================================

(deftest save-mote-fixed-test
  (testing "Saves fixed mote to motes/"
    (init-test-repo)
    (let [m (test-mote :id "1" :status :fixed)]
      (store/save-mote! *temp-dir* m)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/motes/1.edn"))))))

(deftest save-mote-proposed-test
  (testing "Saves proposed mote to proposed/"
    (init-test-repo)
    (let [m (test-mote :id "2.1" :status :proposed)]
      (store/save-mote! *temp-dir* m)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/proposed/2.1.edn"))))))

(deftest save-mote-rejected-test
  (testing "Saves rejected mote to archive/"
    (init-test-repo)
    (let [m (test-mote :id "1.2" :status :rejected)]
      (store/save-mote! *temp-dir* m)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/archive/1/1.2.edn"))))))

(deftest save-mote-nested-test
  (testing "Saves nested mote with proper directory structure"
    (init-test-repo)
    (let [m (test-mote :id "1.2.3" :status :fixed)]
      (store/save-mote! *temp-dir* m)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/motes/1/1.2/1.2.3.edn"))))))

;; =============================================================================
;; load-mote Tests
;; =============================================================================

(deftest load-mote-not-found-test
  (testing "Returns nil when mote doesn't exist"
    (init-test-repo)
    (is (nil? (store/load-mote *temp-dir* "nonexistent")))))

(deftest load-mote-fixed-test
  (testing "Loads mote from motes/"
    (init-test-repo)
    (let [m (test-mote :id "1" :claim "Root claim")]
      (store/save-mote! *temp-dir* m)
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= "1" (:id loaded)))
        (is (= "Root claim" (:claim loaded)))))))

(deftest load-mote-proposed-test
  (testing "Loads mote from proposed/"
    (init-test-repo)
    (let [m (test-mote :id "2.1" :status :proposed)]
      (store/save-mote! *temp-dir* m)
      (let [loaded (store/load-mote *temp-dir* "2.1")]
        (is (= "2.1" (:id loaded)))
        (is (= :proposed (:status loaded)))))))

(deftest load-mote-rejected-test
  (testing "Loads mote from archive/"
    (init-test-repo)
    (let [m (test-mote :id "1.2" :status :rejected)]
      (store/save-mote! *temp-dir* m)
      (let [loaded (store/load-mote *temp-dir* "1.2")]
        (is (= "1.2" (:id loaded)))
        (is (= :rejected (:status loaded)))))))

(deftest load-mote-roundtrip-test
  (testing "Mote survives save/load roundtrip"
    (init-test-repo)
    (let [m (test-mote :id "1.2.3"
                       :claim "For all ε > 0"
                       :status :fixed
                       :priority :p1
                       :difficulty 4)]
      (store/save-mote! *temp-dir* m)
      (let [loaded (store/load-mote *temp-dir* "1.2.3")]
        (is (= (:id m) (:id loaded)))
        (is (= (:claim m) (:claim loaded)))
        (is (= (:status m) (:status loaded)))
        (is (= (:priority m) (:priority loaded)))
        (is (= (:difficulty m) (:difficulty loaded)))))))

;; =============================================================================
;; delete-mote! Tests
;; =============================================================================

(deftest delete-mote-not-found-test
  (testing "Returns false when mote doesn't exist"
    (init-test-repo)
    (is (false? (store/delete-mote! *temp-dir* "nonexistent")))))

(deftest delete-mote-fixed-test
  (testing "Deletes mote from motes/"
    (init-test-repo)
    (let [m (test-mote :id "1" :status :fixed)]
      (store/save-mote! *temp-dir* m)
      (is (true? (store/delete-mote! *temp-dir* "1")))
      (is (nil? (store/load-mote *temp-dir* "1"))))))

(deftest delete-mote-proposed-test
  (testing "Deletes mote from proposed/"
    (init-test-repo)
    (let [m (test-mote :id "2.1" :status :proposed)]
      (store/save-mote! *temp-dir* m)
      (is (true? (store/delete-mote! *temp-dir* "2.1")))
      (is (nil? (store/load-mote *temp-dir* "2.1"))))))

(deftest delete-mote-rejected-test
  (testing "Deletes mote from archive/"
    (init-test-repo)
    (let [m (test-mote :id "1.2" :status :rejected)]
      (store/save-mote! *temp-dir* m)
      (is (true? (store/delete-mote! *temp-dir* "1.2")))
      (is (nil? (store/load-mote *temp-dir* "1.2"))))))

;; =============================================================================
;; move-mote! Tests
;; =============================================================================

(deftest move-mote-not-found-test
  (testing "Returns nil when mote doesn't exist"
    (init-test-repo)
    (is (nil? (store/move-mote! *temp-dir* "nonexistent" :rejected)))))

(deftest move-mote-fixed-to-proposed-test
  (testing "Moves mote from motes/ to proposed/"
    (init-test-repo)
    (let [m (test-mote :id "1" :status :fixed)]
      (store/save-mote! *temp-dir* m)
      (store/move-mote! *temp-dir* "1" :proposed)
      ;; Should be in proposed now
      (is (fs/exists? (str *temp-dir* "/.alethfeld/proposed/1.edn")))
      ;; Should not be in motes
      (is (not (fs/exists? (str *temp-dir* "/.alethfeld/motes/1.edn"))))
      ;; Should load with new status
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= :proposed (:status loaded)))))))

(deftest move-mote-proposed-to-rejected-test
  (testing "Moves mote from proposed/ to archive/"
    (init-test-repo)
    (let [m (test-mote :id "2.1" :status :proposed)]
      (store/save-mote! *temp-dir* m)
      (store/move-mote! *temp-dir* "2.1" :rejected)
      ;; Should be in archive now
      (is (fs/exists? (str *temp-dir* "/.alethfeld/archive/2/2.1.edn")))
      ;; Should not be in proposed
      (is (not (fs/exists? (str *temp-dir* "/.alethfeld/proposed/2.1.edn"))))
      ;; Status should be updated
      (let [loaded (store/load-mote *temp-dir* "2.1")]
        (is (= :rejected (:status loaded)))))))

(deftest move-mote-proposed-to-fixed-test
  (testing "Moves mote from proposed/ to motes/ (approved)"
    (init-test-repo)
    (let [m (test-mote :id "1.2" :status :proposed)]
      (store/save-mote! *temp-dir* m)
      (store/move-mote! *temp-dir* "1.2" :fixed)
      ;; Should be in motes now
      (is (fs/exists? (str *temp-dir* "/.alethfeld/motes/1/1.2.edn")))
      ;; Should not be in proposed
      (is (not (fs/exists? (str *temp-dir* "/.alethfeld/proposed/1.2.edn"))))
      ;; Status should be updated
      (let [loaded (store/load-mote *temp-dir* "1.2")]
        (is (= :fixed (:status loaded)))))))

;; =============================================================================
;; load-all-motes Tests
;; =============================================================================

(deftest load-all-motes-empty-test
  (testing "Returns empty map when no motes"
    (init-test-repo)
    (is (= {} (store/load-all-motes *temp-dir*)))))

(deftest load-all-motes-single-test
  (testing "Loads single mote"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 1 (count motes)))
      (is (contains? motes "1")))))

(deftest load-all-motes-multiple-test
  (testing "Loads multiple motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (store/save-mote! *temp-dir* (test-mote :id "1.1"))
    (store/save-mote! *temp-dir* (test-mote :id "1.2"))
    (store/save-mote! *temp-dir* (test-mote :id "2"))
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 4 (count motes)))
      (is (every? #(contains? motes %) ["1" "1.1" "1.2" "2"])))))

(deftest load-all-motes-nested-test
  (testing "Loads deeply nested motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (store/save-mote! *temp-dir* (test-mote :id "1.2"))
    (store/save-mote! *temp-dir* (test-mote :id "1.2.3"))
    (store/save-mote! *temp-dir* (test-mote :id "1.2.3.4"))
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 4 (count motes)))
      (is (every? #(contains? motes %) ["1" "1.2" "1.2.3" "1.2.3.4"])))))

(deftest load-all-motes-includes-proposed-test
  (testing "Includes proposed motes by default"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :proposed))
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 2 (count motes)))
      (is (= :fixed (:status (get motes "1"))))
      (is (= :proposed (:status (get motes "2")))))))

(deftest load-all-motes-excludes-archived-test
  (testing "Excludes archived motes by default"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :rejected))
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 1 (count motes)))
      (is (contains? motes "1"))
      (is (not (contains? motes "2"))))))

(deftest load-all-motes-include-archived-test
  (testing "Can include archived motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :rejected))
    (let [motes (store/load-all-motes *temp-dir* :include-archived true)]
      (is (= 2 (count motes)))
      (is (contains? motes "1"))
      (is (contains? motes "2")))))

(deftest load-all-motes-exclude-proposed-test
  (testing "Can exclude proposed motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :proposed))
    (let [motes (store/load-all-motes *temp-dir* :include-proposed false)]
      (is (= 1 (count motes)))
      (is (contains? motes "1"))
      (is (not (contains? motes "2"))))))

;; =============================================================================
;; validate-mote Tests
;; =============================================================================

(deftest validate-mote-valid-test
  (testing "Returns nil for valid mote"
    (let [m (test-mote)]
      (is (nil? (store/validate-mote m))))))

(deftest validate-mote-invalid-test
  (testing "Returns explanation for invalid mote"
    (let [invalid {:id "1" :claim "test"}]  ; missing required fields
      (is (some? (store/validate-mote invalid))))))
