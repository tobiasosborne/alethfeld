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

;; =============================================================================
;; Schema Validation on Load Tests
;; =============================================================================

(deftest load-mote-invalid-schema-test
  (testing "Returns nil when mote file has invalid schema"
    (init-test-repo)
    ;; Write invalid EDN directly to disk (bypassing save-mote)
    (let [invalid-mote {:id "1" :claim "test" :status :fixed}  ; missing required fields
          file-path (str *temp-dir* "/.alethfeld/motes/1.edn")]
      (spit file-path (pr-str invalid-mote))
      ;; load-mote should return nil for invalid motes
      (is (nil? (store/load-mote *temp-dir* "1"))))))

(deftest load-mote-missing-priority-test
  (testing "Returns nil when mote is missing priority field"
    (init-test-repo)
    ;; Write mote without priority - this would cause NPE in job-comparator
    (let [invalid-mote {:id "1"
                        :claim "Test claim"
                        :status :fixed
                        :difficulty 3
                        :taint #{}
                        :assumptions #{}
                        :children []
                        :created-at "2024-01-01T00:00:00"
                        :created-by "test"
                        :updated-at "2024-01-01T00:00:00"}
          file-path (str *temp-dir* "/.alethfeld/motes/1.edn")]
      (spit file-path (pr-str invalid-mote))
      ;; load-mote should return nil - missing :priority
      (is (nil? (store/load-mote *temp-dir* "1"))))))

(deftest load-all-motes-skips-invalid-test
  (testing "Skips invalid motes when loading all"
    (init-test-repo)
    ;; Save one valid mote
    (store/save-mote! *temp-dir* (test-mote :id "1" :claim "Valid mote"))
    ;; Write invalid mote directly to disk
    (let [invalid-mote {:id "2" :claim "Invalid" :status :fixed}
          file-path (str *temp-dir* "/.alethfeld/motes/2.edn")]
      (spit file-path (pr-str invalid-mote)))
    ;; load-all-motes should only return the valid mote
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 1 (count motes)))
      (is (contains? motes "1"))
      (is (not (contains? motes "2"))))))

(deftest load-all-motes-partial-invalid-test
  (testing "Loads valid motes even when some are invalid"
    (init-test-repo)
    ;; Save three valid motes
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (store/save-mote! *temp-dir* (test-mote :id "2"))
    (store/save-mote! *temp-dir* (test-mote :id "3"))
    ;; Corrupt one of them by overwriting with invalid data
    (let [invalid {:id "2" :bad "data"}
          file-path (str *temp-dir* "/.alethfeld/motes/2.edn")]
      (spit file-path (pr-str invalid)))
    ;; Should load 2 valid motes, skip the invalid one
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 2 (count motes)))
      (is (contains? motes "1"))
      (is (not (contains? motes "2")))
      (is (contains? motes "3")))))

;; =============================================================================
;; Skip Validation Tests (alethfeld-437q)
;; =============================================================================

(deftest load-mote-skip-validation-test
  (testing "Skips schema validation when :validate false"
    (init-test-repo)
    ;; Write invalid mote directly to disk
    (let [invalid-mote {:id "1" :claim "test" :status :fixed}  ; missing required fields
          file-path (str *temp-dir* "/.alethfeld/motes/1.edn")]
      (spit file-path (pr-str invalid-mote))
      ;; With validation (default) - returns nil
      (is (nil? (store/load-mote *temp-dir* "1")))
      ;; Without validation - returns the mote
      (is (= "1" (:id (store/load-mote *temp-dir* "1" :validate false)))))))

(deftest load-all-motes-skip-validation-test
  (testing "Skips schema validation when :validate false"
    (init-test-repo)
    ;; Save one valid mote
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    ;; Write invalid mote directly to disk
    (let [invalid-mote {:id "2" :claim "Invalid" :status :fixed}
          file-path (str *temp-dir* "/.alethfeld/motes/2.edn")]
      (spit file-path (pr-str invalid-mote)))
    ;; With validation (default) - only returns valid mote
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 1 (count motes)))
      (is (contains? motes "1")))
    ;; Without validation - returns both motes
    (let [motes (store/load-all-motes *temp-dir* :validate false)]
      (is (= 2 (count motes)))
      (is (contains? motes "1"))
      (is (contains? motes "2")))))

(deftest load-mote-validate-default-true-test
  (testing "Validation is enabled by default"
    (init-test-repo)
    (let [invalid {:id "1" :status :fixed}  ; missing required fields
          file-path (str *temp-dir* "/.alethfeld/motes/1.edn")]
      (spit file-path (pr-str invalid))
      ;; Default behavior should validate
      (is (nil? (store/load-mote *temp-dir* "1"))))))

;; =============================================================================
;; Caching Tests (alethfeld-ppdz)
;; =============================================================================

(deftest load-all-motes-no-cache-by-default-test
  (testing "No caching when *motes-cache* is not bound"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    ;; Without binding, cache should be nil
    (is (nil? store/*motes-cache*))
    ;; Should still work fine
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= 1 (count motes))))))

(deftest load-all-motes-with-cache-binding-test
  (testing "Caches results when *motes-cache* is bound"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (binding [store/*motes-cache* (atom nil)]
      ;; First call - should populate cache
      (let [motes1 (store/load-all-motes *temp-dir*)]
        (is (= 1 (count motes1)))
        ;; Cache should be populated
        (is (some? @store/*motes-cache*))
        (is (= 1 (count (:motes @store/*motes-cache*))))
        ;; Add another mote
        (store/save-mote! *temp-dir* (test-mote :id "2"))
        ;; Second call should return cached (stale) result
        (let [motes2 (store/load-all-motes *temp-dir*)]
          (is (= 1 (count motes2)))  ; Still 1 from cache
          (is (= motes1 motes2)))))))

(deftest load-all-motes-cache-invalidation-test
  (testing "Cache invalidates when options change"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :rejected))
    (binding [store/*motes-cache* (atom nil)]
      ;; First call without archived
      (let [motes1 (store/load-all-motes *temp-dir*)]
        (is (= 1 (count motes1)))
        ;; Second call with include-archived - should not use stale cache
        (let [motes2 (store/load-all-motes *temp-dir* :include-archived true)]
          (is (= 2 (count motes2))))))))

(deftest load-all-motes-use-cache-false-test
  (testing "Can bypass cache with :use-cache false"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (binding [store/*motes-cache* (atom nil)]
      ;; Populate cache
      (store/load-all-motes *temp-dir*)
      ;; Add another mote
      (store/save-mote! *temp-dir* (test-mote :id "2"))
      ;; With cache - returns stale result
      (is (= 1 (count (store/load-all-motes *temp-dir*))))
      ;; Bypass cache - returns fresh result
      (is (= 2 (count (store/load-all-motes *temp-dir* :use-cache false)))))))

(deftest with-motes-cache-macro-test
  (testing "with-motes-cache macro enables caching"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    ;; Outside macro - no caching
    (is (nil? store/*motes-cache*))
    ;; Inside macro - caching is enabled
    (store/with-motes-cache
      (is (some? store/*motes-cache*))
      (is (nil? @store/*motes-cache*))  ; Initially empty
      (store/load-all-motes *temp-dir*)
      (is (some? @store/*motes-cache*)))  ; Populated after call
    ;; After macro - back to nil
    (is (nil? store/*motes-cache*))))

(deftest with-motes-cache-multiple-calls-test
  (testing "Multiple calls within with-motes-cache share cache"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (let [call-count (atom 0)]
      ;; We can't directly track file reads, but we can verify cache behavior
      (store/with-motes-cache
        (let [motes1 (store/load-all-motes *temp-dir*)
              cache-after-first @store/*motes-cache*
              motes2 (store/load-all-motes *temp-dir*)
              cache-after-second @store/*motes-cache*]
          ;; Both calls return same result
          (is (= motes1 motes2))
          ;; Cache object should be same (not re-loaded)
          (is (identical? cache-after-first cache-after-second)))))))
