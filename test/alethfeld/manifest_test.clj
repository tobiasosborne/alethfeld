(ns alethfeld.manifest-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.manifest :as manifest]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-manifest-test-"})]
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
  [& {:keys [id claim status priority difficulty taint]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3
           taint #{:needs-verification}}}]
  (mote/make-mote id claim "test-agent"
                  :status status
                  :priority priority
                  :difficulty difficulty
                  :taint taint))

(defn- init-test-repo
  "Initialize a test repository in the temp directory."
  []
  (store/init-repo! *temp-dir*))

;; =============================================================================
;; manifest-path Tests
;; =============================================================================

(deftest manifest-path-test
  (testing "Returns correct path"
    (is (= ".alethfeld/manifest.edn" (manifest/manifest-path)))))

;; =============================================================================
;; mote->summary Tests
;; =============================================================================

(deftest mote-to-summary-basic-test
  (testing "Extracts correct fields from mote"
    (let [m (test-mote :id "1"
                       :status :fixed
                       :priority :p1
                       :difficulty 4
                       :taint #{:needs-verification :needs-decomposition})
          summary (manifest/mote->summary m)]
      (is (= :fixed (:status summary)))
      (is (= :p1 (:priority summary)))
      (is (= 4 (:difficulty summary)))
      (is (= #{:needs-verification :needs-decomposition} (:taint summary)))
      (is (= [] (:children summary)))
      (is (inst? (:updated-at summary))))))

(deftest mote-to-summary-excludes-extra-fields-test
  (testing "Does not include non-indexed fields"
    (let [m (test-mote :id "1" :claim "A complex claim")
          summary (manifest/mote->summary m)]
      ;; Should not include claim, votes, assumptions, etc.
      (is (not (contains? summary :id)))
      (is (not (contains? summary :claim)))
      (is (not (contains? summary :votes)))
      (is (not (contains? summary :assumptions)))
      (is (not (contains? summary :created-by))))))

;; =============================================================================
;; create-manifest Tests
;; =============================================================================

(deftest create-manifest-empty-test
  (testing "Creates manifest from empty mote map"
    (let [m (manifest/create-manifest {})]
      (is (= 1 (:version m)))
      (is (inst? (:updated-at m)))
      (is (= {} (:motes-by-id m)))
      (is (= {} (:motes-by-status m)))
      (is (= {} (:motes-by-priority m)))
      (is (= {} (:motes-by-taint m))))))

(deftest create-manifest-single-mote-test
  (testing "Creates manifest from single mote"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p2 :taint #{:needs-verification})
          m (manifest/create-manifest {"1" mote1})]
      ;; Check motes-by-id
      (is (= 1 (count (:motes-by-id m))))
      (is (= :fixed (get-in m [:motes-by-id "1" :status])))
      ;; Check motes-by-status
      (is (= #{"1"} (get-in m [:motes-by-status :fixed])))
      ;; Check motes-by-priority
      (is (= #{"1"} (get-in m [:motes-by-priority :p2])))
      ;; Check motes-by-taint
      (is (= #{"1"} (get-in m [:motes-by-taint :needs-verification]))))))

(deftest create-manifest-multiple-motes-test
  (testing "Creates manifest with multiple motes"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p0 :taint #{:needs-verification})
          mote2 (test-mote :id "1.1" :status :proposed :priority :p2 :taint #{:needs-verification})
          mote3 (test-mote :id "2" :status :fixed :priority :p0 :taint #{:needs-decomposition})
          m (manifest/create-manifest {"1" mote1 "1.1" mote2 "2" mote3})]
      ;; motes-by-id
      (is (= 3 (count (:motes-by-id m))))
      ;; motes-by-status: 2 fixed, 1 proposed
      (is (= #{"1" "2"} (get-in m [:motes-by-status :fixed])))
      (is (= #{"1.1"} (get-in m [:motes-by-status :proposed])))
      ;; motes-by-priority: 2 p0, 1 p2
      (is (= #{"1" "2"} (get-in m [:motes-by-priority :p0])))
      (is (= #{"1.1"} (get-in m [:motes-by-priority :p2])))
      ;; motes-by-taint
      (is (= #{"1" "1.1"} (get-in m [:motes-by-taint :needs-verification])))
      (is (= #{"2"} (get-in m [:motes-by-taint :needs-decomposition]))))))

(deftest create-manifest-multiple-taints-test
  (testing "Mote with multiple taints appears in each taint index"
    (let [mote1 (test-mote :id "1" :taint #{:needs-verification :needs-decomposition :needs-refs})
          m (manifest/create-manifest {"1" mote1})]
      (is (= #{"1"} (get-in m [:motes-by-taint :needs-verification])))
      (is (= #{"1"} (get-in m [:motes-by-taint :needs-decomposition])))
      (is (= #{"1"} (get-in m [:motes-by-taint :needs-refs]))))))

;; =============================================================================
;; empty-manifest Tests
;; =============================================================================

(deftest empty-manifest-test
  (testing "Creates properly structured empty manifest"
    (let [m (manifest/empty-manifest)]
      (is (= 1 (:version m)))
      (is (inst? (:updated-at m)))
      (is (= {} (:motes-by-id m)))
      (is (= {} (:motes-by-status m)))
      (is (= {} (:motes-by-priority m)))
      (is (= {} (:motes-by-taint m))))))

;; =============================================================================
;; Persistence Tests
;; =============================================================================

(deftest save-manifest-creates-file-test
  (testing "save-manifest! creates manifest file"
    (init-test-repo)
    (let [m (manifest/empty-manifest)]
      (manifest/save-manifest! *temp-dir* m)
      (is (fs/exists? (str *temp-dir* "/.alethfeld/manifest.edn"))))))

(deftest load-manifest-not-exists-test
  (testing "load-manifest returns nil when file doesn't exist"
    (init-test-repo)
    (is (nil? (manifest/load-manifest *temp-dir*)))))

(deftest save-load-manifest-roundtrip-test
  (testing "Manifest survives save/load roundtrip"
    (init-test-repo)
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p1)
          mote2 (test-mote :id "2" :status :proposed :priority :p2)
          m (manifest/create-manifest {"1" mote1 "2" mote2})]
      (manifest/save-manifest! *temp-dir* m)
      (let [loaded (manifest/load-manifest *temp-dir*)]
        (is (= 1 (:version loaded)))
        (is (= 2 (count (:motes-by-id loaded))))
        (is (= #{"1"} (get-in loaded [:motes-by-status :fixed])))
        (is (= #{"2"} (get-in loaded [:motes-by-status :proposed])))))))

;; =============================================================================
;; rebuild-manifest! Tests
;; =============================================================================

(deftest rebuild-manifest-empty-repo-test
  (testing "Rebuilds manifest for empty repo"
    (init-test-repo)
    (let [m (manifest/rebuild-manifest! *temp-dir*)]
      (is (= 0 (count (:motes-by-id m))))
      (is (fs/exists? (str *temp-dir* "/.alethfeld/manifest.edn"))))))

(deftest rebuild-manifest-with-motes-test
  (testing "Rebuilds manifest from existing motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed :priority :p0))
    (store/save-mote! *temp-dir* (test-mote :id "1.1" :status :fixed :priority :p1))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :proposed :priority :p2))
    (let [m (manifest/rebuild-manifest! *temp-dir*)]
      (is (= 3 (count (:motes-by-id m))))
      (is (= #{"1" "1.1"} (get-in m [:motes-by-status :fixed])))
      (is (= #{"2"} (get-in m [:motes-by-status :proposed])))
      (is (= #{"1"} (get-in m [:motes-by-priority :p0])))
      (is (= #{"1.1"} (get-in m [:motes-by-priority :p1])))
      (is (= #{"2"} (get-in m [:motes-by-priority :p2]))))))

(deftest rebuild-manifest-excludes-archived-by-default-test
  (testing "Rebuild excludes archived motes by default"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :rejected))
    (let [m (manifest/rebuild-manifest! *temp-dir*)]
      (is (= 1 (count (:motes-by-id m))))
      (is (contains? (:motes-by-id m) "1"))
      (is (not (contains? (:motes-by-id m) "2"))))))

(deftest rebuild-manifest-include-archived-test
  (testing "Rebuild can include archived motes"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1" :status :fixed))
    (store/save-mote! *temp-dir* (test-mote :id "2" :status :rejected))
    (let [m (manifest/rebuild-manifest! *temp-dir* :include-archived true)]
      (is (= 2 (count (:motes-by-id m))))
      (is (contains? (:motes-by-id m) "1"))
      (is (contains? (:motes-by-id m) "2")))))

;; =============================================================================
;; update-manifest-entry Tests (Pure Function)
;; =============================================================================

(deftest update-manifest-entry-add-new-test
  (testing "Adding new mote to empty manifest"
    (let [m (manifest/empty-manifest)
          mote1 (test-mote :id "1" :status :fixed :priority :p2 :taint #{:needs-verification})
          updated (manifest/update-manifest-entry m "1" mote1)]
      (is (= 1 (count (:motes-by-id updated))))
      (is (= #{"1"} (get-in updated [:motes-by-status :fixed])))
      (is (= #{"1"} (get-in updated [:motes-by-priority :p2])))
      (is (= #{"1"} (get-in updated [:motes-by-taint :needs-verification]))))))

(deftest update-manifest-entry-update-existing-test
  (testing "Updating existing mote changes indices"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p2 :taint #{:needs-verification})
          m (manifest/create-manifest {"1" mote1})
          ;; Update to proposed with different priority
          mote1-updated (test-mote :id "1" :status :proposed :priority :p0 :taint #{:needs-decomposition})
          updated (manifest/update-manifest-entry m "1" mote1-updated)]
      ;; Old entries removed
      (is (nil? (get-in updated [:motes-by-status :fixed])))
      (is (nil? (get-in updated [:motes-by-priority :p2])))
      (is (nil? (get-in updated [:motes-by-taint :needs-verification])))
      ;; New entries added
      (is (= #{"1"} (get-in updated [:motes-by-status :proposed])))
      (is (= #{"1"} (get-in updated [:motes-by-priority :p0])))
      (is (= #{"1"} (get-in updated [:motes-by-taint :needs-decomposition]))))))

(deftest update-manifest-entry-remove-test
  (testing "Removing mote (nil) cleans up indices"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p2 :taint #{:needs-verification})
          m (manifest/create-manifest {"1" mote1})
          updated (manifest/update-manifest-entry m "1" nil)]
      (is (= 0 (count (:motes-by-id updated))))
      (is (nil? (get-in updated [:motes-by-status :fixed])))
      (is (nil? (get-in updated [:motes-by-priority :p2])))
      (is (nil? (get-in updated [:motes-by-taint :needs-verification]))))))

(deftest update-manifest-entry-no-change-test
  (testing "No change when both old and new are nil"
    (let [m (manifest/empty-manifest)
          updated (manifest/update-manifest-entry m "nonexistent" nil)]
      (is (= m updated)))))

(deftest update-manifest-entry-preserves-others-test
  (testing "Updating one mote preserves others"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p2 :taint #{:needs-verification})
          mote2 (test-mote :id "2" :status :fixed :priority :p2 :taint #{:needs-verification})
          m (manifest/create-manifest {"1" mote1 "2" mote2})
          mote1-updated (test-mote :id "1" :status :proposed :priority :p0 :taint #{})
          updated (manifest/update-manifest-entry m "1" mote1-updated)]
      ;; Mote 2 still present
      (is (contains? (:motes-by-id updated) "2"))
      ;; Mote 2 still in indices
      (is (contains? (get-in updated [:motes-by-status :fixed]) "2"))
      (is (contains? (get-in updated [:motes-by-priority :p2]) "2"))
      ;; Mote 1 moved
      (is (contains? (get-in updated [:motes-by-status :proposed]) "1")))))

;; =============================================================================
;; update-manifest! Tests (Persisted)
;; =============================================================================

(deftest update-manifest-persisted-test
  (testing "update-manifest! persists changes"
    (init-test-repo)
    (let [mote1 (test-mote :id "1" :status :fixed)]
      (manifest/update-manifest! *temp-dir* "1" mote1)
      (let [loaded (manifest/load-manifest *temp-dir*)]
        (is (= 1 (count (:motes-by-id loaded))))
        (is (contains? (:motes-by-id loaded) "1"))))))

(deftest update-manifest-creates-if-missing-test
  (testing "update-manifest! creates manifest if missing"
    (init-test-repo)
    ;; No manifest exists yet
    (is (nil? (manifest/load-manifest *temp-dir*)))
    (let [mote1 (test-mote :id "1")]
      (manifest/update-manifest! *temp-dir* "1" mote1)
      (let [loaded (manifest/load-manifest *temp-dir*)]
        (is (some? loaded))
        (is (= 1 (count (:motes-by-id loaded))))))))

;; =============================================================================
;; Query Function Tests
;; =============================================================================

(deftest motes-by-status-test
  (testing "Returns mote IDs by status"
    (let [mote1 (test-mote :id "1" :status :fixed)
          mote2 (test-mote :id "2" :status :fixed)
          mote3 (test-mote :id "3" :status :proposed)
          m (manifest/create-manifest {"1" mote1 "2" mote2 "3" mote3})]
      (is (= #{"1" "2"} (manifest/motes-by-status m :fixed)))
      (is (= #{"3"} (manifest/motes-by-status m :proposed)))
      (is (= #{} (manifest/motes-by-status m :verified))))))

(deftest motes-by-priority-test
  (testing "Returns mote IDs by priority"
    (let [mote1 (test-mote :id "1" :priority :p0)
          mote2 (test-mote :id "2" :priority :p2)
          mote3 (test-mote :id "3" :priority :p2)
          m (manifest/create-manifest {"1" mote1 "2" mote2 "3" mote3})]
      (is (= #{"1"} (manifest/motes-by-priority m :p0)))
      (is (= #{"2" "3"} (manifest/motes-by-priority m :p2)))
      (is (= #{} (manifest/motes-by-priority m :p4))))))

(deftest motes-by-taint-test
  (testing "Returns mote IDs by taint"
    (let [mote1 (test-mote :id "1" :taint #{:needs-verification :needs-refs})
          mote2 (test-mote :id "2" :taint #{:needs-verification})
          mote3 (test-mote :id "3" :taint #{:needs-decomposition})
          m (manifest/create-manifest {"1" mote1 "2" mote2 "3" mote3})]
      (is (= #{"1" "2"} (manifest/motes-by-taint m :needs-verification)))
      (is (= #{"1"} (manifest/motes-by-taint m :needs-refs)))
      (is (= #{"3"} (manifest/motes-by-taint m :needs-decomposition)))
      (is (= #{} (manifest/motes-by-taint m :needs-counterexample))))))

(deftest mote-summary-test
  (testing "Returns summary for specific mote"
    (let [mote1 (test-mote :id "1" :status :fixed :priority :p1 :difficulty 4)
          m (manifest/create-manifest {"1" mote1})
          summary (manifest/mote-summary m "1")]
      (is (= :fixed (:status summary)))
      (is (= :p1 (:priority summary)))
      (is (= 4 (:difficulty summary)))))

  (testing "Returns nil for non-existent mote"
    (let [m (manifest/empty-manifest)]
      (is (nil? (manifest/mote-summary m "nonexistent"))))))

(deftest mote-ids-test
  (testing "Returns all mote IDs"
    (let [mote1 (test-mote :id "1")
          mote2 (test-mote :id "2")
          mote3 (test-mote :id "3")
          m (manifest/create-manifest {"1" mote1 "2" mote2 "3" mote3})]
      (is (= #{"1" "2" "3"} (manifest/mote-ids m)))))

  (testing "Returns empty set for empty manifest"
    (let [m (manifest/empty-manifest)]
      (is (= #{} (manifest/mote-ids m))))))

(deftest mote-count-test
  (testing "Returns correct count"
    (let [mote1 (test-mote :id "1")
          mote2 (test-mote :id "2")
          m (manifest/create-manifest {"1" mote1 "2" mote2})]
      (is (= 2 (manifest/mote-count m)))))

  (testing "Returns 0 for empty manifest"
    (let [m (manifest/empty-manifest)]
      (is (= 0 (manifest/mote-count m))))))

;; =============================================================================
;; manifest-stale? Tests
;; =============================================================================

(deftest manifest-stale-no-file-test
  (testing "Stale when manifest file doesn't exist"
    (init-test-repo)
    (is (true? (manifest/manifest-stale? *temp-dir*)))))

(deftest manifest-stale-after-rebuild-test
  (testing "Not stale immediately after rebuild"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (manifest/rebuild-manifest! *temp-dir*)
    ;; Small delay to ensure file system timestamps settle
    (Thread/sleep 10)
    (is (false? (manifest/manifest-stale? *temp-dir*)))))

(deftest manifest-stale-after-mote-change-test
  (testing "Stale when mote file is newer than manifest"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (manifest/rebuild-manifest! *temp-dir*)
    ;; Wait a bit to ensure different timestamps
    (Thread/sleep 50)
    ;; Modify a mote file
    (store/save-mote! *temp-dir* (test-mote :id "1" :claim "Modified claim"))
    (is (true? (manifest/manifest-stale? *temp-dir*)))))

(deftest manifest-stale-with-preloaded-test
  (testing "Uses pre-loaded manifest when provided"
    (init-test-repo)
    ;; Create manifest file
    (manifest/rebuild-manifest! *temp-dir*)
    ;; Provide a pre-loaded manifest
    (let [m (manifest/load-manifest *temp-dir*)]
      (is (false? (manifest/manifest-stale? *temp-dir* :manifest m))))))

;; =============================================================================
;; ensure-manifest! Tests
;; =============================================================================

(deftest ensure-manifest-creates-when-missing-test
  (testing "Creates manifest when missing"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (is (nil? (manifest/load-manifest *temp-dir*)))
    (let [m (manifest/ensure-manifest! *temp-dir*)]
      (is (some? m))
      (is (= 1 (manifest/mote-count m)))
      (is (fs/exists? (str *temp-dir* "/.alethfeld/manifest.edn"))))))

(deftest ensure-manifest-returns-existing-test
  (testing "Returns existing manifest when not stale"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (manifest/rebuild-manifest! *temp-dir*)
    (Thread/sleep 10)
    ;; Call ensure - should return existing
    (let [m (manifest/ensure-manifest! *temp-dir*)]
      (is (some? m))
      (is (= 1 (manifest/mote-count m))))))

(deftest ensure-manifest-rebuilds-when-stale-test
  (testing "Rebuilds when stale"
    (init-test-repo)
    (store/save-mote! *temp-dir* (test-mote :id "1"))
    (manifest/rebuild-manifest! *temp-dir*)
    ;; Wait and add another mote
    (Thread/sleep 50)
    (store/save-mote! *temp-dir* (test-mote :id "2"))
    ;; ensure should rebuild
    (let [m (manifest/ensure-manifest! *temp-dir*)]
      (is (= 2 (manifest/mote-count m))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest empty-taint-set-test
  (testing "Handles motes with empty taint set"
    (let [mote1 (test-mote :id "1" :taint #{})
          m (manifest/create-manifest {"1" mote1})]
      (is (= 1 (count (:motes-by-id m))))
      ;; Should not be in any taint index
      (is (= {} (:motes-by-taint m))))))

(deftest deeply-nested-mote-ids-test
  (testing "Handles deeply nested mote IDs"
    (let [mote1 (test-mote :id "1.2.3.4.5" :status :fixed)
          m (manifest/create-manifest {"1.2.3.4.5" mote1})]
      (is (contains? (:motes-by-id m) "1.2.3.4.5"))
      (is (contains? (get-in m [:motes-by-status :fixed]) "1.2.3.4.5")))))

(deftest concurrent-index-membership-test
  (testing "Mote appears in all relevant indices simultaneously"
    (let [mote1 (test-mote :id "1"
                          :status :proposed
                          :priority :p1
                          :taint #{:needs-verification :needs-proposal-review})
          m (manifest/create-manifest {"1" mote1})]
      ;; Should be in status index
      (is (contains? (manifest/motes-by-status m :proposed) "1"))
      ;; Should be in priority index
      (is (contains? (manifest/motes-by-priority m :p1) "1"))
      ;; Should be in both taint indices
      (is (contains? (manifest/motes-by-taint m :needs-verification) "1"))
      (is (contains? (manifest/motes-by-taint m :needs-proposal-review) "1")))))
