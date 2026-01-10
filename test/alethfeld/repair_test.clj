(ns alethfeld.repair-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.repair :as repair]
            [alethfeld.store :as store]
            [alethfeld.session :as session]
            [alethfeld.io :as io]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-repair-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-repo
  "Initialize a repository with config."
  []
  (store/init-repo! *temp-dir* :project-name "Repair Test"))

(defn- create-mote
  "Create a minimal valid mote with required fields."
  [id & {:keys [parent children status assumptions depends-on]
         :or {status :fixed
              children []
              assumptions []}}]
  (let [now (java.util.Date.)]
    (cond-> {:id id
             :claim (str "Claim for " id)
             :status status
             :taint #{}
             :priority :p2
             :difficulty 3
             :children children
             :assumptions assumptions
             :definitions []
             :votes []
             :created-by "test-agent"
             :created-at now
             :updated-at now}
      parent (assoc :parent parent)
      depends-on (assoc :depends-on depends-on))))

(defn- save-mote!
  "Save a mote to the repository."
  [mote]
  (store/save-mote! *temp-dir* mote))

(defn- save-mote-raw!
  "Save a mote bypassing validation (for testing repair of invalid states)."
  [mote]
  (let [mote-id (:id mote)
        status (:status mote)
        path (str *temp-dir* "/.alethfeld/"
                  (case status
                    :proposed "proposed/"
                    :rejected "archive/"
                    "motes/")
                  mote-id ".edn")]
    (io/write-edn path mote)))

(defn- init-session-dirs
  "Initialize session directories in temp directory."
  []
  (session/ensure-session-dirs! *temp-dir*))

;; =============================================================================
;; find-orphaned-parents Tests
;; =============================================================================

(deftest find-orphaned-parents-no-orphans-test
  (testing "Returns empty vector when no orphaned parents exist"
    (let [motes {"1" (create-mote "1" :children ["1.1"])
                 "1.1" (create-mote "1.1" :parent "1")}]
      (is (= [] (repair/find-orphaned-parents motes)))))

  (testing "Returns empty vector for empty motes map"
    (is (= [] (repair/find-orphaned-parents {}))))

  (testing "Returns empty vector for motes without parent refs"
    (let [motes {"1" (create-mote "1")
                 "2" (create-mote "2")}]
      (is (= [] (repair/find-orphaned-parents motes))))))

(deftest find-orphaned-parents-single-orphan-test
  (testing "Detects single orphaned parent reference"
    (let [motes {"1.1" (create-mote "1.1" :parent "1")}  ; parent "1" doesn't exist
          result (repair/find-orphaned-parents motes)]
      (is (= 1 (count result)))
      (is (= "1.1" (:mote-id (first result))))
      (is (= "1" (:orphan-parent (first result)))))))

(deftest find-orphaned-parents-multiple-orphans-test
  (testing "Detects multiple orphaned parent references"
    (let [motes {"1.1" (create-mote "1.1" :parent "1")
                 "2.1" (create-mote "2.1" :parent "2")
                 "3" (create-mote "3")}  ; "3" is fine, no parent
          result (repair/find-orphaned-parents motes)]
      (is (= 2 (count result)))
      (is (some #(= "1.1" (:mote-id %)) result))
      (is (some #(= "2.1" (:mote-id %)) result)))))

(deftest find-orphaned-parents-nested-test
  (testing "Detects orphaned parent in nested structure"
    (let [motes {"1" (create-mote "1" :children ["1.1"])
                 "1.1" (create-mote "1.1" :parent "1" :children ["1.1.1"])
                 "1.1.1" (create-mote "1.1.1" :parent "1.1.2")}]  ; wrong parent
      (let [result (repair/find-orphaned-parents motes)]
        (is (= 1 (count result)))
        (is (= "1.1.1" (:mote-id (first result))))
        (is (= "1.1.2" (:orphan-parent (first result))))))))

;; =============================================================================
;; find-stale-sessions Tests
;; =============================================================================

(deftest find-stale-sessions-no-stale-test
  (testing "Returns empty vector when no stale sessions exist"
    (init-repo)
    (init-session-dirs)
    (let [mote (create-mote "1")
          _ (save-mote! mote)
          _ (session/create-session! *temp-dir* "1" :proposer "agent-1")
          motes (store/load-all-motes *temp-dir*)]
      (is (= [] (repair/find-stale-sessions *temp-dir* motes)))))

  (testing "Returns empty vector when no sessions exist"
    (init-repo)
    (init-session-dirs)
    (let [motes (store/load-all-motes *temp-dir*)]
      (is (= [] (repair/find-stale-sessions *temp-dir* motes))))))

(deftest find-stale-sessions-single-stale-test
  (testing "Detects session referencing non-existent mote"
    (init-repo)
    (init-session-dirs)
    ;; Create a session for a mote that doesn't exist (use valid mote ID format)
    (let [sess (session/create-session! *temp-dir* "999" :proposer "agent-1")
          motes {}  ; Empty motes map
          result (repair/find-stale-sessions *temp-dir* motes)]
      (is (= 1 (count result)))
      (is (= (:session-id sess) (:session-id (first result))))
      (is (= "999" (:mote-id (first result))))
      (is (= "agent-1" (:agent (first result)))))))

(deftest find-stale-sessions-mixed-test
  (testing "Correctly identifies stale vs valid sessions"
    (init-repo)
    (init-session-dirs)
    ;; Create mote "1"
    (save-mote! (create-mote "1"))
    ;; Create valid session for mote "1"
    (session/create-session! *temp-dir* "1" :proposer "agent-1")
    ;; Create stale session for missing mote (use valid format)
    (session/create-session! *temp-dir* "999" :advisor "agent-2")
    (let [motes (store/load-all-motes *temp-dir*)
          result (repair/find-stale-sessions *temp-dir* motes)]
      (is (= 1 (count result)))
      (is (= "999" (:mote-id (first result)))))))

;; =============================================================================
;; find-phantom-children Tests
;; =============================================================================

(deftest find-phantom-children-no-phantoms-test
  (testing "Returns empty vector when all children exist"
    (let [motes {"1" (create-mote "1" :children ["1.1"])
                 "1.1" (create-mote "1.1" :parent "1")}]
      (is (= [] (repair/find-phantom-children motes)))))

  (testing "Returns empty vector for empty motes map"
    (is (= [] (repair/find-phantom-children {}))))

  (testing "Returns empty vector for motes without children"
    (let [motes {"1" (create-mote "1")
                 "2" (create-mote "2")}]
      (is (= [] (repair/find-phantom-children motes))))))

(deftest find-phantom-children-single-phantom-test
  (testing "Detects single phantom child"
    (let [motes {"1" (create-mote "1" :children ["1.1"])}  ; child doesn't exist
          result (repair/find-phantom-children motes)]
      (is (= 1 (count result)))
      (is (= "1" (:parent-id (first result))))
      (is (= ["1.1"] (:phantom-children (first result)))))))

(deftest find-phantom-children-multiple-phantoms-test
  (testing "Detects multiple phantom children in same parent"
    (let [motes {"1" (create-mote "1" :children ["1.1" "1.2" "1.3"])}
          result (repair/find-phantom-children motes)]
      (is (= 1 (count result)))
      (is (= "1" (:parent-id (first result))))
      (is (= 3 (count (:phantom-children (first result)))))))

  (testing "Detects phantom children across multiple parents"
    (let [motes {"1" (create-mote "1" :children ["1.1"])
                 "2" (create-mote "2" :children ["2.1"])}
          result (repair/find-phantom-children motes)]
      (is (= 2 (count result)))
      (is (some #(= "1" (:parent-id %)) result))
      (is (some #(= "2" (:parent-id %)) result)))))

(deftest find-phantom-children-partial-phantoms-test
  (testing "Detects phantoms when some children exist"
    (let [motes {"1" (create-mote "1" :children ["1.1" "1.2"])
                 "1.1" (create-mote "1.1" :parent "1")}  ; 1.1 exists, 1.2 doesn't
          result (repair/find-phantom-children motes)]
      (is (= 1 (count result)))
      (is (= "1" (:parent-id (first result))))
      (is (= ["1.2"] (:phantom-children (first result)))))))

;; =============================================================================
;; detect-issues Tests
;; =============================================================================

(deftest detect-issues-no-issues-test
  (testing "Returns zero total issues for healthy graph"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1" :children ["1.1"]))
    (save-mote! (create-mote "1.1" :parent "1"))
    (let [result (repair/detect-issues *temp-dir*)]
      (is (= 0 (:total-issues result)))
      (is (= [] (:orphaned-parents result)))
      (is (= [] (:stale-sessions result)))
      (is (= [] (:phantom-children result)))
      (is (nil? (:broken-refs result)))
      (is (nil? (:cycle result))))))

(deftest detect-issues-orphaned-parents-test
  (testing "Detects orphaned parents"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1.1" :parent "1"))  ; orphaned - no parent "1"
    (let [result (repair/detect-issues *temp-dir*)]
      (is (pos? (:total-issues result)))
      (is (= 1 (count (:orphaned-parents result)))))))

(deftest detect-issues-stale-sessions-test
  (testing "Detects stale sessions"
    (init-repo)
    (init-session-dirs)
    (session/create-session! *temp-dir* "999" :proposer "agent")
    (let [result (repair/detect-issues *temp-dir*)]
      (is (pos? (:total-issues result)))
      (is (= 1 (count (:stale-sessions result)))))))

(deftest detect-issues-phantom-children-test
  (testing "Detects phantom children"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1" :children ["1.1"]))  ; phantom - no child "1.1"
    (let [result (repair/detect-issues *temp-dir*)]
      (is (pos? (:total-issues result)))
      (is (= 1 (count (:phantom-children result)))))))

(deftest detect-issues-broken-refs-test
  (testing "Detects broken internal references"
    (init-repo)
    (init-session-dirs)
    ;; Use raw save to bypass schema validation (testing repair of invalid state)
    (save-mote-raw! (create-mote "1" :assumptions [{:type :internal :ref "999"}]))
    (let [result (repair/detect-issues *temp-dir*)]
      (is (pos? (:total-issues result)))
      (is (some? (:broken-refs result))))))

(deftest detect-issues-multiple-issues-test
  (testing "Counts total of all issue types"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1" :children ["1.1"]))  ; phantom
    (save-mote! (create-mote "2.1" :parent "2"))      ; orphaned
    (session/create-session! *temp-dir* "999" :proposer "agent")  ; stale
    (let [result (repair/detect-issues *temp-dir*)]
      (is (>= (:total-issues result) 3)))))

;; =============================================================================
;; repair-orphaned-parent! Tests
;; =============================================================================

(deftest repair-orphaned-parent-success-test
  (testing "Removes orphaned parent reference"
    (init-repo)
    (save-mote! (create-mote "1.1" :parent "1"))  ; orphaned
    (let [repaired (repair/repair-orphaned-parent! *temp-dir* "1.1")]
      (is (some? repaired))
      (is (nil? (:parent repaired)))
      ;; Verify persisted
      (let [loaded (store/load-mote *temp-dir* "1.1")]
        (is (nil? (:parent loaded)))))))

(deftest repair-orphaned-parent-not-found-test
  (testing "Returns nil for non-existent mote"
    (init-repo)
    (is (nil? (repair/repair-orphaned-parent! *temp-dir* "missing")))))

;; =============================================================================
;; repair-stale-session! Tests
;; =============================================================================

(deftest repair-stale-session-success-test
  (testing "Archives stale session"
    (init-repo)
    (init-session-dirs)
    (let [sess (session/create-session! *temp-dir* "999" :proposer "agent")]
      (is (session/session-active? *temp-dir* (:session-id sess)))
      (is (true? (repair/repair-stale-session! *temp-dir* (:session-id sess))))
      ;; Session should now be archived (not active)
      (is (not (session/session-active? *temp-dir* (:session-id sess)))))))

(deftest repair-stale-session-not-found-test
  (testing "Returns nil for non-existent session"
    (init-repo)
    (init-session-dirs)
    (is (nil? (repair/repair-stale-session! *temp-dir* "nonexistent-session-id")))))

;; =============================================================================
;; repair-phantom-children! Tests
;; =============================================================================

(deftest repair-phantom-children-success-test
  (testing "Removes phantom children from parent"
    (init-repo)
    (save-mote! (create-mote "1" :children ["1.1" "1.2"]))  ; all phantoms
    (let [repaired (repair/repair-phantom-children! *temp-dir* "1")]
      (is (some? repaired))
      (is (= [] (:children repaired)))
      ;; Verify persisted
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= [] (:children loaded)))))))

(deftest repair-phantom-children-keeps-valid-test
  (testing "Keeps valid children, removes only phantoms"
    (init-repo)
    (save-mote! (create-mote "1" :children ["1.1" "1.2"]))
    (save-mote! (create-mote "1.1" :parent "1"))  ; 1.1 exists
    (let [repaired (repair/repair-phantom-children! *temp-dir* "1")]
      (is (= ["1.1"] (:children repaired))))))

(deftest repair-phantom-children-not-found-test
  (testing "Returns nil for non-existent parent"
    (init-repo)
    (is (nil? (repair/repair-phantom-children! *temp-dir* "missing")))))

;; =============================================================================
;; repair-broken-ref! Tests
;; =============================================================================

(deftest repair-broken-ref-assumptions-test
  (testing "Removes broken assumption reference"
    (init-repo)
    ;; Use raw save to create mote with broken ref (bypassing validation)
    (save-mote-raw! (create-mote "1" :assumptions [{:type :internal :ref "999"}
                                                   {:type :external :ref "valid-external"}]))
    (let [repaired (repair/repair-broken-ref! *temp-dir* "1" "999")]
      (is (some? repaired))
      ;; Internal ref removed, external kept
      (is (= 1 (count (:assumptions repaired))))
      (is (= :external (:type (first (:assumptions repaired))))))))

(deftest repair-broken-ref-depends-on-test
  (testing "Removes broken depends-on reference"
    (init-repo)
    ;; Use raw save for mote with broken ref
    (save-mote-raw! (create-mote "1" :depends-on [{:ref "999" :reason "test"}
                                                  {:ref "2" :reason "valid"}]))
    (save-mote! (create-mote "2"))  ; exists
    (let [repaired (repair/repair-broken-ref! *temp-dir* "1" "999")]
      (is (some? repaired))
      (is (= 1 (count (:depends-on repaired))))
      (is (= "2" (:ref (first (:depends-on repaired))))))))

(deftest repair-broken-ref-not-found-test
  (testing "Returns nil for non-existent mote"
    (init-repo)
    (is (nil? (repair/repair-broken-ref! *temp-dir* "missing" "ref")))))

;; =============================================================================
;; execute-repairs! Tests
;; =============================================================================

(deftest execute-repairs-orphaned-parents-test
  (testing "Repairs all orphaned parents"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1.1" :parent "1"))
    (save-mote! (create-mote "2.1" :parent "2"))
    (let [issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 2 (:repaired-orphans repairs)))
      ;; Verify both are fixed
      (is (nil? (:parent (store/load-mote *temp-dir* "1.1"))))
      (is (nil? (:parent (store/load-mote *temp-dir* "2.1")))))))

(deftest execute-repairs-stale-sessions-test
  (testing "Repairs all stale sessions"
    (init-repo)
    (init-session-dirs)
    (let [s1 (session/create-session! *temp-dir* "997" :proposer "agent1")
          s2 (session/create-session! *temp-dir* "998" :advisor "agent2")
          issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 2 (:repaired-sessions repairs)))
      ;; Verify both are archived
      (is (not (session/session-active? *temp-dir* (:session-id s1))))
      (is (not (session/session-active? *temp-dir* (:session-id s2)))))))

(deftest execute-repairs-phantom-children-test
  (testing "Repairs all phantom children"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1" :children ["1.1"]))
    (save-mote! (create-mote "2" :children ["2.1" "2.2"]))
    (let [issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 2 (:repaired-phantoms repairs)))
      ;; Verify both parents have empty children
      (is (= [] (:children (store/load-mote *temp-dir* "1"))))
      (is (= [] (:children (store/load-mote *temp-dir* "2")))))))

(deftest execute-repairs-broken-refs-test
  (testing "Repairs broken internal references"
    (init-repo)
    (init-session-dirs)
    ;; Use raw save to create mote with broken ref
    (save-mote-raw! (create-mote "1" :assumptions [{:type :internal :ref "999"}]))
    (let [issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 1 (:repaired-refs repairs)))
      ;; Verify assumption removed - load with :validate false since state was invalid
      (is (= [] (:assumptions (store/load-mote *temp-dir* "1" :validate false)))))))

(deftest execute-repairs-no-issues-test
  (testing "Returns zeros when no issues to repair"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1"))
    (let [issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 0 (:repaired-orphans repairs)))
      (is (= 0 (:repaired-sessions repairs)))
      (is (= 0 (:repaired-phantoms repairs)))
      (is (= 0 (:repaired-refs repairs)))
      (is (false? (:unrepaired-cycle repairs))))))

(deftest execute-repairs-mixed-issues-test
  (testing "Repairs multiple issue types in one call"
    (init-repo)
    (init-session-dirs)
    (save-mote! (create-mote "1" :children ["1.1"]))    ; phantom
    (save-mote! (create-mote "2.1" :parent "2"))        ; orphaned
    (session/create-session! *temp-dir* "999" :proposer "agent")  ; stale
    (let [issues (repair/detect-issues *temp-dir*)
          repairs (repair/execute-repairs! *temp-dir* issues)]
      (is (= 1 (:repaired-orphans repairs)))
      (is (= 1 (:repaired-sessions repairs)))
      (is (= 1 (:repaired-phantoms repairs))))))

;; =============================================================================
;; format-issues Tests
;; =============================================================================

(deftest format-issues-no-issues-test
  (testing "Returns 'No issues found.' for empty issues"
    (let [issues {:orphaned-parents []
                  :stale-sessions []
                  :phantom-children []
                  :broken-refs nil
                  :cycle nil
                  :total-issues 0}]
      (is (= "No issues found." (repair/format-issues issues))))))

(deftest format-issues-orphaned-parents-test
  (testing "Formats orphaned parents correctly"
    (let [issues {:orphaned-parents [{:mote-id "1.1" :orphan-parent "1"}]
                  :stale-sessions []
                  :phantom-children []
                  :broken-refs nil
                  :cycle nil}
          result (repair/format-issues issues)]
      (is (clojure.string/includes? result "Orphaned parent references"))
      (is (clojure.string/includes? result "1.1"))
      (is (clojure.string/includes? result "missing parent 1")))))

(deftest format-issues-stale-sessions-test
  (testing "Formats stale sessions correctly"
    (let [issues {:orphaned-parents []
                  :stale-sessions [{:session-id "sess-1" :mote-id "missing"}]
                  :phantom-children []
                  :broken-refs nil
                  :cycle nil}
          result (repair/format-issues issues)]
      (is (clojure.string/includes? result "Stale sessions"))
      (is (clojure.string/includes? result "sess-1"))
      (is (clojure.string/includes? result "missing mote missing")))))

(deftest format-issues-phantom-children-test
  (testing "Formats phantom children correctly"
    (let [issues {:orphaned-parents []
                  :stale-sessions []
                  :phantom-children [{:parent-id "1" :phantom-children ["1.1" "1.2"]}]
                  :broken-refs nil
                  :cycle nil}
          result (repair/format-issues issues)]
      (is (clojure.string/includes? result "Phantom children"))
      (is (clojure.string/includes? result "1 lists missing"))
      (is (clojure.string/includes? result "1.1")))))

(deftest format-issues-broken-refs-test
  (testing "Formats broken refs correctly"
    (let [issues {:orphaned-parents []
                  :stale-sessions []
                  :phantom-children []
                  :broken-refs [{:mote-id "1" :ref "missing" :ref-type :assumption}]
                  :cycle nil}
          result (repair/format-issues issues)]
      (is (clojure.string/includes? result "Broken references"))
      (is (clojure.string/includes? result "1")))))

(deftest format-issues-cycle-test
  (testing "Formats cycle correctly"
    (let [issues {:orphaned-parents []
                  :stale-sessions []
                  :phantom-children []
                  :broken-refs nil
                  :cycle ["1" "2" "3" "1"]}
          result (repair/format-issues issues)]
      (is (clojure.string/includes? result "cycle detected"))
      (is (clojure.string/includes? result "1"))
      (is (clojure.string/includes? result "2"))
      (is (clojure.string/includes? result "3")))))

;; =============================================================================
;; format-repairs Tests
;; =============================================================================

(deftest format-repairs-no-repairs-test
  (testing "Returns 'No repairs needed.' when nothing repaired"
    (let [repairs {:repaired-orphans 0
                   :repaired-sessions 0
                   :repaired-phantoms 0
                   :repaired-refs 0
                   :unrepaired-cycle false}]
      (is (= "No repairs needed." (repair/format-repairs repairs))))))

(deftest format-repairs-orphans-test
  (testing "Formats orphaned repairs correctly"
    (let [repairs {:repaired-orphans 2
                   :repaired-sessions 0
                   :repaired-phantoms 0
                   :repaired-refs 0
                   :unrepaired-cycle false}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "Fixed 2 orphaned parent references")))))

(deftest format-repairs-sessions-test
  (testing "Formats session repairs correctly"
    (let [repairs {:repaired-orphans 0
                   :repaired-sessions 3
                   :repaired-phantoms 0
                   :repaired-refs 0
                   :unrepaired-cycle false}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "Completed 3 stale sessions")))))

(deftest format-repairs-phantoms-test
  (testing "Formats phantom repairs correctly"
    (let [repairs {:repaired-orphans 0
                   :repaired-sessions 0
                   :repaired-phantoms 1
                   :repaired-refs 0
                   :unrepaired-cycle false}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "Fixed 1 phantom children references")))))

(deftest format-repairs-refs-test
  (testing "Formats ref repairs correctly"
    (let [repairs {:repaired-orphans 0
                   :repaired-sessions 0
                   :repaired-phantoms 0
                   :repaired-refs 4
                   :unrepaired-cycle false}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "Removed 4 broken references")))))

(deftest format-repairs-cycle-warning-test
  (testing "Includes cycle warning when cycle exists"
    (let [repairs {:repaired-orphans 1
                   :repaired-sessions 0
                   :repaired-phantoms 0
                   :repaired-refs 0
                   :unrepaired-cycle true}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "WARNING"))
      (is (clojure.string/includes? result "cycle"))
      (is (clojure.string/includes? result "manual")))))

(deftest format-repairs-mixed-test
  (testing "Formats multiple repair types correctly"
    (let [repairs {:repaired-orphans 2
                   :repaired-sessions 1
                   :repaired-phantoms 3
                   :repaired-refs 1
                   :unrepaired-cycle false}
          result (repair/format-repairs repairs)]
      (is (clojure.string/includes? result "orphaned"))
      (is (clojure.string/includes? result "stale sessions"))
      (is (clojure.string/includes? result "phantom"))
      (is (clojure.string/includes? result "broken references")))))
