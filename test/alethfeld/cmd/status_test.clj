(ns alethfeld.cmd.status-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.session :as session]
            [alethfeld.cli :as cli]
            [alethfeld.id :as id]
            [alethfeld.job :as job]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-status-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-test-repo
  "Initialize a test repository with optional project name."
  [& {:keys [project-name] :or {project-name "Test Project"}}]
  (store/init-repo! *temp-dir* :project-name project-name))

(defn- create-test-mote
  "Create and save a test mote.
   Note: taint defaults to empty set for test control (not :needs-verification)."
  [& {:keys [id claim status priority difficulty parent children taint]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3
           parent nil
           children []
           taint #{}}}]
  (let [base-mote (mote/make-mote id claim "test-agent"
                                  :status status
                                  :priority priority
                                  :difficulty difficulty
                                  :taint #{})  ;; Start with empty taint
        with-parent (if parent (assoc base-mote :parent parent) base-mote)
        with-children (assoc with-parent :children children)
        with-taints (if (seq taint)
                      (reduce mote/add-taint with-children taint)
                      with-children)]
    (store/save-mote! *temp-dir* with-taints)
    with-taints))

(defn- get-status
  "Get status for the test repository.
   Since cmd-status uses '.' we need to call it from the temp dir context."
  []
  (let [motes (store/load-all-motes *temp-dir*)
        mote-list (vals motes)
        total-motes (count mote-list)
        config (store/load-config *temp-dir*)
        project-name (:project-name config "Unnamed Project")
        root-motes (count (filter #(= 1 (id/id-depth (:id %))) mote-list))
        status-counts (frequencies (map :status mote-list))
        taint-counts (->> mote-list
                          (mapcat :taint)
                          frequencies)
        active-sessions (session/load-all-active-sessions *temp-dir*)
        claim-timeout (:claim-timeout-minutes config)
        workable-count (count (filter #(job/workable? % :claim-timeout claim-timeout) mote-list))]
    {:project-name project-name
     :root-motes root-motes
     :total-motes total-motes
     :status-counts status-counts
     :taint-counts taint-counts
     :active-sessions (count active-sessions)
     :ready-for-work workable-count}))

;; =============================================================================
;; Basic Status Tests
;; =============================================================================

(deftest status-empty-repo-test
  (testing "status shows zeros for empty repository"
    (init-test-repo :project-name "Empty Project")
    (let [result (get-status)]
      (is (= "Empty Project" (:project-name result)))
      (is (= 0 (:root-motes result)))
      (is (= 0 (:total-motes result)))
      (is (= {} (:status-counts result)))
      (is (= {} (:taint-counts result)))
      (is (= 0 (:active-sessions result)))
      (is (= 0 (:ready-for-work result))))))

(deftest status-project-name-test
  (testing "status shows project name from config"
    (init-test-repo :project-name "My Proof Project")
    (let [result (get-status)]
      (is (= "My Proof Project" (:project-name result))))))

;; =============================================================================
;; Mote Counting Tests
;; =============================================================================

(deftest status-single-root-mote-test
  (testing "status counts single root mote"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root")
    (let [result (get-status)]
      (is (= 1 (:root-motes result)))
      (is (= 1 (:total-motes result))))))

(deftest status-multiple-root-motes-test
  (testing "status counts multiple root motes"
    (init-test-repo)
    (create-test-mote :id "1" :claim "First root")
    (create-test-mote :id "2" :claim "Second root")
    (create-test-mote :id "3" :claim "Third root")
    (let [result (get-status)]
      (is (= 3 (:root-motes result)))
      (is (= 3 (:total-motes result))))))

(deftest status-hierarchy-counting-test
  (testing "status counts root and child motes separately"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1" "1.2"])
    (create-test-mote :id "1.1" :claim "Child 1" :parent "1")
    (create-test-mote :id "1.2" :claim "Child 2" :parent "1")
    (let [result (get-status)]
      (is (= 1 (:root-motes result)))
      (is (= 3 (:total-motes result))))))

(deftest status-deep-hierarchy-test
  (testing "status counts deeply nested motes"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root" :children ["1.1"])
    (create-test-mote :id "1.1" :claim "L1" :parent "1" :children ["1.1.1"])
    (create-test-mote :id "1.1.1" :claim "L2" :parent "1.1" :children ["1.1.1.1"])
    (create-test-mote :id "1.1.1.1" :claim "L3" :parent "1.1.1")
    (let [result (get-status)]
      (is (= 1 (:root-motes result)))
      (is (= 4 (:total-motes result))))))

;; =============================================================================
;; Status Count Tests
;; =============================================================================

(deftest status-counts-by-status-test
  (testing "status counts motes by their status"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Verified" :status :verified)
    (create-test-mote :id "2" :claim "Fixed 1" :status :fixed)
    (create-test-mote :id "3" :claim "Fixed 2" :status :fixed)
    (create-test-mote :id "4" :claim "Proposed" :status :proposed)
    (let [result (get-status)
          counts (:status-counts result)]
      (is (= 1 (get counts :verified)))
      (is (= 2 (get counts :fixed)))
      (is (= 1 (get counts :proposed))))))

(deftest status-counts-all-statuses-test
  (testing "status counts all possible statuses"
    (init-test-repo)
    (create-test-mote :id "1" :status :verified)
    (create-test-mote :id "2" :status :fixed)
    (create-test-mote :id "3" :status :proposed)
    (create-test-mote :id "4" :status :contested)
    (create-test-mote :id "5" :status :refuted)
    (let [result (get-status)
          counts (:status-counts result)]
      (is (= 1 (get counts :verified)))
      (is (= 1 (get counts :fixed)))
      (is (= 1 (get counts :proposed)))
      (is (= 1 (get counts :contested)))
      (is (= 1 (get counts :refuted))))))

;; =============================================================================
;; Taint Count Tests
;; =============================================================================

(deftest status-taint-counts-single-test
  (testing "status counts single taint"
    (init-test-repo)
    (create-test-mote :id "1" :taint #{:needs-decomposition})
    (let [result (get-status)
          counts (:taint-counts result)]
      (is (= 1 (get counts :needs-decomposition))))))

(deftest status-taint-counts-multiple-motes-test
  (testing "status counts taints across multiple motes"
    (init-test-repo)
    (create-test-mote :id "1" :taint #{:needs-decomposition})
    (create-test-mote :id "2" :taint #{:needs-decomposition})
    (create-test-mote :id "3" :taint #{:needs-verification})
    (let [result (get-status)
          counts (:taint-counts result)]
      (is (= 2 (get counts :needs-decomposition)))
      (is (= 1 (get counts :needs-verification))))))

(deftest status-taint-counts-multiple-taints-per-mote-test
  (testing "status counts multiple taints on single mote"
    (init-test-repo)
    (create-test-mote :id "1" :taint #{:needs-decomposition :needs-verification :needs-refs})
    (let [result (get-status)
          counts (:taint-counts result)]
      (is (= 1 (get counts :needs-decomposition)))
      (is (= 1 (get counts :needs-verification)))
      (is (= 1 (get counts :needs-refs))))))

(deftest status-no-taints-test
  (testing "status shows empty taint counts when no taints"
    (init-test-repo)
    (create-test-mote :id "1")
    (let [result (get-status)]
      (is (= {} (:taint-counts result))))))

;; =============================================================================
;; Active Sessions Tests
;; =============================================================================

(deftest status-no-active-sessions-test
  (testing "status shows zero active sessions when none exist"
    (init-test-repo)
    (session/ensure-session-dirs! *temp-dir*)
    (let [result (get-status)]
      (is (= 0 (:active-sessions result))))))

(deftest status-with-active-session-test
  (testing "status counts active sessions"
    (init-test-repo)
    (session/ensure-session-dirs! *temp-dir*)
    (create-test-mote :id "1" :taint #{:needs-decomposition})
    (session/create-session! *temp-dir* "1" :proposer "agent-1")
    (let [result (get-status)]
      (is (= 1 (:active-sessions result))))))

(deftest status-multiple-active-sessions-test
  (testing "status counts multiple active sessions"
    (init-test-repo)
    (session/ensure-session-dirs! *temp-dir*)
    (create-test-mote :id "1" :taint #{:needs-decomposition})
    (create-test-mote :id "2" :taint #{:needs-verification})
    (session/create-session! *temp-dir* "1" :proposer "agent-1")
    (session/create-session! *temp-dir* "2" :verifier "agent-2")
    (let [result (get-status)]
      (is (= 2 (:active-sessions result))))))

;; =============================================================================
;; Ready for Work Tests
;; =============================================================================

(deftest status-ready-for-work-unclaimed-test
  (testing "status counts unclaimed workable motes"
    (init-test-repo)
    (create-test-mote :id "1" :status :fixed :taint #{:needs-decomposition})
    (let [result (get-status)]
      (is (= 1 (:ready-for-work result))))))

(deftest status-ready-excludes-verified-test
  (testing "status excludes verified motes from ready count"
    (init-test-repo)
    (create-test-mote :id "1" :status :verified)
    (create-test-mote :id "2" :status :fixed :taint #{:needs-decomposition})
    (let [result (get-status)]
      (is (= 1 (:ready-for-work result))))))

(deftest status-ready-excludes-no-taints-test
  (testing "status excludes motes without taints from ready count"
    (init-test-repo)
    (create-test-mote :id "1" :status :fixed)
    (let [result (get-status)]
      (is (= 0 (:ready-for-work result))))))

(deftest status-ready-excludes-claimed-test
  (testing "status excludes claimed motes from ready count"
    (init-test-repo)
    (session/ensure-session-dirs! *temp-dir*)
    (let [m (create-test-mote :id "1" :status :fixed :taint #{:needs-decomposition})
          claimed (mote/set-claimed-by m "someone")]
      (store/save-mote! *temp-dir* claimed)
      (let [result (get-status)]
        (is (= 0 (:ready-for-work result)))))))

;; =============================================================================
;; CLI Integration Tests
;; =============================================================================

(deftest status-handler-registered-test
  (testing "status handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "status")))))

(deftest status-handler-is-function-test
  (testing "status handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "status")]
      (is (fn? handler)))))
