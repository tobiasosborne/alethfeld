(ns alethfeld.cmd.ready-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-ready-test-"})
        orig (System/getProperty "user.dir")]
    (try
      (System/setProperty "user.dir" (str temp))
      (binding [*temp-dir* (str temp)
                *original-dir* orig]
        (f))
      (finally
        (System/setProperty "user.dir" orig)
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-repo!
  "Initialize a test repository."
  []
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :project-name "Test Project")
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-mote!
  "Create a mote directly in the store for test setup."
  [id claim & {:keys [difficulty priority taint parent status]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}
                    status :fixed}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :difficulty difficulty
                          :priority priority
                          :taint taint
                          :status status
                          :parent parent)]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

(defn- create-mote-with-children!
  "Create a parent mote and add child IDs to it."
  [id claim children & opts]
  (let [m (apply create-mote! id claim opts)]
    (when (seq children)
      (let [updated (reduce mote/add-child m children)]
        (store/save-mote! *temp-dir* updated)
        (git/git-add-all! *temp-dir*)
        (git/git-commit! *temp-dir* (str "Add children to " id))
        updated))))

(defn- cmd-ready-in-temp
  "Call cmd-ready using the temp directory."
  [& {:keys [agent role difficulty priority max no-claim]
      :or {max 1}}]
  ;; Load motes from temp dir and use job selection
  (let [repo-path *temp-dir*]
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [motes (store/load-all-motes repo-path)
          difficulty-filter (when difficulty
                              (if (string? difficulty)
                                (@#'cmd/parse-difficulty-spec difficulty)
                                difficulty))
          priority-filter (when priority
                            (if (string? priority)
                              (@#'cmd/parse-priority-spec priority)
                              priority))
          jobs (alethfeld.job/select-jobs motes
                                          :role role
                                          :difficulty difficulty-filter
                                          :priority priority-filter
                                          :max max)
          jobs-with-prompts (mapv (fn [j]
                                    (let [resolved-children (@#'cmd/resolve-children (:mote j) motes)
                                          rendered-prompt (alethfeld.prompt/render-prompt j :resolved-children resolved-children)]
                                      (assoc j :prompt rendered-prompt)))
                                  jobs)]
      (if (and agent (not no-claim) (seq jobs-with-prompts))
        (let [claimed-jobs (mapv (fn [j]
                                   (let [updated-mote (mote/set-claimed-by (:mote j) agent)]
                                     (store/save-mote! repo-path updated-mote)
                                     (assoc j :mote updated-mote :claimed-by agent)))
                                 jobs-with-prompts)]
          (git/git-add-all! repo-path)
          (git/git-commit! repo-path (str "Claim jobs for " agent))
          claimed-jobs)
        jobs-with-prompts))))

;; =============================================================================
;; Basic Functionality Tests
;; =============================================================================

(deftest ready-returns-vector-test
  (testing "ready returns a vector"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp)]
      (is (vector? result)))))

(deftest ready-returns-jobs-test
  (testing "ready returns job maps"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp)]
      (is (= 1 (count result)))
      (is (map? (first result)))
      (is (contains? (first result) :job-id)))))

(deftest ready-job-has-mote-id-test
  (testing "ready job contains mote-id"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp)]
      (is (= "1" (:mote-id (first result)))))))

(deftest ready-job-has-role-test
  (testing "ready job contains role"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition})
    (let [result (cmd-ready-in-temp)]
      (is (= :proposer (:role (first result)))))))

(deftest ready-job-has-prompt-test
  (testing "ready job contains prompt"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition})
    (let [result (cmd-ready-in-temp)]
      (is (string? (:prompt (first result))))
      (is (str/includes? (:prompt (first result)) "PROPOSER")))))

(deftest ready-empty-when-no-workable-test
  (testing "ready returns empty when no workable motes"
    (init-repo!)
    ;; Create mote with no work-related taints
    (create-mote! "1" "Test claim" :taint #{})
    (let [result (cmd-ready-in-temp)]
      (is (empty? result)))))

(deftest ready-excludes-claimed-motes-test
  (testing "ready excludes already claimed motes"
    (init-repo!)
    (let [m (create-mote! "1" "Test claim")
          claimed (mote/set-claimed-by m "other-agent")]
      (store/save-mote! *temp-dir* claimed)
      (git/git-add-all! *temp-dir*)
      (git/git-commit! *temp-dir* "Claim mote"))
    (let [result (cmd-ready-in-temp)]
      (is (empty? result)))))

(deftest ready-excludes-verified-motes-test
  (testing "ready excludes verified motes"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :verified :taint #{:needs-decomposition})
    (let [result (cmd-ready-in-temp)]
      (is (empty? result)))))

;; =============================================================================
;; Max Jobs Tests
;; =============================================================================

(deftest ready-default-max-one-test
  (testing "ready returns max 1 job by default"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (create-mote! "3" "Third")
    (let [result (cmd-ready-in-temp)]
      (is (= 1 (count result))))))

(deftest ready-respects-max-test
  (testing "ready respects max parameter"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (create-mote! "3" "Third")
    (let [result (cmd-ready-in-temp :max 2)]
      (is (= 2 (count result))))))

(deftest ready-max-exceeds-available-test
  (testing "ready returns all available when max exceeds count"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (let [result (cmd-ready-in-temp :max 10)]
      (is (= 2 (count result))))))

;; =============================================================================
;; Max Jobs with Claiming Tests
;; =============================================================================

(deftest ready-max-with-claim-returns-multiple-jobs-test
  (testing "ready with --max and --name claims multiple jobs"
    (init-repo!)
    (create-mote! "1" "First" :priority :p1)
    (create-mote! "2" "Second" :priority :p2)
    (create-mote! "3" "Third" :priority :p3)
    (create-mote! "4" "Fourth" :priority :p4)
    (let [result (cmd-ready-in-temp :agent "batch-agent" :max 3)]
      ;; Should claim exactly 3 jobs
      (is (= 3 (count result)))
      ;; All should be claimed by the agent
      (is (every? #(= "batch-agent" (:claimed-by %)) result)))))

(deftest ready-max-with-claim-respects-priority-order-test
  (testing "ready with --max claims highest priority jobs first"
    (init-repo!)
    (create-mote! "1" "Low priority" :priority :p4)
    (create-mote! "2" "Critical" :priority :p0)
    (create-mote! "3" "Normal" :priority :p2)
    (create-mote! "4" "High" :priority :p1)
    (let [result (cmd-ready-in-temp :agent "batch-agent" :max 2)]
      ;; Should get the 2 highest priority jobs (p0, p1)
      (is (= 2 (count result)))
      (is (= :p0 (:priority (first result))))
      (is (= :p1 (:priority (second result)))))))

(deftest ready-max-with-claim-persists-all-claims-test
  (testing "ready with --max persists all claims to disk"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (create-mote! "3" "Third")
    (cmd-ready-in-temp :agent "batch-agent" :max 3)
    ;; Verify all motes are claimed in the store
    (let [m1 (store/load-mote *temp-dir* "1")
          m2 (store/load-mote *temp-dir* "2")
          m3 (store/load-mote *temp-dir* "3")]
      (is (= "batch-agent" (:claimed-by m1)))
      (is (= "batch-agent" (:claimed-by m2)))
      (is (= "batch-agent" (:claimed-by m3))))))

(deftest ready-max-with-claim-filters-by-role-test
  (testing "ready with --max and --role only claims jobs for that role"
    (init-repo!)
    (create-mote! "1" "Needs decomp" :taint #{:needs-decomposition})
    (create-mote! "2" "Needs verification" :taint #{:needs-verification})
    (create-mote! "3" "More decomp" :taint #{:needs-decomposition})
    (create-mote! "4" "More verification" :taint #{:needs-verification})
    (let [result (cmd-ready-in-temp :agent "batch-agent" :role :verifier :max 10)]
      ;; Should only get verifier jobs (motes 2 and 4)
      (is (= 2 (count result)))
      (is (every? #(= :verifier (:role %)) result)))))

(deftest ready-max-one-is-default-for-claiming-test
  (testing "ready defaults to max 1 when claiming (agent provided)"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (create-mote! "3" "Third")
    (let [result (cmd-ready-in-temp :agent "my-agent")]
      (is (= 1 (count result))))))

(deftest ready-max-with-no-claim-shows-multiple-test
  (testing "ready with --max and --no-claim shows multiple jobs without claiming"
    (init-repo!)
    (create-mote! "1" "First")
    (create-mote! "2" "Second")
    (create-mote! "3" "Third")
    (let [result (cmd-ready-in-temp :agent "batch-agent" :max 3 :no-claim true)]
      ;; Should return 3 jobs
      (is (= 3 (count result)))
      ;; None should be claimed
      (is (every? #(nil? (:claimed-by %)) result))
      ;; Verify not persisted
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "1"))))
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "2"))))
      (is (nil? (:claimed-by (store/load-mote *temp-dir* "3")))))))

;; =============================================================================
;; Role Filter Tests
;; =============================================================================

(deftest ready-filter-by-role-test
  (testing "ready filters by role"
    (init-repo!)
    (create-mote! "1" "Needs decomp" :taint #{:needs-decomposition})
    (create-mote! "2" "Needs verification" :taint #{:needs-verification})
    (let [result (cmd-ready-in-temp :role :verifier :max 10)]
      (is (= 1 (count result)))
      (is (= "2" (:mote-id (first result)))))))

(deftest ready-filter-proposer-test
  (testing "ready filters for proposer role"
    (init-repo!)
    (create-mote! "1" "Needs decomp" :taint #{:needs-decomposition})
    (create-mote! "2" "Needs refs" :taint #{:needs-refs})
    (let [result (cmd-ready-in-temp :role :proposer :max 10)]
      (is (= 1 (count result)))
      (is (= :proposer (:role (first result)))))))

(deftest ready-filter-advisor-test
  (testing "ready filters for advisor role"
    (init-repo!)
    (create-mote! "1" "Needs review" :taint #{:needs-proposal-review})
    (create-mote! "2" "Needs decomp" :taint #{:needs-decomposition})
    (let [result (cmd-ready-in-temp :role :advisor :max 10)]
      (is (= 1 (count result)))
      (is (= :advisor (:role (first result)))))))

;; =============================================================================
;; Difficulty Filter Tests
;; =============================================================================

(deftest ready-filter-exact-difficulty-test
  (testing "ready filters by exact difficulty"
    (init-repo!)
    (create-mote! "1" "Easy" :difficulty 1)
    (create-mote! "2" "Medium" :difficulty 3)
    (create-mote! "3" "Hard" :difficulty 5)
    (let [result (cmd-ready-in-temp :difficulty "3" :max 10)]
      (is (= 1 (count result)))
      (is (= 3 (:difficulty (first result)))))))

(deftest ready-filter-difficulty-range-test
  (testing "ready filters by difficulty range"
    (init-repo!)
    (create-mote! "1" "Very easy" :difficulty 1)
    (create-mote! "2" "Easy" :difficulty 2)
    (create-mote! "3" "Medium" :difficulty 3)
    (create-mote! "4" "Hard" :difficulty 4)
    (create-mote! "5" "Very hard" :difficulty 5)
    (let [result (cmd-ready-in-temp :difficulty "2-4" :max 10)]
      (is (= 3 (count result)))
      (is (every? #(<= 2 (:difficulty %) 4) result)))))

;; =============================================================================
;; Priority Filter Tests
;; =============================================================================

(deftest ready-filter-exact-priority-test
  (testing "ready filters by exact priority"
    (init-repo!)
    (create-mote! "1" "Critical" :priority :p0)
    (create-mote! "2" "Normal" :priority :p2)
    (create-mote! "3" "Low" :priority :p4)
    (let [result (cmd-ready-in-temp :priority "p2" :max 10)]
      (is (= 1 (count result)))
      (is (= :p2 (:priority (first result)))))))

(deftest ready-filter-priority-range-test
  (testing "ready filters by priority range"
    (init-repo!)
    (create-mote! "1" "Critical" :priority :p0)
    (create-mote! "2" "High" :priority :p1)
    (create-mote! "3" "Normal" :priority :p2)
    (create-mote! "4" "Low" :priority :p3)
    (create-mote! "5" "Backlog" :priority :p4)
    (let [result (cmd-ready-in-temp :priority "p1-p3" :max 10)
          priorities (set (map :priority result))]
      (is (= 3 (count result)))
      (is (contains? priorities :p1))
      (is (contains? priorities :p2))
      (is (contains? priorities :p3)))))

;; =============================================================================
;; Sorting Tests
;; =============================================================================

(deftest ready-sorts-by-priority-test
  (testing "ready sorts by priority (p0 first)"
    (init-repo!)
    (create-mote! "1" "Low" :priority :p4)
    (create-mote! "2" "High" :priority :p0)
    (create-mote! "3" "Normal" :priority :p2)
    (let [result (cmd-ready-in-temp :max 10)]
      (is (= :p0 (:priority (first result))))
      (is (= :p4 (:priority (last result)))))))

(deftest ready-sorts-by-difficulty-secondary-test
  (testing "ready sorts by difficulty when priority is equal"
    (init-repo!)
    (create-mote! "1" "Hard p2" :priority :p2 :difficulty 5)
    (create-mote! "2" "Easy p2" :priority :p2 :difficulty 1)
    (create-mote! "3" "Med p2" :priority :p2 :difficulty 3)
    (let [result (cmd-ready-in-temp :max 10)]
      (is (= 1 (:difficulty (first result))))
      (is (= 5 (:difficulty (last result)))))))

;; =============================================================================
;; Auto-Claim Tests
;; =============================================================================

(deftest ready-auto-claim-with-agent-test
  (testing "ready auto-claims when agent provided"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp :agent "my-agent")]
      (is (= "my-agent" (:claimed-by (first result))))
      ;; Verify persisted
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= "my-agent" (:claimed-by loaded)))))))

(deftest ready-no-claim-flag-test
  (testing "ready does not claim with --no-claim"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp :agent "my-agent" :no-claim true)]
      (is (nil? (:claimed-by (first result))))
      ;; Verify not persisted
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (nil? (:claimed-by loaded)))))))

(deftest ready-without-agent-no-claim-test
  (testing "ready does not claim without agent"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp)]
      (is (nil? (:claimed-by (first result))))
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (nil? (:claimed-by loaded)))))))

(deftest ready-claim-creates-commit-test
  (testing "ready auto-claim creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-ready-in-temp :agent "my-agent")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (= (inc initial-count) final-count))))))

;; =============================================================================
;; Prompt Tests
;; =============================================================================

(deftest ready-prompt-includes-claim-test
  (testing "ready prompt includes the mote claim"
    (init-repo!)
    (create-mote! "1" "My specific claim text")
    (let [result (cmd-ready-in-temp)]
      (is (str/includes? (:prompt (first result)) "My specific claim text")))))

(deftest ready-prompt-includes-mote-id-test
  (testing "ready prompt includes the mote ID"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-ready-in-temp)]
      (is (str/includes? (:prompt (first result)) "1")))))

(deftest ready-prompt-role-appropriate-test
  (testing "ready prompt is role-appropriate"
    (init-repo!)
    (create-mote! "1" "Test" :taint #{:needs-verification})
    (let [result (cmd-ready-in-temp)]
      (is (str/includes? (:prompt (first result)) "VERIFIER")))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest ready-no-repo-throws-test
  (testing "ready throws when no repository initialized"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-ready-in-temp)))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest ready-handler-registered-test
  (testing "ready handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "ready")))))

(deftest ready-handler-is-function-test
  (testing "ready handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "ready")]
      (is (fn? handler)))))

;; =============================================================================
;; Parse Helper Tests
;; =============================================================================

(deftest parse-difficulty-spec-exact-test
  (testing "parse-difficulty-spec handles exact values"
    (is (= 3 (@#'cmd/parse-difficulty-spec "3")))
    (is (= 1 (@#'cmd/parse-difficulty-spec "1")))
    (is (= 5 (@#'cmd/parse-difficulty-spec "5")))))

(deftest parse-difficulty-spec-range-test
  (testing "parse-difficulty-spec handles ranges"
    (is (= [2 4] (@#'cmd/parse-difficulty-spec "2-4")))
    (is (= [1 5] (@#'cmd/parse-difficulty-spec "1-5")))))

(deftest parse-difficulty-spec-nil-test
  (testing "parse-difficulty-spec returns nil for nil input"
    (is (nil? (@#'cmd/parse-difficulty-spec nil)))))

(deftest parse-priority-spec-exact-test
  (testing "parse-priority-spec handles exact values"
    (is (= :p0 (@#'cmd/parse-priority-spec "p0")))
    (is (= :p2 (@#'cmd/parse-priority-spec "p2")))
    (is (= :p4 (@#'cmd/parse-priority-spec "P4"))))) ;; case insensitive

(deftest parse-priority-spec-range-test
  (testing "parse-priority-spec handles ranges"
    (is (= [:p1 :p3] (@#'cmd/parse-priority-spec "p1-p3")))
    (is (= [:p0 :p4] (@#'cmd/parse-priority-spec "p0-p4")))))

(deftest parse-priority-spec-nil-test
  (testing "parse-priority-spec returns nil for nil input"
    (is (nil? (@#'cmd/parse-priority-spec nil)))))

(deftest parse-priority-spec-invalid-test
  (testing "parse-priority-spec returns nil for invalid input"
    (is (nil? (@#'cmd/parse-priority-spec "p5")))
    (is (nil? (@#'cmd/parse-priority-spec "high")))))

;; =============================================================================
;; Role Detection Hint Tests
;; =============================================================================

(deftest name-looks-like-role-test
  (testing "name-looks-like-role? detects role names"
    (is (= "advisor" (@#'cmd/name-looks-like-role? "advisor")))
    (is (= "proposer" (@#'cmd/name-looks-like-role? "proposer")))
    (is (= "verifier" (@#'cmd/name-looks-like-role? "verifier")))
    (is (= "prover" (@#'cmd/name-looks-like-role? "prover")))
    (is (= "ref-checker" (@#'cmd/name-looks-like-role? "ref-checker")))
    (is (= "counterexample" (@#'cmd/name-looks-like-role? "counterexample")))))

(deftest name-looks-like-role-case-insensitive-test
  (testing "name-looks-like-role? is case insensitive"
    (is (= "advisor" (@#'cmd/name-looks-like-role? "Advisor")))
    (is (= "proposer" (@#'cmd/name-looks-like-role? "PROPOSER")))))

(deftest name-looks-like-role-negative-test
  (testing "name-looks-like-role? returns nil for non-role names"
    (is (nil? (@#'cmd/name-looks-like-role? "claude")))
    (is (nil? (@#'cmd/name-looks-like-role? "alice")))
    (is (nil? (@#'cmd/name-looks-like-role? nil)))))

(deftest format-role-hint-test
  (testing "format-role-hint produces correct message"
    (let [hint (@#'cmd/format-role-hint "advisor")]
      (is (str/includes? hint "looks like a role name"))
      (is (str/includes? hint "Did you mean"))
      (is (str/includes? hint "--role advisor")))))
