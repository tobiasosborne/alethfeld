(ns alethfeld.cmd.update-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [alethfeld.verify :as verify]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-update-test-"})
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

(defn- cmd-update-in-temp!
  "Call cmd-update! using the temp directory context."
  [id & {:keys [claim priority difficulty agent]}]
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to update"]})))
    (when (and (nil? claim) (nil? priority) (nil? difficulty))
      (throw (ex-info "No update fields provided"
                      {:type :validation-failed
                       :errors ["Provide at least one of --claim, --priority, or --difficulty"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [parsed-priority (when priority (@#'cmd/parse-priority priority))]
        (when (and priority (nil? parsed-priority))
          (throw (ex-info "Invalid priority"
                          {:type :validation-failed
                           :errors [(str "Priority must be p0-p4, got: " priority)]})))
        (when (and difficulty (or (< difficulty 1) (> difficulty 5)))
          (throw (ex-info "Invalid difficulty"
                          {:type :validation-failed
                           :errors [(str "Difficulty must be 1-5, got: " difficulty)]})))
        (let [updated-mote (cond-> current-mote
                            claim (mote/set-claim claim)
                            parsed-priority (mote/set-priority parsed-priority)
                            difficulty (mote/set-difficulty difficulty))]
          (alethfeld.tx/atomic-write! repo-path
                                       (str "Update mote " id)
                                       [updated-mote])
          updated-mote)))))

(defn- cmd-vote-in-temp!
  "Call cmd-vote! using the temp directory context."
  [id & {:keys [for against reason agent]}]
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to vote on"]})))
    (when (and for against)
      (throw (ex-info "Cannot vote both for and against"
                      {:type :validation-failed
                       :errors ["Provide either --for or --against, not both"]})))
    (when (and (not for) (not against))
      (throw (ex-info "Vote direction required"
                      {:type :validation-failed
                       :errors ["Provide --for or --against"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [vote-type (if for :for :against)
          result (verify/cast-vote! repo-path id agent vote-type :reason reason)]
      (:result result))))

(defn- cmd-taint-in-temp!
  "Call cmd-taint! using the temp directory context."
  [id & {:keys [add remove agent]}]
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")
        adds (if (sequential? add) add (when add [add]))
        removes (if (sequential? remove) remove (when remove [remove]))]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to modify taints"]})))
    (when (and (empty? adds) (empty? removes))
      (throw (ex-info "No taint changes provided"
                      {:type :validation-failed
                       :errors ["Provide at least one --add or --remove"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [parsed-adds (map @#'cmd/parse-taint adds)
            parsed-removes (map @#'cmd/parse-taint removes)]
        (when (some nil? (concat (when (seq adds) parsed-adds)
                                  (when (seq removes) parsed-removes)))
          (let [invalid-values (concat
                                 (filter #(nil? (@#'cmd/parse-taint %)) adds)
                                 (filter #(nil? (@#'cmd/parse-taint %)) removes))]
            (throw (ex-info "Invalid taint"
                            {:type :validation-failed
                             :errors [(str "Invalid taint: " (first invalid-values))]}))))
        (let [updated-mote (as-> current-mote m
                            (reduce mote/add-taint m (filter some? parsed-adds))
                            (reduce mote/remove-taint m (filter some? parsed-removes)))]
          (alethfeld.tx/atomic-write! repo-path
                                       (str "Update taints on " id)
                                       [updated-mote])
          updated-mote)))))

;; =============================================================================
;; Update Command - Basic Tests
;; =============================================================================

(deftest update-claim-test
  (testing "update changes claim text"
    (init-repo!)
    (create-mote! "1" "Original claim")
    (let [result (cmd-update-in-temp! "1" :claim "New claim")]
      (is (= "New claim" (:claim result)))
      ;; Verify persisted
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= "New claim" (:claim loaded)))))))

(deftest update-priority-test
  (testing "update changes priority"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p2)
    (let [result (cmd-update-in-temp! "1" :priority "p0")]
      (is (= :p0 (:priority result)))
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= :p0 (:priority loaded)))))))

(deftest update-difficulty-test
  (testing "update changes difficulty"
    (init-repo!)
    (create-mote! "1" "Test claim" :difficulty 3)
    (let [result (cmd-update-in-temp! "1" :difficulty 5)]
      (is (= 5 (:difficulty result)))
      (let [loaded (store/load-mote *temp-dir* "1")]
        (is (= 5 (:difficulty loaded)))))))

(deftest update-multiple-fields-test
  (testing "update can change multiple fields at once"
    (init-repo!)
    (create-mote! "1" "Original" :priority :p2 :difficulty 3)
    (let [result (cmd-update-in-temp! "1" :claim "Updated" :priority "p1" :difficulty 4)]
      (is (= "Updated" (:claim result)))
      (is (= :p1 (:priority result)))
      (is (= 4 (:difficulty result))))))

(deftest update-priority-case-insensitive-test
  (testing "priority parsing is case insensitive"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-update-in-temp! "1" :priority "P1")]
      (is (= :p1 (:priority result))))))

(deftest update-preserves-other-fields-test
  (testing "update preserves fields not being changed"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-verification})
    (cmd-update-in-temp! "1" :claim "New claim")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (contains? (:taint loaded) :needs-verification)))))

;; =============================================================================
;; Update Command - Validation Tests
;; =============================================================================

(deftest update-requires-mote-id-test
  (testing "update requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-update-in-temp! nil :claim "New")))))

(deftest update-requires-fields-test
  (testing "update requires at least one field"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"No update fields provided"
                          (cmd-update-in-temp! "1")))))

(deftest update-requires-repo-test
  (testing "update requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-update-in-temp! "1" :claim "New")))))

(deftest update-mote-not-found-test
  (testing "update fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-update-in-temp! "999" :claim "New")))))

(deftest update-invalid-priority-test
  (testing "update rejects invalid priority"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid priority"
                          (cmd-update-in-temp! "1" :priority "p9")))))

(deftest update-invalid-difficulty-low-test
  (testing "update rejects difficulty below 1"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid difficulty"
                          (cmd-update-in-temp! "1" :difficulty 0)))))

(deftest update-invalid-difficulty-high-test
  (testing "update rejects difficulty above 5"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid difficulty"
                          (cmd-update-in-temp! "1" :difficulty 6)))))

(deftest update-creates-git-commit-test
  (testing "update creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-update-in-temp! "1" :claim "New claim")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

;; =============================================================================
;; Vote Command - Basic Tests
;; =============================================================================

(deftest vote-for-test
  (testing "vote --for casts for vote"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed :taint #{:needs-verification})
    (let [result (cmd-vote-in-temp! "1" :for true)]
      (is (= :for (get-in result [:vote-cast :vote]))))))

(deftest vote-against-test
  (testing "vote --against casts against vote"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed :taint #{:needs-verification})
    (let [result (cmd-vote-in-temp! "1" :against true)]
      (is (= :against (get-in result [:vote-cast :vote]))))))

(deftest vote-with-reason-test
  (testing "vote records reason"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (let [result (cmd-vote-in-temp! "1" :for true :reason "Proof is correct")]
      (is (= "Proof is correct" (get-in result [:vote-cast :reason]))))))

(deftest vote-returns-pending-initially-test
  (testing "first vote returns pending status"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (let [result (cmd-vote-in-temp! "1" :for true)]
      (is (= :pending (:quorum-status result))))))

(deftest vote-for-quorum-verified-test
  (testing "unanimous for votes lead to verified status"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed :taint #{:needs-verification})
    (cmd-vote-in-temp! "1" :for true :agent "agent-1")
    (let [result (cmd-vote-in-temp! "1" :for true :agent "agent-2")]
      (is (= :verified (:quorum-status result)))
      (is (= :verified (:new-status result)))
      (is (:status-changed result)))))

(deftest vote-against-quorum-refuted-test
  (testing "unanimous against votes lead to refuted status"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed :taint #{:needs-verification})
    (cmd-vote-in-temp! "1" :against true :agent "agent-1")
    (let [result (cmd-vote-in-temp! "1" :against true :agent "agent-2")]
      (is (= :refuted (:quorum-status result)))
      (is (= :refuted (:new-status result))))))

(deftest vote-mixed-contested-test
  (testing "mixed votes lead to contested status"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed :taint #{:needs-verification})
    (cmd-vote-in-temp! "1" :for true :agent "agent-1")
    (let [result (cmd-vote-in-temp! "1" :against true :agent "agent-2")]
      (is (= :contested (:quorum-status result)))
      (is (= :contested (:new-status result))))))

;; =============================================================================
;; Vote Command - Validation Tests
;; =============================================================================

(deftest vote-requires-mote-id-test
  (testing "vote requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-vote-in-temp! nil :for true)))))

(deftest vote-requires-direction-test
  (testing "vote requires --for or --against"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Vote direction required"
                          (cmd-vote-in-temp! "1")))))

(deftest vote-cannot-vote-both-test
  (testing "cannot vote both for and against"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Cannot vote both for and against"
                          (cmd-vote-in-temp! "1" :for true :against true)))))

(deftest vote-requires-repo-test
  (testing "vote requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-vote-in-temp! "1" :for true)))))

(deftest vote-mote-not-found-test
  (testing "vote fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-vote-in-temp! "999" :for true)))))

(deftest vote-only-fixed-motes-test
  (testing "can only vote on fixed motes"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :verified)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Can only vote on fixed motes"
                          (cmd-vote-in-temp! "1" :for true)))))

(deftest vote-already-voted-test
  (testing "cannot vote twice"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (cmd-vote-in-temp! "1" :for true :agent "same-agent")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Agent has already voted"
                          (cmd-vote-in-temp! "1" :for true :agent "same-agent")))))

(deftest vote-creates-git-commit-test
  (testing "vote creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim" :status :fixed)
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-vote-in-temp! "1" :for true)
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

;; =============================================================================
;; Taint Command - Basic Tests
;; =============================================================================

(deftest taint-add-single-test
  (testing "taint --add adds a single taint"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{})
    (let [result (cmd-taint-in-temp! "1" :add "needs-verification")]
      (is (contains? (:taint result) :needs-verification)))))

(deftest taint-add-multiple-test
  (testing "taint can add multiple taints"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{})
    (let [result (cmd-taint-in-temp! "1" :add ["needs-verification" "needs-refs"])]
      (is (contains? (:taint result) :needs-verification))
      (is (contains? (:taint result) :needs-refs)))))

(deftest taint-remove-single-test
  (testing "taint --remove removes a single taint"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition :needs-verification})
    (let [result (cmd-taint-in-temp! "1" :remove "needs-decomposition")]
      (is (not (contains? (:taint result) :needs-decomposition)))
      (is (contains? (:taint result) :needs-verification)))))

(deftest taint-remove-multiple-test
  (testing "taint can remove multiple taints"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition :needs-verification :needs-refs})
    (let [result (cmd-taint-in-temp! "1" :remove ["needs-decomposition" "needs-verification"])]
      (is (not (contains? (:taint result) :needs-decomposition)))
      (is (not (contains? (:taint result) :needs-verification)))
      (is (contains? (:taint result) :needs-refs)))))

(deftest taint-add-and-remove-test
  (testing "taint can add and remove in same call"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition})
    (let [result (cmd-taint-in-temp! "1" :add "needs-verification" :remove "needs-decomposition")]
      (is (contains? (:taint result) :needs-verification))
      (is (not (contains? (:taint result) :needs-decomposition))))))

(deftest taint-persists-test
  (testing "taint changes are persisted"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{})
    (cmd-taint-in-temp! "1" :add "needs-verification")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (contains? (:taint loaded) :needs-verification)))))

(deftest taint-add-idempotent-test
  (testing "adding existing taint is idempotent"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition})
    (let [result (cmd-taint-in-temp! "1" :add "needs-decomposition")]
      (is (contains? (:taint result) :needs-decomposition)))))

(deftest taint-remove-nonexistent-test
  (testing "removing nonexistent taint is safe"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{:needs-decomposition})
    (let [result (cmd-taint-in-temp! "1" :remove "needs-verification")]
      (is (contains? (:taint result) :needs-decomposition)))))

;; =============================================================================
;; Taint Command - Validation Tests
;; =============================================================================

(deftest taint-requires-mote-id-test
  (testing "taint requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-taint-in-temp! nil :add "needs-verification")))))

(deftest taint-requires-changes-test
  (testing "taint requires --add or --remove"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"No taint changes provided"
                          (cmd-taint-in-temp! "1")))))

(deftest taint-requires-repo-test
  (testing "taint requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-taint-in-temp! "1" :add "needs-verification")))))

(deftest taint-mote-not-found-test
  (testing "taint fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-taint-in-temp! "999" :add "needs-verification")))))

(deftest taint-invalid-add-test
  (testing "taint rejects invalid taint to add"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid taint"
                          (cmd-taint-in-temp! "1" :add "invalid-taint")))))

(deftest taint-invalid-remove-test
  (testing "taint rejects invalid taint to remove"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid taint"
                          (cmd-taint-in-temp! "1" :remove "not-a-taint")))))

(deftest taint-creates-git-commit-test
  (testing "taint creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim" :taint #{})
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-taint-in-temp! "1" :add "needs-verification")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest update-handler-registered-test
  (testing "update handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "update")))))

(deftest vote-handler-registered-test
  (testing "vote handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "vote")))))

(deftest taint-handler-registered-test
  (testing "taint handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "taint")))))

(deftest update-handler-is-function-test
  (testing "update handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "update")]
      (is (fn? handler)))))

(deftest vote-handler-is-function-test
  (testing "vote handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "vote")]
      (is (fn? handler)))))

(deftest taint-handler-is-function-test
  (testing "taint handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "taint")]
      (is (fn? handler)))))

;; =============================================================================
;; Parse Helper Tests
;; =============================================================================

(deftest parse-priority-valid-test
  (testing "parse-priority handles valid priorities"
    (is (= :p0 (@#'cmd/parse-priority "p0")))
    (is (= :p1 (@#'cmd/parse-priority "p1")))
    (is (= :p2 (@#'cmd/parse-priority "p2")))
    (is (= :p3 (@#'cmd/parse-priority "p3")))
    (is (= :p4 (@#'cmd/parse-priority "p4")))))

(deftest parse-priority-case-insensitive-test
  (testing "parse-priority is case insensitive"
    (is (= :p0 (@#'cmd/parse-priority "P0")))
    (is (= :p2 (@#'cmd/parse-priority "P2")))))

(deftest parse-priority-nil-test
  (testing "parse-priority returns nil for nil input"
    (is (nil? (@#'cmd/parse-priority nil)))))

(deftest parse-priority-invalid-test
  (testing "parse-priority returns nil for invalid input"
    (is (nil? (@#'cmd/parse-priority "p5")))
    (is (nil? (@#'cmd/parse-priority "high")))
    (is (nil? (@#'cmd/parse-priority "")))))

(deftest parse-taint-valid-test
  (testing "parse-taint handles valid taints"
    (is (= :needs-decomposition (@#'cmd/parse-taint "needs-decomposition")))
    (is (= :needs-verification (@#'cmd/parse-taint "needs-verification")))
    (is (= :needs-refs (@#'cmd/parse-taint "needs-refs")))))

(deftest parse-taint-with-colon-test
  (testing "parse-taint handles taints with leading colon"
    (is (= :needs-decomposition (@#'cmd/parse-taint ":needs-decomposition")))))

(deftest parse-taint-case-insensitive-test
  (testing "parse-taint is case insensitive"
    (is (= :needs-decomposition (@#'cmd/parse-taint "NEEDS-DECOMPOSITION")))
    (is (= :needs-verification (@#'cmd/parse-taint "Needs-Verification")))))

(deftest parse-taint-nil-test
  (testing "parse-taint returns nil for nil input"
    (is (nil? (@#'cmd/parse-taint nil)))))

(deftest parse-taint-invalid-test
  (testing "parse-taint returns nil for invalid input"
    (is (nil? (@#'cmd/parse-taint "invalid")))
    (is (nil? (@#'cmd/parse-taint "needs-foo")))))
