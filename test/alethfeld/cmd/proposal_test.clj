(ns alethfeld.cmd.proposal-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-proposal-test-"})
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

(defn- cmd-propose-in-temp!
  "Call cmd-propose! using the temp directory context."
  [id args & {:keys [agent]}]
  ;; Create a mock context and call cmd-propose!
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")]
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID"]})))
    (when (empty? args)
      (throw (ex-info "At least one claim is required"
                      {:type :validation-failed
                       :errors ["Provide at least one claim as argument"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [claims (@#'cmd/parse-claims args)
          result (alethfeld.proposal/create-proposal! repo-path id claims agent)]
      (:result result))))

(defn- cmd-approve-in-temp!
  "Call cmd-approve! using the temp directory context."
  [id & {:keys [agent reason]}]
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [result (alethfeld.proposal/approve-proposal! repo-path id agent :reason reason)]
      (:result result))))

(defn- cmd-reject-in-temp!
  "Call cmd-reject! using the temp directory context."
  [id & {:keys [agent reason]}]
  (let [repo-path *temp-dir*
        agent (or agent "cli-user")]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [result (alethfeld.proposal/reject-proposal! repo-path id agent :reason reason)]
      (:result result))))

;; =============================================================================
;; Parse Claims Tests
;; =============================================================================

(deftest parse-claims-simple-test
  (testing "parse-claims handles simple claims"
    (let [result (@#'cmd/parse-claims ["First claim" "Second claim"])]
      (is (= 2 (count result)))
      (is (= "First claim" (:claim (first result))))
      (is (nil? (:difficulty (first result)))))))

(deftest parse-claims-with-difficulty-test
  (testing "parse-claims extracts difficulty from @ notation"
    (let [result (@#'cmd/parse-claims ["My claim @3"])]
      (is (= "My claim" (:claim (first result))))
      (is (= 3 (:difficulty (first result)))))))

(deftest parse-claims-mixed-test
  (testing "parse-claims handles mixed claims"
    (let [result (@#'cmd/parse-claims ["Simple claim" "Hard claim @5" "Easy @1"])]
      (is (= 3 (count result)))
      (is (nil? (:difficulty (first result))))
      (is (= 5 (:difficulty (second result))))
      (is (= 1 (:difficulty (nth result 2)))))))

(deftest parse-claims-preserves-whitespace-test
  (testing "parse-claims trims whitespace around claim"
    (let [result (@#'cmd/parse-claims ["  Claim with spaces   @2  "])]
      (is (= "Claim with spaces" (:claim (first result))))
      (is (= 2 (:difficulty (first result)))))))

;; =============================================================================
;; Propose Command - Basic Tests
;; =============================================================================

(deftest propose-creates-proposal-test
  (testing "propose creates a proposal with children"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Child 1" "Child 2"])]
      (is (contains? result :proposal))
      (is (contains? result :children))
      (is (= 2 (count (:children result)))))))

(deftest propose-sets-proposal-id-test
  (testing "propose sets proposal ID"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Child claim"])]
      (is (string? (get-in result [:proposal :id]))))))

(deftest propose-creates-children-with-ids-test
  (testing "propose creates children with proper IDs"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["First" "Second"])
          child-ids (map :id (:children result))]
      (is (= ["1.1" "1.2"] child-ids)))))

(deftest propose-children-have-proposed-status-test
  (testing "proposed children have :proposed status"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Child claim"])
          child (first (:children result))]
      (is (= :proposed (:status child))))))

(deftest propose-children-inherit-difficulty-test
  (testing "proposed children inherit parent difficulty"
    (init-repo!)
    (create-mote! "1" "Parent claim" :difficulty 4)
    (let [result (cmd-propose-in-temp! "1" ["Child claim"])
          child (first (:children result))]
      (is (= 4 (:difficulty child))))))

(deftest propose-children-custom-difficulty-test
  (testing "proposed children can have custom difficulty"
    (init-repo!)
    (create-mote! "1" "Parent claim" :difficulty 3)
    (let [result (cmd-propose-in-temp! "1" ["Easy child @1"])
          child (first (:children result))]
      (is (= 1 (:difficulty child))))))

(deftest propose-updates-parent-taint-test
  (testing "propose updates parent taint to needs-proposal-review"
    (init-repo!)
    (create-mote! "1" "Parent claim" :taint #{:needs-decomposition})
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (contains? (:taint parent) :needs-proposal-review))
      (is (not (contains? (:taint parent) :needs-decomposition))))))

(deftest propose-sets-parent-proposal-test
  (testing "propose sets proposal on parent"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (some? (:proposal parent))))))

(deftest propose-stores-children-in-proposed-test
  (testing "proposed children are stored in proposed/ directory"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [child (store/load-mote *temp-dir* "1.1")]
      (is (some? child))
      (is (= :proposed (:status child))))))

;; =============================================================================
;; Propose Command - Validation Tests
;; =============================================================================

(deftest propose-requires-parent-id-test
  (testing "propose requires parent mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Parent mote ID is required"
                          (cmd-propose-in-temp! nil ["Child claim"])))))

(deftest propose-requires-claims-test
  (testing "propose requires at least one claim"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"At least one claim is required"
                          (cmd-propose-in-temp! "1" [])))))

(deftest propose-requires-repo-test
  (testing "propose requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-propose-in-temp! "1" ["Child claim"])))))

(deftest propose-parent-not-found-test
  (testing "propose fails when parent not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Parent mote not found"
                          (cmd-propose-in-temp! "999" ["Child claim"])))))

(deftest propose-existing-proposal-fails-test
  (testing "propose fails when parent already has proposal"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["First proposal"])
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"already has an active proposal"
                          (cmd-propose-in-temp! "1" ["Second proposal"])))))

;; =============================================================================
;; Approve Command - Basic Tests
;; =============================================================================

(deftest approve-casts-vote-test
  (testing "approve casts an approve vote"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-approve-in-temp! "1")]
      (is (= :approve (get-in result [:vote-cast :vote]))))))

(deftest approve-returns-pending-when-no-quorum-test
  (testing "approve returns pending when quorum not reached"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-approve-in-temp! "1")]
      (is (= :pending (:quorum-status result)))
      (is (nil? (:promoted-children result))))))

(deftest approve-second-vote-reaches-quorum-test
  (testing "approve reaches quorum with two votes"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (let [result (cmd-approve-in-temp! "1" :agent "agent-2")]
      (is (= :approved (:quorum-status result)))
      (is (= ["1.1"] (:promoted-children result))))))

(deftest approve-with-reason-test
  (testing "approve records reason"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-approve-in-temp! "1" :reason "Looks good")]
      (is (= "Looks good" (get-in result [:vote-cast :reason]))))))

;; =============================================================================
;; Approve Command - Quorum Effects Tests
;; =============================================================================

(deftest approve-quorum-promotes-children-test
  (testing "approve quorum promotes children to motes/"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (cmd-approve-in-temp! "1" :agent "agent-2")
    (let [child (store/load-mote *temp-dir* "1.1")]
      (is (= :fixed (:status child))))))

(deftest approve-quorum-clears-proposal-test
  (testing "approve quorum clears parent proposal"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (cmd-approve-in-temp! "1" :agent "agent-2")
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (nil? (:proposal parent))))))

(deftest approve-quorum-updates-parent-children-test
  (testing "approve quorum adds children to parent"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["First" "Second"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (cmd-approve-in-temp! "1" :agent "agent-2")
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (= ["1.1" "1.2"] (:children parent))))))

(deftest approve-quorum-removes-needs-proposal-review-test
  (testing "approve quorum removes needs-proposal-review taint"
    (init-repo!)
    (create-mote! "1" "Parent claim" :taint #{:needs-decomposition})
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (cmd-approve-in-temp! "1" :agent "agent-2")
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (not (contains? (:taint parent) :needs-proposal-review))))))

;; =============================================================================
;; Approve Command - Validation Tests
;; =============================================================================

(deftest approve-requires-mote-id-test
  (testing "approve requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-approve-in-temp! nil)))))

(deftest approve-requires-repo-test
  (testing "approve requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-approve-in-temp! "1")))))

(deftest approve-mote-not-found-test
  (testing "approve fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Parent mote not found"
                          (cmd-approve-in-temp! "999")))))

(deftest approve-no-proposal-test
  (testing "approve fails when no active proposal"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"No active proposal"
                          (cmd-approve-in-temp! "1")))))

(deftest approve-already-voted-test
  (testing "approve fails when agent already voted"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "same-agent")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Agent has already voted"
                          (cmd-approve-in-temp! "1" :agent "same-agent")))))

;; =============================================================================
;; Reject Command - Basic Tests
;; =============================================================================

(deftest reject-casts-vote-test
  (testing "reject casts a reject vote"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-reject-in-temp! "1")]
      (is (= :reject (get-in result [:vote-cast :vote]))))))

(deftest reject-returns-pending-when-no-quorum-test
  (testing "reject returns pending when quorum not reached"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-reject-in-temp! "1")]
      (is (= :pending (:quorum-status result)))
      (is (nil? (:archived-children result))))))

(deftest reject-second-vote-reaches-quorum-test
  (testing "reject reaches quorum with two votes"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "agent-1")
    (let [result (cmd-reject-in-temp! "1" :agent "agent-2")]
      (is (= :rejected (:quorum-status result)))
      (is (= ["1.1"] (:archived-children result))))))

(deftest reject-with-reason-test
  (testing "reject records reason"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [result (cmd-reject-in-temp! "1" :reason "Not a good decomposition")]
      (is (= "Not a good decomposition" (get-in result [:vote-cast :reason]))))))

;; =============================================================================
;; Reject Command - Quorum Effects Tests
;; =============================================================================

(deftest reject-quorum-archives-children-test
  (testing "reject quorum archives children"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "agent-1")
    (cmd-reject-in-temp! "1" :agent "agent-2")
    (let [child (store/load-mote *temp-dir* "1.1")]
      (is (= :rejected (:status child))))))

(deftest reject-quorum-clears-proposal-test
  (testing "reject quorum clears parent proposal"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "agent-1")
    (cmd-reject-in-temp! "1" :agent "agent-2")
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (nil? (:proposal parent))))))

(deftest reject-quorum-restores-needs-decomposition-test
  (testing "reject quorum restores needs-decomposition taint"
    (init-repo!)
    (create-mote! "1" "Parent claim" :taint #{:needs-decomposition})
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "agent-1")
    (cmd-reject-in-temp! "1" :agent "agent-2")
    (let [parent (store/load-mote *temp-dir* "1")]
      (is (contains? (:taint parent) :needs-decomposition))
      (is (not (contains? (:taint parent) :needs-proposal-review))))))

;; =============================================================================
;; Reject Command - Validation Tests
;; =============================================================================

(deftest reject-requires-mote-id-test
  (testing "reject requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-reject-in-temp! nil)))))

(deftest reject-requires-repo-test
  (testing "reject requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-reject-in-temp! "1")))))

(deftest reject-mote-not-found-test
  (testing "reject fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Parent mote not found"
                          (cmd-reject-in-temp! "999")))))

(deftest reject-no-proposal-test
  (testing "reject fails when no active proposal"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"No active proposal"
                          (cmd-reject-in-temp! "1")))))

(deftest reject-already-voted-test
  (testing "reject fails when agent already voted"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "same-agent")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Agent has already voted"
                          (cmd-reject-in-temp! "1" :agent "same-agent")))))

;; =============================================================================
;; Mixed Voting Tests
;; =============================================================================

(deftest mixed-votes-keeps-pending-test
  (testing "mixed approve and reject keeps proposal pending"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [r1 (cmd-approve-in-temp! "1" :agent "agent-1")
          r2 (cmd-reject-in-temp! "1" :agent "agent-2")]
      (is (= :pending (:quorum-status r1)))
      (is (= :pending (:quorum-status r2)))
      ;; Children still proposed
      (let [child (store/load-mote *temp-dir* "1.1")]
        (is (= :proposed (:status child)))))))

(deftest approve-after-reject-test
  (testing "approve vote after reject vote works"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-reject-in-temp! "1" :agent "agent-1")
    (let [result (cmd-approve-in-temp! "1" :agent "agent-2")]
      (is (= :pending (:quorum-status result))))))

(deftest reject-after-approve-test
  (testing "reject vote after approve vote works"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (let [result (cmd-reject-in-temp! "1" :agent "agent-2")]
      (is (= :pending (:quorum-status result))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest propose-handler-registered-test
  (testing "propose handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "propose")))))

(deftest approve-handler-registered-test
  (testing "approve handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "approve")))))

(deftest reject-handler-registered-test
  (testing "reject handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "reject")))))

(deftest propose-handler-is-function-test
  (testing "propose handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "propose")]
      (is (fn? handler)))))

(deftest approve-handler-is-function-test
  (testing "approve handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "approve")]
      (is (fn? handler)))))

(deftest reject-handler-is-function-test
  (testing "reject handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "reject")]
      (is (fn? handler)))))

;; =============================================================================
;; Full Lifecycle Tests
;; =============================================================================

(deftest full-approve-lifecycle-test
  (testing "full proposal lifecycle: create, approve, approve"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    ;; Create proposal
    (let [propose-result (cmd-propose-in-temp! "1" ["Child 1" "Child 2"])]
      (is (= 2 (count (:children propose-result))))
      ;; First approve (pending)
      (let [approve1 (cmd-approve-in-temp! "1" :agent "agent-1")]
        (is (= :pending (:quorum-status approve1)))
        ;; Second approve (quorum)
        (let [approve2 (cmd-approve-in-temp! "1" :agent "agent-2")]
          (is (= :approved (:quorum-status approve2)))
          (is (= ["1.1" "1.2"] (:promoted-children approve2)))
          ;; Verify final state
          (let [parent (store/load-mote *temp-dir* "1")
                child1 (store/load-mote *temp-dir* "1.1")
                child2 (store/load-mote *temp-dir* "1.2")]
            (is (nil? (:proposal parent)))
            (is (= ["1.1" "1.2"] (:children parent)))
            (is (= :fixed (:status child1)))
            (is (= :fixed (:status child2)))))))))

(deftest full-reject-lifecycle-test
  (testing "full proposal lifecycle: create, reject, reject"
    (init-repo!)
    (create-mote! "1" "Parent claim" :taint #{:needs-decomposition})
    ;; Create proposal
    (let [propose-result (cmd-propose-in-temp! "1" ["Child claim"])]
      (is (= 1 (count (:children propose-result))))
      ;; First reject (pending)
      (let [reject1 (cmd-reject-in-temp! "1" :agent "agent-1")]
        (is (= :pending (:quorum-status reject1)))
        ;; Second reject (quorum)
        (let [reject2 (cmd-reject-in-temp! "1" :agent "agent-2")]
          (is (= :rejected (:quorum-status reject2)))
          (is (= ["1.1"] (:archived-children reject2)))
          ;; Verify final state
          (let [parent (store/load-mote *temp-dir* "1")
                child (store/load-mote *temp-dir* "1.1")]
            (is (nil? (:proposal parent)))
            (is (empty? (:children parent)))
            (is (contains? (:taint parent) :needs-decomposition))
            (is (= :rejected (:status child)))))))))

(deftest propose-creates-git-commit-test
  (testing "propose creates git commit"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-propose-in-temp! "1" ["Child claim"])
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest approve-creates-git-commit-test
  (testing "approve creates git commit"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-approve-in-temp! "1")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest reject-creates-git-commit-test
  (testing "reject creates git commit"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Child claim"])
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-reject-in-temp! "1")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

;; =============================================================================
;; Parse Claims - Atomic Notation Tests (Step C.5)
;; =============================================================================

(deftest parse-claims-atomic-test
  (testing "parse-claims handles atomic marker (!)"
    (let [result (@#'cmd/parse-claims ["Simple fact!"])]
      (is (= "Simple fact" (:claim (first result))))
      (is (true? (:atomic (first result)))))))

(deftest parse-claims-atomic-with-difficulty-test
  (testing "parse-claims handles atomic with difficulty (@N!)"
    (let [result (@#'cmd/parse-claims ["Verified fact @2!"])]
      (is (= "Verified fact" (:claim (first result))))
      (is (= 2 (:difficulty (first result))))
      (is (true? (:atomic (first result)))))))

(deftest parse-claims-mixed-atomic-test
  (testing "parse-claims handles mixed atomic and non-atomic"
    (let [result (@#'cmd/parse-claims ["Complex step" "Simple fact!" "Another step @3"])]
      ;; First: non-atomic, no difficulty
      (is (= "Complex step" (:claim (first result))))
      (is (nil? (:atomic (first result))))
      (is (nil? (:difficulty (first result))))
      ;; Second: atomic, no difficulty
      (is (= "Simple fact" (:claim (second result))))
      (is (true? (:atomic (second result))))
      (is (nil? (:difficulty (second result))))
      ;; Third: non-atomic, with difficulty
      (is (= "Another step" (:claim (nth result 2))))
      (is (nil? (:atomic (nth result 2))))
      (is (= 3 (:difficulty (nth result 2)))))))

(deftest parse-claims-atomic-preserves-whitespace-test
  (testing "parse-claims handles atomic with whitespace"
    (let [result (@#'cmd/parse-claims ["  Claim with spaces  @3!"])]
      (is (= "Claim with spaces" (:claim (first result))))
      (is (= 3 (:difficulty (first result))))
      (is (true? (:atomic (first result)))))))

;; =============================================================================
;; Atomic Claims - Proposal Integration Tests (Step C.5)
;; =============================================================================

(deftest propose-atomic-claim-has-correct-taint-test
  (testing "propose with atomic claim sets :needs-verification taint"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Simple fact!"])
          child (first (:children result))]
      (is (contains? (:taint child) :needs-verification))
      (is (not (contains? (:taint child) :needs-decomposition)))
      (is (true? (:atomic child))))))

(deftest propose-non-atomic-claim-has-correct-taint-test
  (testing "propose with non-atomic claim sets :needs-decomposition taint"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Complex step"])
          child (first (:children result))]
      (is (contains? (:taint child) :needs-decomposition))
      (is (not (contains? (:taint child) :needs-verification)))
      (is (nil? (:atomic child))))))

(deftest propose-mixed-atomic-claims-test
  (testing "propose with mixed claims sets correct taints"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (let [result (cmd-propose-in-temp! "1" ["Complex step" "Simple fact!" "Hard step @4"])
          [child1 child2 child3] (:children result)]
      ;; First: non-atomic
      (is (contains? (:taint child1) :needs-decomposition))
      (is (nil? (:atomic child1)))
      ;; Second: atomic
      (is (contains? (:taint child2) :needs-verification))
      (is (true? (:atomic child2)))
      ;; Third: non-atomic with difficulty
      (is (contains? (:taint child3) :needs-decomposition))
      (is (nil? (:atomic child3)))
      (is (= 4 (:difficulty child3))))))

(deftest approve-atomic-claim-preserves-taint-test
  (testing "approved atomic claim has :needs-verification taint"
    (init-repo!)
    (create-mote! "1" "Parent claim")
    (cmd-propose-in-temp! "1" ["Simple fact!"])
    (cmd-approve-in-temp! "1" :agent "agent-1")
    (cmd-approve-in-temp! "1" :agent "agent-2")
    (let [child (store/load-mote *temp-dir* "1.1")]
      (is (= :fixed (:status child)))
      (is (contains? (:taint child) :needs-verification))
      (is (not (contains? (:taint child) :needs-decomposition)))
      (is (true? (:atomic child))))))
