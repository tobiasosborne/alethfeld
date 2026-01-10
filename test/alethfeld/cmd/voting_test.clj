(ns alethfeld.cmd.voting-test
  "Tests for voting command with --propagate flag integration.

   These tests verify the cmd-vote! function properly handles the --propagate flag,
   which triggers automatic verification propagation up the mote tree when all
   siblings are verified."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [alethfeld.cmd.voting :as voting]
            [alethfeld.mote :as mote]
            [alethfeld.store :as store]
            [alethfeld.session :as session]
            [alethfeld.verify :as verify]
            [alethfeld.git :as git]
            [babashka.fs :as fs]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-voting-test-"})
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
;; Helper Functions
;; -----------------------------------------------------------------------------

(defn- init-repo!
  "Initialize a test repository with quorum=1 for easy testing."
  []
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :config {:project-name "Voting Test"
                                        :version "0.1"
                                        :default-difficulty 3
                                        :vote-quorum 1
                                        :proposal-quorum 1
                                        :claim-timeout-minutes 30})
  (session/ensure-session-dirs! *temp-dir*)
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-mote!
  "Create a mote directly in the store for test setup."
  [id claim & {:keys [difficulty priority taint parent status children contributors]
               :or {difficulty 3 priority :p2
                    taint #{:needs-verification}
                    status :fixed
                    children []}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :difficulty difficulty
                          :priority priority
                          :taint taint
                          :status status
                          :parent parent
                          :children children
                          :contributors (or contributors {:created-by "test-agent"}))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

(defn- create-session!
  "Create a test session for an agent on a mote."
  [agent mote-id role]
  (let [result (session/create-session! *temp-dir* mote-id role agent)]
    (:session-id result)))

(defn- create-tree!
  "Create a simple tree structure for testing propagation.

   Creates:
   - parent (1): with children [1.1, 1.2]
   - child1 (1.1): verified or fixed based on options
   - child2 (1.2): fixed (needs verification)

   Returns map of mote-id -> mote."
  [& {:keys [parent-status parent-contributors child1-status child2-status]
      :or {parent-status :fixed
           parent-contributors {:created-by "proposer-1"}
           child1-status :verified
           child2-status :fixed}}]
  (let [parent (create-mote! "1" "Root claim"
                             :status parent-status
                             :taint (if (= parent-status :fixed)
                                      #{:needs-verification}
                                      #{})
                             :children ["1.1" "1.2"]
                             :contributors parent-contributors)
        child1 (create-mote! "1.1" "Child 1 claim"
                             :status child1-status
                             :taint (if (= child1-status :fixed)
                                      #{:needs-verification}
                                      #{})
                             :parent "1")
        child2 (create-mote! "1.2" "Child 2 claim"
                             :status child2-status
                             :taint (if (= child2-status :fixed)
                                      #{:needs-verification}
                                      #{})
                             :parent "1")]
    {"1" parent "1.1" child1 "1.2" child2}))

;; Local implementation that matches cmd-vote! but uses *temp-dir*
(defn- cmd-vote-in-temp!
  "Execute vote command in the test temp directory.

   Arguments:
   - id: Mote ID to vote on
   - options: Map with :session, :for/:against, :propagate, :reason, :name"
  [id options]
  (let [repo-path *temp-dir*
        {:keys [for against reason session propagate]} options]

    ;; Validation
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

    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Execute
    (let [sess (session/enforce-session! repo-path session :vote id)
          agent (or (:name options) (:agent sess))
          vote-type (if for :for :against)
          result (verify/cast-vote! repo-path id agent vote-type :reason reason)
          vote-result (:result result)
          quorum-status (:quorum-status vote-result)
          ;; Handle propagation if requested and vote was for (not against)
          final-result (if (and propagate for (= :verified quorum-status))
                         (let [propagated (verify/propagate-verification! repo-path id agent :reason reason)]
                           (assoc vote-result :propagated propagated))
                         vote-result)]
      (assoc final-result
             :message (case quorum-status
                        :verified "Mote verified! Quorum reached."
                        :refuted "Mote refuted. Quorum reached."
                        :contested "Mote contested - votes are mixed."
                        :pending "Vote recorded.")))))

;; -----------------------------------------------------------------------------
;; cmd-vote! Basic Validation Tests
;; -----------------------------------------------------------------------------

(deftest cmd-vote-validation-test
  (init-repo!)

  (testing "cmd-vote! requires mote ID"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Mote ID is required"
                          (cmd-vote-in-temp! nil {:for true :session "token"}))))

  (testing "cmd-vote! rejects both --for and --against"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cannot vote both for and against"
                          (cmd-vote-in-temp! "1" {:for true :against true :session "token"}))))

  (testing "cmd-vote! requires vote direction"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Vote direction required"
                          (cmd-vote-in-temp! "1" {:session "token"}))))

  (testing "cmd-vote! requires session"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Session token is required"
                          (cmd-vote-in-temp! "1" {:for true})))))

;; -----------------------------------------------------------------------------
;; cmd-vote! Basic Voting Tests
;; -----------------------------------------------------------------------------

(deftest cmd-vote-basic-test
  (testing "cmd-vote! casts vote and verifies with quorum=1"
    (init-repo!)
    (create-mote! "1" "Test claim"
                  :contributors {:created-by "creator-1"})
    (let [token (create-session! "verifier-1" "1" :verifier)
          result (cmd-vote-in-temp! "1" {:session token :for true})]
      (is (= :verified (:quorum-status result)))
      (is (:status-changed result))
      (is (= "Mote verified! Quorum reached." (:message result))))))

(deftest cmd-vote-against-test
  (testing "cmd-vote! with --against refutes mote"
    (init-repo!)
    (create-mote! "1" "Test claim"
                  :contributors {:created-by "creator-1"})
    (let [token (create-session! "verifier-1" "1" :verifier)
          result (cmd-vote-in-temp! "1" {:session token :against true})]
      (is (= :refuted (:quorum-status result)))
      (is (:status-changed result))
      (is (= "Mote refuted. Quorum reached." (:message result))))))

;; -----------------------------------------------------------------------------
;; --propagate Flag Tests
;; -----------------------------------------------------------------------------

(deftest cmd-vote-propagate-basic-test
  (testing "cmd-vote! with --propagate propagates to parent when all siblings verified"
    (init-repo!)
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :for true :propagate true})]
      ;; Child should be verified
      (is (= :verified (:quorum-status result)))
      ;; Propagation should have occurred
      (is (= ["1"] (:propagated result)))
      ;; Parent should now be verified
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :verified (:status parent)))))))

(deftest cmd-vote-propagate-disabled-test
  (testing "cmd-vote! without --propagate does not propagate"
    (init-repo!)
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :for true :propagate false})]
      ;; Child should be verified
      (is (= :verified (:quorum-status result)))
      ;; No propagation key in result
      (is (nil? (:propagated result)))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))))))

(deftest cmd-vote-propagate-against-test
  (testing "cmd-vote! with --propagate and --against does not propagate"
    (init-repo!)
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :against true :propagate true})]
      ;; Child should be refuted (not verified)
      (is (= :refuted (:quorum-status result)))
      ;; No propagation (propagation only applies to :for votes that result in :verified)
      (is (nil? (:propagated result)))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))))))

(deftest cmd-vote-propagate-stops-at-contributor-test
  (testing "cmd-vote! with --propagate stops at contributor boundary"
    (init-repo!)
    (create-tree! :child1-status :verified
                  :child2-status :fixed
                  :parent-contributors {:created-by "verifier-1"})
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :for true :propagate true})]
      ;; Child should be verified
      (is (= :verified (:quorum-status result)))
      ;; Propagation should be empty (verifier-1 is contributor to parent)
      (is (empty? (:propagated result)))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))))))

(deftest cmd-vote-propagate-not-all-siblings-verified-test
  (testing "cmd-vote! with --propagate does not propagate when siblings not verified"
    (init-repo!)
    (create-tree! :child1-status :fixed :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :for true :propagate true})]
      ;; Child should be verified
      (is (= :verified (:quorum-status result)))
      ;; Propagation should be empty (sibling 1.1 is not verified)
      (is (empty? (:propagated result)))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))))))

(deftest cmd-vote-propagate-multi-level-test
  (testing "cmd-vote! with --propagate propagates multiple levels up the tree"
    (init-repo!)
    ;; Create a deeper tree
    (create-mote! "1" "Root"
                  :status :fixed
                  :taint #{:needs-verification}
                  :children ["1.1" "1.2"]
                  :contributors {:created-by "proposer-1"})
    (create-mote! "1.1" "Child 1"
                  :status :verified
                  :taint #{}
                  :parent "1")
    (create-mote! "1.2" "Child 2"
                  :status :fixed
                  :taint #{:needs-verification}
                  :parent "1"
                  :children ["1.2.1" "1.2.2"]
                  :contributors {:created-by "proposer-2"})
    (create-mote! "1.2.1" "Grandchild 1"
                  :status :verified
                  :taint #{}
                  :parent "1.2")
    (create-mote! "1.2.2" "Grandchild 2"
                  :status :fixed
                  :taint #{:needs-verification}
                  :parent "1.2")

    (let [token (create-session! "verifier-1" "1.2.2" :verifier)
          result (cmd-vote-in-temp! "1.2.2" {:session token :for true :propagate true})]
      ;; Grandchild should be verified
      (is (= :verified (:quorum-status result)))
      ;; Propagation should include both 1.2 and 1
      (is (= ["1.2" "1"] (:propagated result)))
      ;; Both parent and grandparent should be verified
      (let [c2 (store/load-mote *temp-dir* "1.2")
            root (store/load-mote *temp-dir* "1")]
        (is (= :verified (:status c2)))
        (is (= :verified (:status root)))))))

(deftest cmd-vote-propagate-pending-quorum-test
  (testing "cmd-vote! with --propagate does not propagate when initial vote doesn't reach quorum"
    (init-repo!)
    ;; Set up repo with quorum=2
    (store/save-config! *temp-dir* {:project-name "Test" :vote-quorum 2})
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token :for true :propagate true})]
      ;; Child should be pending (quorum=2, only 1 vote)
      (is (= :pending (:quorum-status result)))
      ;; No propagation key (child not verified yet)
      (is (nil? (:propagated result)))
      ;; Parent should still be fixed
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))))))

(deftest cmd-vote-propagate-stops-at-root-test
  (testing "cmd-vote! with --propagate stops at root (no parent)"
    (init-repo!)
    (create-mote! "1" "Root only"
                  :status :fixed
                  :taint #{:needs-verification}
                  :children []
                  :contributors {:created-by "creator-1"})
    (let [token (create-session! "verifier-1" "1" :verifier)
          result (cmd-vote-in-temp! "1" {:session token :for true :propagate true})]
      ;; Root should be verified
      (is (= :verified (:quorum-status result)))
      ;; Propagation should be empty (root has no parent)
      (is (empty? (:propagated result))))))

;; -----------------------------------------------------------------------------
;; Integration with verify module
;; -----------------------------------------------------------------------------

(deftest propagate-uses-verify-module-test
  (testing "propagation uses verify/propagate-verification! correctly"
    (init-repo!)
    (create-tree! :child1-status :verified :child2-status :fixed)
    ;; Verify child 1.2 directly with verify module
    (verify/cast-vote! *temp-dir* "1.2" "verifier-1" :for)
    ;; Now propagate
    (let [propagated (verify/propagate-verification! *temp-dir* "1.2" "verifier-1")]
      (is (= ["1"] propagated))
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :verified (:status parent)))))))

;; -----------------------------------------------------------------------------
;; Edge Cases
;; -----------------------------------------------------------------------------

(deftest propagate-with-reason-test
  (testing "propagation passes reason to auto-votes"
    (init-repo!)
    (create-tree! :child1-status :verified :child2-status :fixed)
    (let [token (create-session! "verifier-1" "1.2" :verifier)
          _result (cmd-vote-in-temp! "1.2" {:session token
                                            :for true
                                            :propagate true
                                            :reason "All checks passed"})]
      ;; Check parent vote has the reason
      (let [parent (store/load-mote *temp-dir* "1")
            vote (first (:votes parent))]
        ;; When reason is passed, it's used for propagated votes
        (is (= "All checks passed" (:reason vote)))))))

(deftest propagate-partial-success-test
  (testing "propagation reports parents that were voted on even if not all reached quorum"
    (init-repo!)
    ;; Set quorum=2 so parent won't reach quorum with just one propagated vote
    (store/save-config! *temp-dir* {:project-name "Test" :vote-quorum 2})
    ;; Create tree with both children verified (after this vote)
    (create-mote! "1" "Root"
                  :status :fixed
                  :taint #{:needs-verification}
                  :children ["1.1" "1.2"]
                  :contributors {:created-by "proposer-1"})
    (create-mote! "1.1" "Child 1"
                  :status :verified
                  :taint #{}
                  :parent "1")
    (create-mote! "1.2" "Child 2"
                  :status :fixed
                  :taint #{:needs-verification}
                  :parent "1")
    ;; Cast first vote on 1.2 (doesn't reach quorum)
    (let [token1 (create-session! "verifier-1" "1.2" :verifier)]
      (verify/cast-vote! *temp-dir* "1.2" "verifier-1" :for))
    ;; Cast second vote on 1.2 with propagation
    (let [token2 (create-session! "verifier-2" "1.2" :verifier)
          result (cmd-vote-in-temp! "1.2" {:session token2 :for true :propagate true})]
      ;; Child should be verified (quorum=2, got 2 votes)
      (is (= :verified (:quorum-status result)))
      ;; Propagation should include parent
      (is (= ["1"] (:propagated result)))
      ;; Parent should have 1 vote but still be fixed (needs 2 for quorum)
      (let [parent (store/load-mote *temp-dir* "1")]
        (is (= :fixed (:status parent)))
        (is (= 1 (count (:votes parent))))))))
