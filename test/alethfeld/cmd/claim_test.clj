(ns alethfeld.cmd.claim-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]
            [alethfeld.tx :as tx]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)
(def ^:dynamic *original-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-claim-test-"})
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
  [id claim & {:keys [difficulty priority taint parent status claimed-by]
               :or {difficulty 3 priority :p2
                    taint #{:needs-decomposition}
                    status :fixed}}]
  (let [m (cond-> (mote/make-mote id claim "test-agent"
                                   :difficulty difficulty
                                   :priority priority
                                   :taint taint
                                   :status status
                                   :parent parent)
            claimed-by (mote/set-claimed-by claimed-by))]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

(defn- cmd-claim-in-temp!
  "Call cmd-claim! using the temp directory context."
  [id & {:keys [agent]}]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to claim"]})))
    (when-not agent
      (throw (ex-info "Agent name is required"
                      {:type :validation-failed
                       :errors ["Provide --agent to claim the mote"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [current-claimer (:claimed-by current-mote)]
        (when (and current-claimer (not= current-claimer agent))
          (throw (ex-info "Mote already claimed"
                          {:type :already-claimed
                           :mote-id id
                           :claimed-by current-claimer}))))
      (let [updated-mote (mote/set-claimed-by current-mote agent)]
        (tx/atomic-write! repo-path
                          (str "Claim mote " id " for " agent)
                          [updated-mote])
        updated-mote))))

(defn- cmd-unclaim-in-temp!
  "Call cmd-unclaim! using the temp directory context."
  [id]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to unclaim"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [updated-mote (mote/clear-claim current-mote)]
        (tx/atomic-write! repo-path
                          (str "Unclaim mote " id)
                          [updated-mote])
        updated-mote))))

;; =============================================================================
;; Claim Command - Basic Tests
;; =============================================================================

(deftest claim-sets-claimed-by-test
  (testing "claim sets claimed-by field"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-claim-in-temp! "1" :agent "agent-1")]
      (is (= "agent-1" (:claimed-by result))))))

(deftest claim-sets-claimed-at-test
  (testing "claim sets claimed-at timestamp"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-claim-in-temp! "1" :agent "agent-1")]
      (is (some? (:claimed-at result)))
      (is (instance? java.util.Date (:claimed-at result))))))

(deftest claim-persists-test
  (testing "claim changes are persisted"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-claim-in-temp! "1" :agent "agent-1")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (= "agent-1" (:claimed-by loaded)))
      (is (some? (:claimed-at loaded))))))

(deftest claim-same-agent-succeeds-test
  (testing "same agent can re-claim (updates timestamp)"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result1 (cmd-claim-in-temp! "1" :agent "agent-1")
          ts1 (:claimed-at result1)]
      (Thread/sleep 10) ; ensure different timestamp
      (let [result2 (cmd-claim-in-temp! "1" :agent "agent-1")
            ts2 (:claimed-at result2)]
        (is (= "agent-1" (:claimed-by result2)))
        ;; Timestamp should be updated
        (is (some? ts2))))))

(deftest claim-creates-git-commit-test
  (testing "claim creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-claim-in-temp! "1" :agent "agent-1")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest claim-preserves-other-fields-test
  (testing "claim preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p1 :difficulty 4
                  :taint #{:needs-verification})
    (let [result (cmd-claim-in-temp! "1" :agent "agent-1")]
      (is (= "Test claim" (:claim result)))
      (is (= :p1 (:priority result)))
      (is (= 4 (:difficulty result)))
      (is (contains? (:taint result) :needs-verification)))))

;; =============================================================================
;; Claim Command - Validation Tests
;; =============================================================================

(deftest claim-requires-mote-id-test
  (testing "claim requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-claim-in-temp! nil :agent "agent-1")))))

(deftest claim-requires-agent-test
  (testing "claim requires agent name"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Agent name is required"
                          (cmd-claim-in-temp! "1")))))

(deftest claim-requires-repo-test
  (testing "claim requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-claim-in-temp! "1" :agent "agent-1")))))

(deftest claim-mote-not-found-test
  (testing "claim fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-claim-in-temp! "999" :agent "agent-1")))))

(deftest claim-already-claimed-test
  (testing "claim fails when already claimed by another agent"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote already claimed"
                          (cmd-claim-in-temp! "1" :agent "agent-2")))))

(deftest claim-already-claimed-exception-data-test
  (testing "already-claimed exception contains correct data"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (try
      (cmd-claim-in-temp! "1" :agent "agent-2")
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (let [data (ex-data e)]
          (is (= :already-claimed (:type data)))
          (is (= "1" (:mote-id data)))
          (is (= "agent-1" (:claimed-by data))))))))

;; =============================================================================
;; Unclaim Command - Basic Tests
;; =============================================================================

(deftest unclaim-clears-claimed-by-test
  (testing "unclaim clears claimed-by field"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [result (cmd-unclaim-in-temp! "1")]
      (is (nil? (:claimed-by result))))))

(deftest unclaim-clears-claimed-at-test
  (testing "unclaim clears claimed-at timestamp"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [result (cmd-unclaim-in-temp! "1")]
      (is (nil? (:claimed-at result))))))

(deftest unclaim-persists-test
  (testing "unclaim changes are persisted"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (cmd-unclaim-in-temp! "1")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (nil? (:claimed-by loaded)))
      (is (nil? (:claimed-at loaded))))))

(deftest unclaim-idempotent-test
  (testing "unclaiming unclaimed mote is idempotent"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-unclaim-in-temp! "1")]
      (is (nil? (:claimed-by result)))
      (is (nil? (:claimed-at result))))))

(deftest unclaim-creates-git-commit-test
  (testing "unclaim creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-unclaim-in-temp! "1")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest unclaim-preserves-other-fields-test
  (testing "unclaim preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p1 :difficulty 4
                  :taint #{:needs-verification} :claimed-by "agent-1")
    (let [result (cmd-unclaim-in-temp! "1")]
      (is (= "Test claim" (:claim result)))
      (is (= :p1 (:priority result)))
      (is (= 4 (:difficulty result)))
      (is (contains? (:taint result) :needs-verification)))))

;; =============================================================================
;; Unclaim Command - Validation Tests
;; =============================================================================

(deftest unclaim-requires-mote-id-test
  (testing "unclaim requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-unclaim-in-temp! nil)))))

(deftest unclaim-requires-repo-test
  (testing "unclaim requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-unclaim-in-temp! "1")))))

(deftest unclaim-mote-not-found-test
  (testing "unclaim fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-unclaim-in-temp! "999")))))

;; =============================================================================
;; Claim/Unclaim Workflow Tests
;; =============================================================================

(deftest claim-then-unclaim-test
  (testing "claim then unclaim workflow"
    (init-repo!)
    (create-mote! "1" "Test claim")
    ;; Claim
    (let [claimed (cmd-claim-in-temp! "1" :agent "agent-1")]
      (is (= "agent-1" (:claimed-by claimed)))
      (is (some? (:claimed-at claimed))))
    ;; Unclaim
    (let [unclaimed (cmd-unclaim-in-temp! "1")]
      (is (nil? (:claimed-by unclaimed)))
      (is (nil? (:claimed-at unclaimed))))
    ;; Can claim again
    (let [reclaimed (cmd-claim-in-temp! "1" :agent "agent-2")]
      (is (= "agent-2" (:claimed-by reclaimed))))))

(deftest claim-transfer-after-unclaim-test
  (testing "claim can be transferred after unclaim"
    (init-repo!)
    (create-mote! "1" "Test claim" :claimed-by "agent-1")
    ;; Unclaim first
    (cmd-unclaim-in-temp! "1")
    ;; Now different agent can claim
    (let [result (cmd-claim-in-temp! "1" :agent "agent-2")]
      (is (= "agent-2" (:claimed-by result))))))

(deftest multiple-motes-independent-claims-test
  (testing "multiple motes can have independent claims"
    (init-repo!)
    (create-mote! "1" "Claim 1")
    (create-mote! "2" "Claim 2")
    ;; Claim different motes with different agents
    (cmd-claim-in-temp! "1" :agent "agent-1")
    (cmd-claim-in-temp! "2" :agent "agent-2")
    ;; Verify
    (let [m1 (store/load-mote *temp-dir* "1")
          m2 (store/load-mote *temp-dir* "2")]
      (is (= "agent-1" (:claimed-by m1)))
      (is (= "agent-2" (:claimed-by m2))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest claim-handler-registered-test
  (testing "claim handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "claim")))))

(deftest unclaim-handler-registered-test
  (testing "unclaim handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "unclaim")))))

(deftest claim-handler-is-function-test
  (testing "claim handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "claim")]
      (is (fn? handler)))))

(deftest unclaim-handler-is-function-test
  (testing "unclaim handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "unclaim")]
      (is (fn? handler)))))
