(ns alethfeld.middleware-test
  "Tests for session enforcement middleware."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.middleware :as middleware]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.git :as git]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-middleware-test-"})]
    (try
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
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
  (session/ensure-session-dirs! *temp-dir*)
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "Initialize"))

(defn- create-mote!
  "Create a mote directly in the store for test setup."
  [id claim & {:keys [taint] :or {taint #{:needs-verification}}}]
  (let [m (mote/make-mote id claim "test-agent"
                          :difficulty 3
                          :priority :p2
                          :taint taint
                          :status :fixed)]
    (store/save-mote! *temp-dir* m)
    (git/git-add-all! *temp-dir*)
    (git/git-commit! *temp-dir* (str "Create mote " id))
    m))

;; -----------------------------------------------------------------------------
;; wrap-session-enforcement Tests
;; -----------------------------------------------------------------------------

(deftest wrap-session-enforcement-passes-valid-session
  (testing "middleware passes valid session to handler"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [sess (session/create-session! *temp-dir* "1" :proposer "agent1")
          session-id (:session-id sess)
          ;; Track what the handler receives
          received (atom nil)
          handler (fn [ctx]
                    (reset! received ctx)
                    {:result "ok"})
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      ;; Call wrapped handler
      (wrapped {:id "1" :options {:session session-id}})
      ;; Verify handler received validated session
      (is (some? (:validated-session @received)))
      (is (= session-id (:session-id (:validated-session @received)))))))

(deftest wrap-session-enforcement-throws-for-invalid-session
  (testing "middleware throws for non-existent session"
    (init-repo!)
    (let [handler (fn [_ctx] {:result "ok"})
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid session"
            (wrapped {:id "1" :options {:session "fake-session-id"}}))))))

(deftest wrap-session-enforcement-throws-for-wrong-mote
  (testing "middleware throws when session is for different mote"
    (init-repo!)
    (create-mote! "1" "Test claim 1")
    (create-mote! "2" "Test claim 2")
    (let [sess (session/create-session! *temp-dir* "1" :proposer "agent1")
          session-id (:session-id sess)
          handler (fn [_ctx] {:result "ok"})
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Session locked to different mote"
            (wrapped {:id "2" :options {:session session-id}}))))))

(deftest wrap-session-enforcement-throws-for-unauthorized-action
  (testing "middleware throws when role cannot perform action"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [;; Create advisor session (can only approve/reject)
          sess (session/create-session! *temp-dir* "1" :advisor "agent1")
          session-id (:session-id sess)
          handler (fn [_ctx] {:result "ok"})
          ;; Try to propose with advisor role
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Action not allowed for role"
            (wrapped {:id "1" :options {:session session-id}}))))))

(deftest wrap-session-enforcement-validate-only-skips-role-check
  (testing "validate-only mode skips role permission check"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [;; Create advisor session
          sess (session/create-session! *temp-dir* "1" :advisor "agent1")
          session-id (:session-id sess)
          received (atom nil)
          handler (fn [ctx]
                    (reset! received ctx)
                    {:result "ok"})
          ;; Use validate-only mode - should pass even though action doesn't match role
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :validate-only true
                                                       :repo-path *temp-dir*)]
      ;; Should not throw - validate-only doesn't check role permissions
      (wrapped {:id "1" :options {:session session-id}})
      (is (some? (:validated-session @received))))))

(deftest wrap-session-enforcement-passes-through-without-session
  (testing "middleware passes through when no session provided"
    (init-repo!)
    (let [received (atom nil)
          handler (fn [ctx]
                    (reset! received ctx)
                    {:result "ok"})
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      ;; Call without session - should pass through
      (wrapped {:id "1" :options {}})
      (is (nil? (:validated-session @received))))))

(deftest wrap-session-enforcement-passes-through-without-id
  (testing "middleware passes through when no mote ID provided"
    (init-repo!)
    (let [received (atom nil)
          handler (fn [ctx]
                    (reset! received ctx)
                    {:result "ok"})
          wrapped (middleware/wrap-session-enforcement handler :propose
                                                       :repo-path *temp-dir*)]
      ;; Call without ID - should pass through
      (wrapped {:options {:session "some-session"}})
      (is (nil? (:validated-session @received))))))
