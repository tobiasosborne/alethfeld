(ns alethfeld.cmd.show-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.mote :as mote]
            [alethfeld.cli :as cli]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-show-test-"})]
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
  "Initialize a test repository."
  []
  (store/init-repo! *temp-dir*))

(defn- create-test-mote
  "Create and save a test mote."
  [& {:keys [id claim status priority difficulty parent children]
      :or {id "1"
           claim "Test claim"
           status :fixed
           priority :p2
           difficulty 3
           parent nil
           children []}}]
  (let [m (-> (mote/make-mote id claim "test-agent"
                              :status status
                              :priority priority
                              :difficulty difficulty)
              (assoc :parent parent
                     :children children))]
    (store/save-mote! *temp-dir* m)
    m))

(defn- show-mote
  "Call show command for a mote in the temp directory.
   Since cmd-show uses '.' we need to directly test the underlying logic."
  [id]
  (let [mote (store/load-mote *temp-dir* id)]
    (if mote
      mote
      (throw (ex-info "Mote not found"
                      {:type :not-found
                       :mote-id id})))))

;; =============================================================================
;; Basic Show Tests
;; =============================================================================

(deftest show-returns-mote-test
  (testing "show returns the mote data"
    (init-test-repo)
    (create-test-mote :id "1" :claim "My claim")
    (let [result (show-mote "1")]
      (is (map? result))
      (is (= "1" (:id result)))
      (is (= "My claim" (:claim result))))))

(deftest show-returns-all-fields-test
  (testing "show returns all mote fields"
    (init-test-repo)
    (create-test-mote :id "1"
                      :claim "Test claim"
                      :status :fixed
                      :priority :p1
                      :difficulty 4)
    (let [result (show-mote "1")]
      (is (= "1" (:id result)))
      (is (= "Test claim" (:claim result)))
      (is (= :fixed (:status result)))
      (is (= :p1 (:priority result)))
      (is (= 4 (:difficulty result)))
      (is (= "test-agent" (:created-by result))))))

;; =============================================================================
;; Hierarchical ID Tests
;; =============================================================================

(deftest show-child-mote-test
  (testing "show finds child mote by hierarchical ID"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root")
    (create-test-mote :id "1.1" :claim "Child" :parent "1")
    (let [result (show-mote "1.1")]
      (is (= "1.1" (:id result)))
      (is (= "Child" (:claim result)))
      (is (= "1" (:parent result))))))

(deftest show-nested-child-test
  (testing "show finds deeply nested mote"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root")
    (create-test-mote :id "1.2" :claim "Level 2" :parent "1")
    (create-test-mote :id "1.2.3" :claim "Level 3" :parent "1.2")
    (let [result (show-mote "1.2.3")]
      (is (= "1.2.3" (:id result)))
      (is (= "Level 3" (:claim result))))))

;; =============================================================================
;; Proposed Mote Tests
;; =============================================================================

(deftest show-proposed-mote-test
  (testing "show finds proposed motes"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Root")
    (create-test-mote :id "1.1" :claim "Proposed child" :status :proposed :parent "1")
    (let [result (show-mote "1.1")]
      (is (= "1.1" (:id result)))
      (is (= :proposed (:status result))))))

;; =============================================================================
;; Multiple Root Tests
;; =============================================================================

(deftest show-second-root-test
  (testing "show finds motes with different root IDs"
    (init-test-repo)
    (create-test-mote :id "1" :claim "First root")
    (create-test-mote :id "2" :claim "Second root")
    (let [result1 (show-mote "1")
          result2 (show-mote "2")]
      (is (= "1" (:id result1)))
      (is (= "2" (:id result2)))
      (is (= "First root" (:claim result1)))
      (is (= "Second root" (:claim result2))))))

;; =============================================================================
;; Vote and Assumption Tests
;; =============================================================================

(deftest show-mote-with-votes-test
  (testing "show returns mote with votes"
    (init-test-repo)
    (let [m (mote/make-mote "1" "Voted claim" "agent-1")
          vote (mote/make-vote "verifier-1" :for :reason "Looks correct")
          with-vote (mote/add-vote m vote)]
      (store/save-mote! *temp-dir* with-vote)
      (let [result (show-mote "1")]
        (is (seq (:votes result)))
        (is (= "verifier-1" (get-in result [:votes 0 :agent])))))))

(deftest show-mote-with-assumptions-test
  (testing "show returns mote with assumptions"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Base claim")
    (let [m (mote/make-mote "2" "Dependent claim" "agent-1")
          with-assumption (mote/add-assumption m {:type :internal :ref "1" :note "Uses base"})]
      (store/save-mote! *temp-dir* with-assumption)
      (let [result (show-mote "2")]
        (is (seq (:assumptions result)))
        (is (= "1" (get-in result [:assumptions 0 :ref])))))))

(deftest show-mote-with-definitions-test
  (testing "show returns mote with definitions"
    (init-test-repo)
    (let [m (mote/make-mote "1" "Claim with defs" "agent-1")
          with-def (mote/add-definition m {:symbol "epsilon" :meaning "small positive number"})]
      (store/save-mote! *temp-dir* with-def)
      (let [result (show-mote "1")]
        (is (seq (:definitions result)))
        (is (= "epsilon" (get-in result [:definitions 0 :symbol])))))))

;; =============================================================================
;; Claim/Work Tracking Tests
;; =============================================================================

(deftest show-claimed-mote-test
  (testing "show returns claim info"
    (init-test-repo)
    (let [m (mote/make-mote "1" "Claimed claim" "agent-1")
          claimed (mote/set-claimed-by m "worker-1")]
      (store/save-mote! *temp-dir* claimed)
      (let [result (show-mote "1")]
        (is (= "worker-1" (:claimed-by result)))
        (is (inst? (:claimed-at result)))))))

;; =============================================================================
;; Taint Tests
;; =============================================================================

(deftest show-mote-with-taints-test
  (testing "show returns taint flags"
    (init-test-repo)
    (let [m (mote/make-mote "1" "Tainted claim" "agent-1")
          tainted (-> m
                      (mote/add-taint :needs-verification)
                      (mote/add-taint :needs-refs))]
      (store/save-mote! *temp-dir* tainted)
      (let [result (show-mote "1")]
        (is (contains? (:taint result) :needs-verification))
        (is (contains? (:taint result) :needs-refs))))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest show-not-found-test
  (testing "show throws for non-existent mote"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (show-mote "999")))))

(deftest show-not-found-error-type-test
  (testing "show throws with :not-found type"
    (init-test-repo)
    (try
      (show-mote "nonexistent")
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (is (= :not-found (:type (ex-data e))))
        (is (= "nonexistent" (:mote-id (ex-data e))))))))

(deftest show-empty-id-test
  (testing "show throws for empty ID"
    (init-test-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (show-mote "")))))

;; =============================================================================
;; CLI Integration Tests
;; =============================================================================

(deftest show-handler-registered-test
  (testing "show handler is registered"
    (cmd/register-handlers!)
    ;; Deref var, then deref atom
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "show")))))

(deftest show-handler-is-function-test
  (testing "show handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "show")]
      (is (fn? handler)))))

;; =============================================================================
;; Data Integrity Tests
;; =============================================================================

(deftest show-returns-exact-stored-data-test
  (testing "show returns exactly what was stored"
    (init-test-repo)
    (let [original (mote/make-mote "1" "Original claim" "creator"
                                   :priority :p0
                                   :difficulty 5)]
      (store/save-mote! *temp-dir* original)
      (let [result (show-mote "1")]
        ;; Compare key fields - timestamps may differ slightly
        (is (= (:id original) (:id result)))
        (is (= (:claim original) (:claim result)))
        (is (= (:priority original) (:priority result)))
        (is (= (:difficulty original) (:difficulty result)))
        (is (= (:created-by original) (:created-by result)))))))

(deftest show-preserves-children-list-test
  (testing "show preserves children list"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Parent" :children ["1.1" "1.2"])
    (let [result (show-mote "1")]
      (is (= ["1.1" "1.2"] (:children result))))))

;; =============================================================================
;; Timestamp Tests
;; =============================================================================

(deftest show-includes-timestamps-test
  (testing "show includes timestamp fields"
    (init-test-repo)
    (create-test-mote :id "1" :claim "Timestamped")
    (let [result (show-mote "1")]
      (is (inst? (:created-at result)))
      (is (inst? (:updated-at result))))))
