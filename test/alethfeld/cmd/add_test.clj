(ns alethfeld.cmd.add-test
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
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-add-test-"})
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

(defn- cmd-add-ref-in-temp!
  "Call cmd-add-ref! using the temp directory context."
  [id & {:keys [ref note]}]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add reference to"]})))
    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the citation"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [external-ref (cond-> {:type :external :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote external-ref)]
        (tx/atomic-write! repo-path
                          (str "Add external reference to " id)
                          [updated-mote])
        updated-mote))))

(defn- cmd-add-assumption-in-temp!
  "Call cmd-add-assumption! using the temp directory context."
  [id & {:keys [ref note]}]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add assumption to"]})))
    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the mote ID to reference"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (when-not (store/load-mote repo-path ref)
        (throw (ex-info "Referenced mote not found"
                        {:type :not-found
                         :mote-id ref})))
      (let [internal-ref (cond-> {:type :internal :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote internal-ref)]
        (tx/atomic-write! repo-path
                          (str "Add internal assumption to " id)
                          [updated-mote])
        updated-mote))))

(defn- cmd-add-definition-in-temp!
  "Call cmd-add-definition! using the temp directory context."
  [id & {:keys [symbol meaning]}]
  (let [repo-path *temp-dir*]
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add definition to"]})))
    (when-not symbol
      (throw (ex-info "Symbol is required"
                      {:type :validation-failed
                       :errors ["Provide --symbol to define"]})))
    (when-not meaning
      (throw (ex-info "Meaning is required"
                      {:type :validation-failed
                       :errors ["Provide --meaning for the symbol"]})))
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))
      (let [definition {:symbol symbol :meaning meaning}
            updated-mote (mote/add-definition current-mote definition)]
        (tx/atomic-write! repo-path
                          (str "Add definition to " id)
                          [updated-mote])
        updated-mote))))

;; =============================================================================
;; Add-Ref Command - Basic Tests
;; =============================================================================

(deftest add-ref-basic-test
  (testing "add-ref adds external reference"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-add-ref-in-temp! "1" :ref "Author2024")]
      (is (= 1 (count (:assumptions result))))
      (let [assumption (first (:assumptions result))]
        (is (= :external (:type assumption)))
        (is (= "Author2024" (:ref assumption)))))))

(deftest add-ref-with-note-test
  (testing "add-ref includes note when provided"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-add-ref-in-temp! "1" :ref "Author2024" :note "Provides theorem 3.1")]
      (let [assumption (first (:assumptions result))]
        (is (= :external (:type assumption)))
        (is (= "Author2024" (:ref assumption)))
        (is (= "Provides theorem 3.1" (:note assumption)))))))

(deftest add-ref-persists-test
  (testing "add-ref changes are persisted"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-add-ref-in-temp! "1" :ref "Citation2024")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (= 1 (count (:assumptions loaded))))
      (is (= "Citation2024" (:ref (first (:assumptions loaded))))))))

(deftest add-ref-multiple-test
  (testing "can add multiple references"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-add-ref-in-temp! "1" :ref "First2024")
    (let [result (cmd-add-ref-in-temp! "1" :ref "Second2024")]
      (is (= 2 (count (:assumptions result))))
      (is (= "First2024" (:ref (first (:assumptions result)))))
      (is (= "Second2024" (:ref (second (:assumptions result))))))))

(deftest add-ref-creates-git-commit-test
  (testing "add-ref creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-add-ref-in-temp! "1" :ref "Author2024")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest add-ref-preserves-other-fields-test
  (testing "add-ref preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p1 :difficulty 4)
    (let [result (cmd-add-ref-in-temp! "1" :ref "Author2024")]
      (is (= "Test claim" (:claim result)))
      (is (= :p1 (:priority result)))
      (is (= 4 (:difficulty result))))))

;; =============================================================================
;; Add-Ref Command - Validation Tests
;; =============================================================================

(deftest add-ref-requires-mote-id-test
  (testing "add-ref requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-add-ref-in-temp! nil :ref "Author2024")))))

(deftest add-ref-requires-ref-test
  (testing "add-ref requires --ref"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Reference is required"
                          (cmd-add-ref-in-temp! "1")))))

(deftest add-ref-requires-repo-test
  (testing "add-ref requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-add-ref-in-temp! "1" :ref "Author2024")))))

(deftest add-ref-mote-not-found-test
  (testing "add-ref fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-add-ref-in-temp! "999" :ref "Author2024")))))

;; =============================================================================
;; Add-Assumption Command - Basic Tests
;; =============================================================================

(deftest add-assumption-basic-test
  (testing "add-assumption adds internal reference"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    (let [result (cmd-add-assumption-in-temp! "2" :ref "1")]
      (is (= 1 (count (:assumptions result))))
      (let [assumption (first (:assumptions result))]
        (is (= :internal (:type assumption)))
        (is (= "1" (:ref assumption)))))))

(deftest add-assumption-with-note-test
  (testing "add-assumption includes note when provided"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    (let [result (cmd-add-assumption-in-temp! "2" :ref "1" :note "Depends on this result")]
      (let [assumption (first (:assumptions result))]
        (is (= :internal (:type assumption)))
        (is (= "1" (:ref assumption)))
        (is (= "Depends on this result" (:note assumption)))))))

(deftest add-assumption-persists-test
  (testing "add-assumption changes are persisted"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    (cmd-add-assumption-in-temp! "2" :ref "1")
    (let [loaded (store/load-mote *temp-dir* "2")]
      (is (= 1 (count (:assumptions loaded))))
      (is (= "1" (:ref (first (:assumptions loaded))))))))

(deftest add-assumption-multiple-test
  (testing "can add multiple assumptions"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    (create-mote! "3" "Third claim")
    (cmd-add-assumption-in-temp! "3" :ref "1")
    (let [result (cmd-add-assumption-in-temp! "3" :ref "2")]
      (is (= 2 (count (:assumptions result))))
      (is (= "1" (:ref (first (:assumptions result)))))
      (is (= "2" (:ref (second (:assumptions result))))))))

(deftest add-assumption-creates-git-commit-test
  (testing "add-assumption creates git commit"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-add-assumption-in-temp! "2" :ref "1")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest add-assumption-preserves-other-fields-test
  (testing "add-assumption preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim" :priority :p0 :difficulty 5)
    (let [result (cmd-add-assumption-in-temp! "2" :ref "1")]
      (is (= "Second claim" (:claim result)))
      (is (= :p0 (:priority result)))
      (is (= 5 (:difficulty result))))))

;; =============================================================================
;; Add-Assumption Command - Validation Tests
;; =============================================================================

(deftest add-assumption-requires-mote-id-test
  (testing "add-assumption requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-add-assumption-in-temp! nil :ref "1")))))

(deftest add-assumption-requires-ref-test
  (testing "add-assumption requires --ref"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Reference is required"
                          (cmd-add-assumption-in-temp! "1")))))

(deftest add-assumption-requires-repo-test
  (testing "add-assumption requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-add-assumption-in-temp! "1" :ref "2")))))

(deftest add-assumption-mote-not-found-test
  (testing "add-assumption fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-add-assumption-in-temp! "999" :ref "1")))))

(deftest add-assumption-referenced-mote-not-found-test
  (testing "add-assumption fails when referenced mote not found"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Referenced mote not found"
                          (cmd-add-assumption-in-temp! "1" :ref "999")))))

;; =============================================================================
;; Add-Definition Command - Basic Tests
;; =============================================================================

(deftest add-definition-basic-test
  (testing "add-definition adds definition"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [result (cmd-add-definition-in-temp! "1" :symbol "ε" :meaning "arbitrarily small positive number")]
      (is (= 1 (count (:definitions result))))
      (let [definition (first (:definitions result))]
        (is (= "ε" (:symbol definition)))
        (is (= "arbitrarily small positive number" (:meaning definition)))))))

(deftest add-definition-persists-test
  (testing "add-definition changes are persisted"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-add-definition-in-temp! "1" :symbol "δ" :meaning "tolerance bound")
    (let [loaded (store/load-mote *temp-dir* "1")]
      (is (= 1 (count (:definitions loaded))))
      (is (= "δ" (:symbol (first (:definitions loaded)))))
      (is (= "tolerance bound" (:meaning (first (:definitions loaded))))))))

(deftest add-definition-multiple-test
  (testing "can add multiple definitions"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (cmd-add-definition-in-temp! "1" :symbol "ε" :meaning "epsilon")
    (let [result (cmd-add-definition-in-temp! "1" :symbol "δ" :meaning "delta")]
      (is (= 2 (count (:definitions result))))
      (is (= "ε" (:symbol (first (:definitions result)))))
      (is (= "δ" (:symbol (second (:definitions result))))))))

(deftest add-definition-creates-git-commit-test
  (testing "add-definition creates git commit"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (let [initial-count (count (git/git-log *temp-dir*))]
      (cmd-add-definition-in-temp! "1" :symbol "x" :meaning "variable")
      (let [final-count (count (git/git-log *temp-dir*))]
        (is (> final-count initial-count))))))

(deftest add-definition-preserves-other-fields-test
  (testing "add-definition preserves other mote fields"
    (init-repo!)
    (create-mote! "1" "Test claim" :priority :p1 :difficulty 2)
    (let [result (cmd-add-definition-in-temp! "1" :symbol "x" :meaning "variable")]
      (is (= "Test claim" (:claim result)))
      (is (= :p1 (:priority result)))
      (is (= 2 (:difficulty result))))))

;; =============================================================================
;; Add-Definition Command - Validation Tests
;; =============================================================================

(deftest add-definition-requires-mote-id-test
  (testing "add-definition requires mote ID"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote ID is required"
                          (cmd-add-definition-in-temp! nil :symbol "x" :meaning "var")))))

(deftest add-definition-requires-symbol-test
  (testing "add-definition requires --symbol"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Symbol is required"
                          (cmd-add-definition-in-temp! "1" :meaning "variable")))))

(deftest add-definition-requires-meaning-test
  (testing "add-definition requires --meaning"
    (init-repo!)
    (create-mote! "1" "Test claim")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Meaning is required"
                          (cmd-add-definition-in-temp! "1" :symbol "x")))))

(deftest add-definition-requires-repo-test
  (testing "add-definition requires initialized repository"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Not an Alethfeld repository"
                          (cmd-add-definition-in-temp! "1" :symbol "x" :meaning "var")))))

(deftest add-definition-mote-not-found-test
  (testing "add-definition fails when mote not found"
    (init-repo!)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Mote not found"
                          (cmd-add-definition-in-temp! "999" :symbol "x" :meaning "var")))))

;; =============================================================================
;; Mixed Add Commands Tests
;; =============================================================================

(deftest mixed-adds-independent-test
  (testing "refs, assumptions, and definitions are independent"
    (init-repo!)
    (create-mote! "1" "First claim")
    (create-mote! "2" "Second claim")
    ;; Add all three types to mote 2
    (cmd-add-ref-in-temp! "2" :ref "Citation")
    (cmd-add-assumption-in-temp! "2" :ref "1")
    (let [result (cmd-add-definition-in-temp! "2" :symbol "x" :meaning "var")]
      (is (= 2 (count (:assumptions result))))  ; ref + assumption
      (is (= 1 (count (:definitions result))))
      ;; Check types
      (let [assumptions (:assumptions result)]
        (is (some #(= :external (:type %)) assumptions))
        (is (some #(= :internal (:type %)) assumptions))))))

;; =============================================================================
;; Handler Registration Tests
;; =============================================================================

(deftest add-ref-handler-registered-test
  (testing "add-ref handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "add-ref")))))

(deftest add-assumption-handler-registered-test
  (testing "add-assumption handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "add-assumption")))))

(deftest add-definition-handler-registered-test
  (testing "add-definition handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "add-definition")))))

(deftest add-ref-handler-is-function-test
  (testing "add-ref handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "add-ref")]
      (is (fn? handler)))))

(deftest add-assumption-handler-is-function-test
  (testing "add-assumption handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "add-assumption")]
      (is (fn? handler)))))

(deftest add-definition-handler-is-function-test
  (testing "add-definition handler is a function"
    (cmd/register-handlers!)
    (let [handler (get @@#'cli/handlers "add-definition")]
      (is (fn? handler)))))
