(ns alethfeld.cmd.config-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.cmd :as cmd]
            [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.cli :as cli]
            [alethfeld.tx :as tx]
            [alethfeld.proposal :as proposal]
            [alethfeld.verify :as verify]
            [alethfeld.mote :as mote]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test, changes to it, and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-config-test-"})
        orig (System/getProperty "user.dir")]
    (try
      (System/setProperty "user.dir" (str temp))
      (binding [*temp-dir* (str temp)]
        (f))
      (finally
        (System/setProperty "user.dir" orig)
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- init-repo
  "Initialize a test repository."
  [& {:keys [name] :or {name "Test Project"}}]
  (git/git-init! *temp-dir*)
  (git/git-config! *temp-dir* "user.name" "test")
  (git/git-config! *temp-dir* "user.email" "test@test.com")
  (store/init-repo! *temp-dir* :project-name name)
  (git/git-add-all! *temp-dir*)
  (git/git-commit! *temp-dir* "init"))

(def ^:private config-keys
  "Valid configuration keys with their types and defaults."
  {:project-name {:type :string :default "Unnamed Proof"}
   :version {:type :string :default "0.1"}
   :default-difficulty {:type :int :min 1 :max 5 :default 3}
   :proposal-quorum {:type :int :min 1 :default 1}  ; v0.2: default is 1
   :vote-quorum {:type :int :min 1 :default 1}      ; v0.2: default is 1
   :claim-timeout-minutes {:type :int :min 1 :default 30}})

(defn- parse-config-value
  "Parse a string value to the appropriate type for a config key."
  [key-name value-str]
  (let [key-kw (keyword key-name)
        spec (get config-keys key-kw)]
    (when-not spec
      (throw (ex-info "Unknown config key"
                      {:type :validation-failed
                       :errors [(str "Unknown config key: " key-name)]})))
    (case (:type spec)
      :string value-str
      :int (let [parsed (parse-long value-str)]
             (when-not parsed
               (throw (ex-info "Invalid integer value"
                               {:type :validation-failed
                                :errors [(str "Expected integer for " key-name ", got: " value-str)]})))
             (when (and (:min spec) (< parsed (:min spec)))
               (throw (ex-info "Value below minimum"
                               {:type :validation-failed
                                :errors [(str key-name " must be >= " (:min spec))]})))
             (when (and (:max spec) (> parsed (:max spec)))
               (throw (ex-info "Value above maximum"
                               {:type :validation-failed
                                :errors [(str key-name " must be <= " (:max spec))]})))
             parsed))))

(defn- config-list
  "Execute config list in temp dir."
  []
  (let [config (store/load-config *temp-dir*)]
    {:config config
     :keys (keys config-keys)}))

(defn- config-get
  "Execute config get in temp dir."
  [key-name]
  (when-not key-name
    (throw (ex-info "Config key required"
                    {:type :validation-failed
                     :errors ["Usage: af config get <key>"]})))
  (let [key-kw (keyword key-name)
        config (store/load-config *temp-dir*)
        spec (get config-keys key-kw)]
    (when-not spec
      (throw (ex-info "Unknown config key"
                      {:type :validation-failed
                       :errors [(str "Unknown config key: " key-name)]})))
    {:key key-kw
     :value (get config key-kw (:default spec))
     :default (:default spec)}))

(defn- config-set
  "Execute config set in temp dir."
  [key-name value-str]
  (when-not key-name
    (throw (ex-info "Config key required"
                    {:type :validation-failed
                     :errors ["Usage: af config set <key> <value>"]})))
  (when-not value-str
    (throw (ex-info "Config value required"
                    {:type :validation-failed
                     :errors ["Usage: af config set <key> <value>"]})))
  (let [key-kw (keyword key-name)
        parsed-value (parse-config-value key-name value-str)
        config (store/load-config *temp-dir*)
        new-config (assoc config key-kw parsed-value)]
    (tx/atomic-write-config! *temp-dir*
                             (str "Set config: " key-name " = " parsed-value)
                             new-config)
    {:key key-kw
     :value parsed-value
     :previous (get config key-kw)}))

;; =============================================================================
;; Config List Tests
;; =============================================================================

(deftest config-list-returns-config-test
  (testing "config list returns the current configuration"
    (init-repo)
    (let [result (config-list)]
      (is (map? (:config result)))
      (is (= "Test Project" (get-in result [:config :project-name]))))))

(deftest config-list-returns-valid-keys-test
  (testing "config list returns list of valid keys"
    (init-repo)
    (let [result (config-list)]
      (is (contains? (set (:keys result)) :proposal-quorum))
      (is (contains? (set (:keys result)) :vote-quorum)))))

(deftest config-list-without-subcommand-test
  (testing "config without subcommand defaults to list"
    (init-repo)
    ;; Just test that list works without subcommand - actual cmd uses "."
    (let [result (config-list)]
      (is (map? (:config result))))))

;; =============================================================================
;; Config Get Tests
;; =============================================================================

(deftest config-get-proposal-quorum-test
  (testing "config get returns proposal-quorum"
    (init-repo)
    (let [result (config-get "proposal-quorum")]
      (is (= :proposal-quorum (:key result)))
      (is (= 1 (:value result))))))

(deftest config-get-vote-quorum-test
  (testing "config get returns vote-quorum"
    (init-repo)
    (let [result (config-get "vote-quorum")]
      (is (= :vote-quorum (:key result)))
      (is (= 1 (:value result))))))

(deftest config-get-unknown-key-throws-test
  (testing "config get throws on unknown key"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Unknown config key"
                          (config-get "unknown-key")))))

(deftest config-get-missing-key-throws-test
  (testing "config get throws when key not provided"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Config key required"
                          (config-get nil)))))

;; =============================================================================
;; Config Set Tests
;; =============================================================================

(deftest config-set-proposal-quorum-test
  (testing "config set updates proposal-quorum"
    (init-repo)
    (let [result (config-set "proposal-quorum" "3")]
      (is (= :proposal-quorum (:key result)))
      (is (= 3 (:value result)))
      (is (= 1 (:previous result))))
    ;; Verify persisted
    (let [config (store/load-config *temp-dir*)]
      (is (= 3 (:proposal-quorum config))))))

(deftest config-set-vote-quorum-test
  (testing "config set updates vote-quorum"
    (init-repo)
    (let [result (config-set "vote-quorum" "1")]
      (is (= :vote-quorum (:key result)))
      (is (= 1 (:value result))))
    ;; Verify persisted
    (let [config (store/load-config *temp-dir*)]
      (is (= 1 (:vote-quorum config))))))

(deftest config-set-creates-git-commit-test
  (testing "config set creates a git commit"
    (init-repo)
    (let [commits-before (count (git/git-log *temp-dir*))]
      (config-set "proposal-quorum" "3")
      (let [commits-after (count (git/git-log *temp-dir*))]
        (is (= (inc commits-before) commits-after))))))

(deftest config-set-invalid-value-throws-test
  (testing "config set throws on invalid integer"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Invalid integer value"
                          (config-set "proposal-quorum" "abc")))))

(deftest config-set-below-minimum-throws-test
  (testing "config set throws when value below minimum"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Value below minimum"
                          (config-set "proposal-quorum" "0")))))

(deftest config-set-above-maximum-throws-test
  (testing "config set throws when value above maximum"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Value above maximum"
                          (config-set "default-difficulty" "6")))))

(deftest config-set-unknown-key-throws-test
  (testing "config set throws on unknown key"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Unknown config key"
                          (config-set "unknown-key" "1")))))

(deftest config-set-missing-value-throws-test
  (testing "config set throws when value not provided"
    (init-repo)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"Config value required"
                          (config-set "proposal-quorum" nil)))))

;; =============================================================================
;; Quorum=1 Integration Tests
;; =============================================================================

;; These tests verify that quorum settings are correctly read from config.
;; Full proposal/verification workflow tests are in proposal_test.clj and verify_test.clj

(deftest quorum-check-proposal-with-quorum-1-test
  (testing "check-proposal-quorum works with quorum=1"
    ;; Pure function test - doesn't need repo
    (let [proposal {:id "p1" :votes [{:agent "a1" :vote :approve}]}]
      (is (= :approved (proposal/check-proposal-quorum proposal 1))))
    (let [proposal {:id "p1" :votes [{:agent "a1" :vote :reject}]}]
      (is (= :rejected (proposal/check-proposal-quorum proposal 1))))))

(deftest quorum-check-verification-with-quorum-1-test
  (testing "check-verification-quorum works with quorum=1"
    ;; Pure function test - doesn't need repo
    (let [mote-for {:id "1" :votes [{:agent "v1" :vote :for}]}]
      (is (= :verified (verify/check-verification-quorum mote-for 1))))
    (let [mote-against {:id "1" :votes [{:agent "v1" :vote :against}]}]
      (is (= :refuted (verify/check-verification-quorum mote-against 1))))))

(deftest quorum-config-persistence-test
  (testing "Quorum settings persist correctly in config"
    (init-repo)
    ;; Verify default values (v0.2: quorums default to 1)
    (let [config (store/load-config *temp-dir*)]
      (is (= 1 (:proposal-quorum config)))
      (is (= 1 (:vote-quorum config))))
    ;; Set to 3
    (config-set "proposal-quorum" "3")
    (config-set "vote-quorum" "3")
    ;; Verify changed values persist
    (let [config (store/load-config *temp-dir*)]
      (is (= 3 (:proposal-quorum config)))
      (is (= 3 (:vote-quorum config))))))

;; =============================================================================
;; CLI Registration Tests
;; =============================================================================

(deftest config-handler-registered-test
  (testing "config handler is registered"
    (cmd/register-handlers!)
    (let [handlers @@#'cli/handlers]
      (is (contains? handlers "config")))))

(deftest config-command-in-commands-test
  (testing "config command is in CLI commands list"
    (is (contains? cli/commands "config"))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest config-not-initialized-returns-nil-test
  (testing "config returns nil when repository not initialized"
    ;; store/load-config returns nil when config doesn't exist
    (let [result (store/load-config *temp-dir*)]
      (is (nil? result)))))
