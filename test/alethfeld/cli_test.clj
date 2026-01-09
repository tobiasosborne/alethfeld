(ns alethfeld.cli-test
  "Tests for CLI infrastructure."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.string :as str]
            [alethfeld.cli :as cli]))

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn capture-exit
  "Run a function and capture the exit code instead of actually exiting.
   Returns {:exit-code n :output stdout :err stderr}."
  [f]
  (let [exit-code (atom nil)
        stdout (java.io.StringWriter.)
        stderr (java.io.StringWriter.)]
    (binding [cli/*exit-fn* (fn [code] (reset! exit-code code))
              *out* stdout
              *err* stderr]
      (f))
    {:exit-code @exit-code
     :output (str stdout)
     :err (str stderr)}))

;; -----------------------------------------------------------------------------
;; Output Formatting Tests
;; -----------------------------------------------------------------------------

(deftest format-edn-test
  (testing "formats map as EDN"
    (let [result (cli/format-edn {:a 1 :b 2})]
      (is (string? result))
      (is (str/includes? result ":a"))
      (is (str/includes? result "1"))))

  (testing "formats vector as EDN"
    (let [result (cli/format-edn [1 2 3])]
      (is (str/includes? result "1"))
      (is (str/includes? result "2"))
      (is (str/includes? result "3"))))

  (testing "formats nested data"
    (let [result (cli/format-edn {:items [{:id 1} {:id 2}]})]
      (is (str/includes? result ":items"))
      (is (str/includes? result ":id")))))

(deftest format-json-test
  (testing "formats map as JSON"
    (let [result (cli/format-json {:a 1 :b 2})]
      (is (string? result))
      (is (or (str/includes? result "\"a\":1")
              (str/includes? result "\"a\": 1")
              (str/includes? result "\"a\" : 1")))))

  (testing "formats vector as JSON"
    (let [result (cli/format-json [1 2 3])]
      (is (= "[1,2,3]" result))))

  (testing "handles nested data"
    (let [result (cli/format-json {:items [{:id 1}]})]
      (is (str/includes? result "items"))
      (is (str/includes? result "id")))))

(deftest format-output-test
  (testing "defaults to EDN"
    (let [result (cli/format-output {:test 1} nil)]
      (is (str/includes? result ":test"))))

  (testing "formats as EDN when specified"
    (let [result (cli/format-output {:test 1} :edn)]
      (is (str/includes? result ":test"))))

  (testing "formats as JSON when specified"
    (let [result (cli/format-output {:test 1} :json)]
      (is (str/includes? result "\"test\"")))))

;; -----------------------------------------------------------------------------
;; Exit Handling Tests
;; -----------------------------------------------------------------------------

(deftest exit-codes-test
  (testing "exit codes are defined"
    (is (= 0 (:success cli/exit-codes)))
    (is (= 1 (:error cli/exit-codes)))
    (is (= 2 (:invalid-args cli/exit-codes)))
    (is (= 3 (:not-found cli/exit-codes)))
    (is (= 4 (:validation-error cli/exit-codes)))
    (is (= 5 (:conflict cli/exit-codes)))))

(deftest exit-function-test
  (testing "exit with keyword code"
    (let [result (capture-exit #(cli/exit! :success))]
      (is (= 0 (:exit-code result)))))

  (testing "exit with numeric code"
    (let [result (capture-exit #(cli/exit! 42))]
      (is (= 42 (:exit-code result)))))

  (testing "exit with message"
    (let [result (capture-exit #(cli/exit! :error "Something went wrong"))]
      (is (= 1 (:exit-code result)))
      (is (str/includes? (:err result) "Something went wrong"))))

  (testing "success message goes to stdout"
    (let [result (capture-exit #(cli/exit! :success "Done!" :stream :out))]
      (is (= 0 (:exit-code result)))
      (is (str/includes? (:output result) "Done!")))))

;; -----------------------------------------------------------------------------
;; Error Message Tests
;; -----------------------------------------------------------------------------

(deftest error-message-test
  (testing "not-found error"
    (let [ex (ex-info "Mote not found" {:type :not-found :mote-id "1.2.3"})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Mote not found"))
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "af check") "should suggest running check")))

  (testing "validation-failed error"
    (let [ex (ex-info "Validation failed" {:type :validation-failed
                                           :errors ["Error 1" "Error 2"]})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Validation failed"))
      (is (str/includes? msg "Error 1"))
      (is (str/includes? msg "Error 2"))))

  (testing "already-voted error"
    (let [ex (ex-info "Agent has already voted" {:type :already-voted :agent "bob"})
          msg (cli/error-message ex)]
      (is (str/includes? msg "already voted"))
      (is (str/includes? msg "bob"))))

  (testing "generic error"
    (let [ex (ex-info "Something happened" {:type :unknown})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Something happened")))))

(deftest error-message-repository-errors-test
  (testing "not-initialized error"
    (let [ex (ex-info "Not initialized" {:type :not-initialized :path "."})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Not an Alethfeld repository"))
      (is (str/includes? msg "af init") "should suggest running init")))

  (testing "already-initialized error"
    (let [ex (ex-info "Already initialized" {:type :already-initialized :path "."})
          msg (cli/error-message ex)]
      (is (str/includes? msg "already initialized"))
      (is (str/includes? msg ".alethfeld/"))))

  (testing "not-git-repo error"
    (let [ex (ex-info "Not a git repo" {:type :not-git-repo :path "."})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Not a git repository"))
      (is (str/includes? msg "git init") "should suggest running git init"))))

(deftest error-message-claim-errors-test
  (testing "already-claimed error"
    (let [ex (ex-info "Already claimed" {:type :already-claimed
                                         :mote-id "1.2"
                                         :claimed-by "agent-1"})
          msg (cli/error-message ex)]
      (is (str/includes? msg "1.2"))
      (is (str/includes? msg "agent-1"))
      (is (str/includes? msg "af unclaim") "should suggest unclaim command"))))

(deftest error-message-proposal-errors-test
  (testing "no-proposal error"
    (let [ex (ex-info "No proposal found" {:type :no-proposal})
          msg (cli/error-message ex)]
      (is (str/includes? msg "No active proposal"))
      (is (str/includes? msg "af propose") "should suggest propose command")))

  (testing "proposal-exists error"
    (let [ex (ex-info "Proposal exists" {:type :proposal-exists :proposal-id "prop-123"})
          msg (cli/error-message ex)]
      (is (str/includes? msg "proposal already exists"))
      (is (str/includes? msg "prop-123"))
      (is (str/includes? msg "af approve") "should mention approve")
      (is (str/includes? msg "af reject") "should mention reject"))))

(deftest error-message-git-errors-test
  (testing "git-error with stderr"
    (let [ex (ex-info "Push failed" {:type :git-error :stderr "remote rejected"})
          msg (cli/error-message ex)]
      (is (str/includes? msg "Git operation failed"))
      (is (str/includes? msg "remote rejected")))))

;; -----------------------------------------------------------------------------
;; Verbose Flag Tests
;; -----------------------------------------------------------------------------

(deftest verbose-flag-parsing-test
  (testing "verbose flag is parsed"
    (let [result (cli/parse-args ["show" "1" "--verbose"])]
      (is (:verbose (:options result))))))

(deftest handle-error-verbose-test
  (testing "handle-error without verbose does not show stack trace"
    (let [ex (ex-info "Test error" {:type :not-found :mote-id "1"})
          result (capture-exit #(cli/handle-error ex :edn false))]
      (is (not (str/includes? (:err result) "Stack trace")))
      (is (not (str/includes? (:err result) "clojure")))))

  (testing "handle-error with verbose shows stack trace"
    (let [ex (ex-info "Test error" {:type :not-found :mote-id "1"})
          result (capture-exit #(cli/handle-error ex :edn true))]
      (is (str/includes? (:err result) "Stack trace"))
      (is (str/includes? (:err result) "clojure.lang.ExceptionInfo"))))

  (testing "handle-error with json format includes stack trace when verbose"
    (let [ex (ex-info "Test error" {:type :not-found :mote-id "1"})
          result (capture-exit #(cli/handle-error ex :json true))]
      (is (str/includes? (:output result) "stack-trace"))
      (is (str/includes? (:output result) "clojure.lang.ExceptionInfo")))))

;; -----------------------------------------------------------------------------
;; Argument Parsing Tests
;; -----------------------------------------------------------------------------

(deftest parse-args-no-command-test
  (testing "no arguments shows bare context output"
    (let [result (cli/parse-args [])]
      (is (nil? (:command result)))
      (is (:bare? result)))))

(deftest parse-args-help-test
  (testing "help command"
    (let [result (cli/parse-args ["help"])]
      (is (= "help" (:command result)))
      (is (:help? result))))

  (testing "help command with subcommand"
    (let [result (cli/parse-args ["help" "show"])]
      (is (= "help" (:command result)))
      (is (= ["show"] (:args result)))))

  (testing "-h flag"
    (let [result (cli/parse-args ["-h"])]
      (is (:help? result))))

  (testing "--help flag"
    (let [result (cli/parse-args ["--help"])]
      (is (:help? result))))

  (testing "command with --help"
    (let [result (cli/parse-args ["show" "--help"])]
      (is (= "show" (:command result)))
      (is (:help? result)))))

(deftest parse-args-version-test
  (testing "-v flag"
    (let [result (cli/parse-args ["-v"])]
      (is (:version (:options result)))))

  (testing "--version flag"
    (let [result (cli/parse-args ["--version"])]
      (is (:version (:options result))))))

(deftest parse-args-unknown-command-test
  (testing "unknown command returns error"
    (let [result (cli/parse-args ["foobar"])]
      (is (= "foobar" (:command result)))
      (is (seq (:errors result)))
      (is (str/includes? (first (:errors result)) "Unknown command")))))

(deftest parse-args-show-command-test
  (testing "show with id"
    (let [result (cli/parse-args ["show" "1.2.3"])]
      (is (= "show" (:command result)))
      (is (= "1.2.3" (:id result)))
      (is (nil? (:errors result)))))

  (testing "show without id is error"
    (let [result (cli/parse-args ["show"])]
      (is (= "show" (:command result)))
      (is (seq (:errors result)))
      (is (str/includes? (first (:errors result)) "requires an ID")))))

(deftest parse-args-create-command-test
  (testing "create root with claim"
    (let [result (cli/parse-args ["create" "--root" "--claim" "Test claim"])]
      (is (= "create" (:command result)))
      (is (:root (:options result)))
      (is (= "Test claim" (:claim (:options result))))))

  (testing "create child with claim"
    (let [result (cli/parse-args ["create" "1" "--claim" "Child claim"])]
      (is (= "create" (:command result)))
      (is (= "1" (:id result)))
      (is (= "Child claim" (:claim (:options result))))))

  (testing "create with options"
    (let [result (cli/parse-args ["create" "--root" "--claim" "Test"
                                  "--difficulty" "4" "--priority" "p1"
                                  "--agent" "bot"])]
      (is (= 4 (:difficulty (:options result))))
      (is (= :p1 (:priority (:options result))))
      (is (= "bot" (:agent (:options result)))))))

(deftest parse-args-format-option-test
  (testing "format defaults to text (human-readable)"
    (let [result (cli/parse-args ["show" "1"])]
      (is (= :text (:format (:options result))))))

  (testing "format can be edn"
    (let [result (cli/parse-args ["show" "1" "--format" "edn"])]
      (is (= :edn (:format (:options result))))))

  (testing "format can be json"
    (let [result (cli/parse-args ["show" "1" "--format" "json"])]
      (is (= :json (:format (:options result))))))

  (testing "format can be short flag"
    (let [result (cli/parse-args ["show" "1" "-f" "json"])]
      (is (= :json (:format (:options result)))))))

(deftest parse-args-vote-command-test
  (testing "vote for"
    (let [result (cli/parse-args ["vote" "1" "--for" "--agent" "bob"])]
      (is (= "vote" (:command result)))
      (is (= "1" (:id result)))
      (is (:for (:options result)))
      (is (= "bob" (:agent (:options result))))))

  (testing "vote against with reason"
    (let [result (cli/parse-args ["vote" "1" "--against" "--agent" "bob"
                                  "--reason" "Found a flaw"])]
      (is (:against (:options result)))
      (is (= "Found a flaw" (:reason (:options result)))))))

(deftest parse-args-case-insensitive-test
  (testing "commands are case insensitive"
    (let [result1 (cli/parse-args ["SHOW" "1"])
          result2 (cli/parse-args ["Show" "1"])
          result3 (cli/parse-args ["show" "1"])]
      (is (= "show" (:command result1)))
      (is (= "show" (:command result2)))
      (is (= "show" (:command result3))))))

;; -----------------------------------------------------------------------------
;; Help Generation Tests
;; -----------------------------------------------------------------------------

(deftest generate-help-global-test
  (testing "global help includes version"
    (let [help (cli/generate-help)]
      (is (str/includes? help cli/version))))

  (testing "global help lists commands"
    (let [help (cli/generate-help)]
      (is (str/includes? help "init"))
      (is (str/includes? help "show"))
      (is (str/includes? help "create"))
      (is (str/includes? help "ready"))
      (is (str/includes? help "vote"))))

  (testing "global help shows global options"
    (let [help (cli/generate-help)]
      (is (str/includes? help "--format"))
      (is (str/includes? help "--help"))
      (is (str/includes? help "--version")))))

(deftest generate-help-command-test
  (testing "command help shows description"
    (let [help (cli/generate-help "show")]
      (is (str/includes? help "Display mote details"))))

  (testing "command help shows usage"
    (let [help (cli/generate-help "show")]
      (is (str/includes? help "af show"))))

  (testing "unknown command falls back to global help"
    (let [help (cli/generate-help "foobar")]
      (is (str/includes? help "Unknown command"))
      (is (str/includes? help "init")))))

;; -----------------------------------------------------------------------------
;; Dispatch Tests
;; -----------------------------------------------------------------------------

(deftest dispatch-errors-test
  (testing "dispatch with errors"
    (let [result (cli/dispatch {:errors ["Error 1" "Error 2"]})]
      (is (:error result))
      (is (= ["Error 1" "Error 2"] (:messages result)))
      (is (= :invalid-args (:exit-code result))))))

(deftest dispatch-version-test
  (testing "dispatch with version"
    (let [result (cli/dispatch {:options {:version true}})]
      (is (str/includes? (:output result) cli/version))
      (is (= :success (:exit-code result))))))

(deftest dispatch-help-test
  (testing "dispatch with help"
    (let [result (cli/dispatch {:help? true})]
      (is (string? (:output result)))
      (is (= :success (:exit-code result)))))

  (testing "dispatch with command help"
    (let [result (cli/dispatch {:command "show" :help? true})]
      (is (str/includes? (:output result) "show"))
      (is (= :success (:exit-code result))))))

(deftest dispatch-unimplemented-test
  (testing "dispatch to unimplemented command"
    ;; Use a command that doesn't exist
    (let [result (cli/dispatch {:command "nonexistent-cmd" :options {}})]
      (is (:error result))
      (is (str/includes? (first (:messages result)) "not yet implemented")))))

(deftest dispatch-with-handler-test
  (testing "dispatch to registered handler"
    (cli/register-handler! "test-cmd" (fn [ctx] {:success true :id (:id ctx)}))
    (let [result (cli/dispatch {:command "test-cmd" :id "123" :options {}})]
      (is (= {:success true :id "123"} (:result result)))
      (is (= :success (:exit-code result))))))

(deftest dispatch-handler-exception-test
  (testing "dispatch catches handler exceptions"
    (cli/register-handler! "error-cmd"
                           (fn [_] (throw (ex-info "Test error"
                                                   {:type :not-found
                                                    :mote-id "1"}))))
    (let [result (cli/dispatch {:command "error-cmd" :id "1" :options {}})]
      (is (:error result))
      (is (some? (:exception result)))
      (is (= :not-found (:exit-code result))))))

;; -----------------------------------------------------------------------------
;; Run Integration Tests
;; -----------------------------------------------------------------------------

(deftest run-help-test
  (testing "run with no args shows help"
    (let [result (cli/run [] :exit? false)]
      (is (string? (:output result)))
      (is (= :success (:exit-code result))))))

(deftest run-version-test
  (testing "run with -v shows version"
    (let [result (cli/run ["-v"] :exit? false)]
      (is (str/includes? (:output result) cli/version)))))

(deftest run-unknown-command-test
  (testing "run with unknown command shows error"
    (let [result (cli/run ["foobar"] :exit? false)]
      (is (:error result))
      (is (= :invalid-args (:exit-code result))))))

(deftest run-with-exit-test
  (testing "run actually calls exit when exit? true"
    (let [{:keys [exit-code]} (capture-exit #(cli/run ["-v"] :exit? true))]
      (is (= 0 exit-code)))))

;; -----------------------------------------------------------------------------
;; Commands Metadata Tests
;; -----------------------------------------------------------------------------

(deftest commands-defined-test
  (testing "all expected commands are defined"
    (let [cmds (set (keys cli/commands))]
      (is (contains? cmds "init"))
      (is (contains? cmds "show"))
      (is (contains? cmds "create"))
      (is (contains? cmds "ready"))
      (is (contains? cmds "propose"))
      (is (contains? cmds "approve"))
      (is (contains? cmds "reject"))
      (is (contains? cmds "vote"))
      (is (contains? cmds "update"))
      (is (contains? cmds "taint"))
      (is (contains? cmds "claim"))
      (is (contains? cmds "unclaim"))
      (is (contains? cmds "add-ref"))
      (is (contains? cmds "add-assumption"))
      (is (contains? cmds "add-definition"))
      (is (contains? cmds "check"))
      (is (contains? cmds "log"))
      (is (contains? cmds "sync"))
      (is (contains? cmds "help")))))

(deftest commands-have-metadata-test
  (testing "all commands have required metadata"
    (doseq [[name cmd] cli/commands]
      (testing (str "command: " name)
        (is (string? (:description cmd)) (str name " missing description"))
        (is (string? (:usage cmd)) (str name " missing usage"))
        (is (vector? (:options cmd)) (str name " missing options"))))))
