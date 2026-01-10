(ns alethfeld.errors-test
  "Tests for alethfeld.errors namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [alethfeld.errors :as err]))

;; -----------------------------------------------------------------------------
;; Repository Error Tests
;; -----------------------------------------------------------------------------

(deftest not-initialized-error-test
  (testing "not-initialized error message"
    (let [ex (ex-info "Not initialized" {:type :not-initialized})
          msg (err/format-error ex)]
      (is (str/includes? msg "Not an Alethfeld repository"))
      (is (str/includes? msg "af init")))))

(deftest already-initialized-error-test
  (testing "already-initialized error message"
    (let [ex (ex-info "Already initialized" {:type :already-initialized})
          msg (err/format-error ex)]
      (is (str/includes? msg "Repository already initialized"))
      (is (str/includes? msg ".alethfeld/")))))

(deftest not-git-repo-error-test
  (testing "not-git-repo error message"
    (let [ex (ex-info "Not a git repo" {:type :not-git-repo})
          msg (err/format-error ex)]
      (is (str/includes? msg "Not a git repository"))
      (is (str/includes? msg "git init")))))

;; -----------------------------------------------------------------------------
;; Mote Error Tests
;; -----------------------------------------------------------------------------

(deftest not-found-error-test
  (testing "not-found error message with mote-id"
    (let [ex (ex-info "Mote not found" {:type :not-found :mote-id "1.2.3"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Mote not found"))
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "af check")))))

(deftest validation-failed-error-test
  (testing "validation-failed error with errors list"
    (let [ex (ex-info "Validation failed"
                      {:type :validation-failed
                       :errors ["Invalid claim" "Missing priority"]})
          msg (err/format-error ex)]
      (is (str/includes? msg "Validation failed"))
      (is (str/includes? msg "Invalid claim"))
      (is (str/includes? msg "Missing priority"))))

  (testing "validation-failed error with field/value"
    (let [ex (ex-info "Validation failed"
                      {:type :validation-failed
                       :field :priority
                       :value "invalid"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Validation failed"))
      (is (str/includes? msg "priority")))))

(deftest invalid-status-error-test
  (testing "invalid-status error message"
    (let [ex (ex-info "Invalid status"
                      {:type :invalid-status
                       :status :verified
                       :current-status :proposed
                       :valid-transitions [:fixed :rejected]})
          msg (err/format-error ex)]
      (is (str/includes? msg "Invalid status transition"))
      (is (str/includes? msg "proposed"))
      (is (str/includes? msg "verified")))))

(deftest integrity-error-test
  (testing "integrity-error message"
    (let [ex (ex-info "Integrity error"
                      {:type :integrity-error
                       :mote-id "1.2.3"
                       :session-mote-id "1.2.4"})
          msg (err/format-error ex)]
      (is (str/includes? msg "integrity"))
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "af check")))))

;; -----------------------------------------------------------------------------
;; Claim Error Tests
;; -----------------------------------------------------------------------------

(deftest already-claimed-error-test
  (testing "already-claimed error message"
    (let [ex (ex-info "Already claimed"
                      {:type :already-claimed
                       :mote-id "1.2.3"
                       :claimed-by "alice"})
          msg (err/format-error ex)]
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "alice"))
      (is (str/includes? msg "af unclaim"))
      (is (str/includes? msg "af ready")))))

;; -----------------------------------------------------------------------------
;; Voting Error Tests
;; -----------------------------------------------------------------------------

(deftest already-voted-error-test
  (testing "already-voted error message"
    (let [ex (ex-info "Already voted"
                      {:type :already-voted
                       :agent "bob"
                       :mote-id "1.2.3"})
          msg (err/format-error ex)]
      (is (str/includes? msg "bob"))
      (is (str/includes? msg "already voted"))
      (is (str/includes? msg "different agent")))))

(deftest self-vote-error-test
  (testing "self-vote error message"
    (let [ex (ex-info "Self vote forbidden"
                      {:type :self-vote
                       :agent "alice"
                       :mote-id "1.2.3"})
          msg (err/format-error ex)]
      (is (str/includes? msg "alice"))
      (is (str/includes? msg "cannot vote on their own work"))
      (is (str/includes? msg "different agent")))))

(deftest quorum-not-reached-error-test
  (testing "quorum-not-reached error message"
    (let [ex (ex-info "Quorum not reached"
                      {:type :quorum-not-reached
                       :mote-id "1.2.3"
                       :votes-needed 3
                       :votes-have 1})
          msg (err/format-error ex)]
      (is (str/includes? msg "Quorum"))
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "3"))
      (is (str/includes? msg "1"))
      (is (str/includes? msg "af vote")))))

;; -----------------------------------------------------------------------------
;; Proposal Error Tests
;; -----------------------------------------------------------------------------

(deftest no-proposal-error-test
  (testing "no-proposal error message"
    (let [ex (ex-info "No proposal"
                      {:type :no-proposal
                       :parent-id "1.2"})
          msg (err/format-error ex)]
      (is (str/includes? msg "No active proposal"))
      (is (str/includes? msg "1.2"))
      (is (str/includes? msg "af propose")))))

(deftest proposal-exists-error-test
  (testing "proposal-exists error message"
    (let [ex (ex-info "Proposal exists"
                      {:type :proposal-exists
                       :parent-id "1.2"
                       :proposal-id "abc123"})
          msg (err/format-error ex)]
      (is (str/includes? msg "proposal already exists"))
      (is (str/includes? msg "1.2"))
      (is (str/includes? msg "abc123"))
      (is (str/includes? msg "af approve"))
      (is (str/includes? msg "af reject")))))

(deftest atomicity-violation-error-test
  (testing "atomicity-violation error message"
    (let [ex (ex-info "Atomicity violation"
                      {:type :atomicity-violation
                       :parent-id "1.2"
                       :children-statuses {"1.2.1" :fixed "1.2.2" :proposed}})
          msg (err/format-error ex)]
      (is (str/includes? msg "Cannot create children"))
      (is (str/includes? msg "1.2"))
      (is (str/includes? msg "1.2.1"))
      (is (str/includes? msg "fixed")))))

;; -----------------------------------------------------------------------------
;; Git Error Tests
;; -----------------------------------------------------------------------------

(deftest git-error-test
  (testing "git-error message"
    (let [ex (ex-info "Git failed"
                      {:type :git-error
                       :cmd "git push"
                       :stderr "fatal: remote rejected"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Git operation failed"))
      (is (str/includes? msg "git push"))
      (is (str/includes? msg "fatal: remote rejected")))))

(deftest no-remote-error-test
  (testing "no-remote error message"
    (let [ex (ex-info "No remote"
                      {:type :no-remote
                       :remote "origin"})
          msg (err/format-error ex)]
      (is (str/includes? msg "No remote configured"))
      (is (str/includes? msg "origin"))
      (is (str/includes? msg "git remote add")))))

;; -----------------------------------------------------------------------------
;; Session Error Tests
;; -----------------------------------------------------------------------------

(deftest invalid-session-error-test
  (testing "invalid-session error message"
    (let [ex (ex-info "Invalid session"
                      {:type :invalid-session
                       :session-id "sess-123"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Invalid or expired session"))
      (is (str/includes? msg "sess-123"))
      (is (str/includes? msg "af ready")))))

(deftest session-expired-error-test
  (testing "session-expired error message"
    (let [ex (ex-info "Session expired"
                      {:type :session-expired
                       :session-id "sess-456"
                       :expires-at "2024-01-01T12:00:00Z"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Session has expired"))
      (is (str/includes? msg "sess-456"))
      (is (str/includes? msg "2024-01-01"))
      (is (str/includes? msg "af ready")))))

(deftest session-mote-mismatch-error-test
  (testing "session-mote-mismatch error message"
    (let [ex (ex-info "Session mote mismatch"
                      {:type :session-mote-mismatch
                       :session-mote-id "1.2.3"
                       :requested-mote-id "4.5.6"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Session is for a different mote"))
      (is (str/includes? msg "1.2.3"))
      (is (str/includes? msg "4.5.6"))
      (is (str/includes? msg "af done")))))

(deftest action-not-allowed-error-test
  (testing "action-not-allowed error message"
    (let [ex (ex-info "Action not allowed"
                      {:type :action-not-allowed
                       :role :advisor
                       :action :vote
                       :allowed-actions [:review :comment]})
          msg (err/format-error ex)]
      ;; New format: "Cannot X: your role is Y"
      (is (str/includes? msg "Cannot vote"))
      (is (str/includes? msg "advisor"))
      ;; Shows what advisor can do
      (is (str/includes? msg "af approve"))
      ;; Shows recovery path
      (is (str/includes? msg "af done"))
      (is (str/includes? msg "af ready")))))

(deftest session-not-found-error-test
  (testing "session-not-found error message"
    (let [ex (ex-info "Session not found"
                      {:type :session-not-found
                       :session-id "sess-789"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Session not found"))
      (is (str/includes? msg "sess-789"))
      ;; New format includes possible causes and recovery
      (is (str/includes? msg "expired"))
      (is (str/includes? msg "af ready")))))

;; -----------------------------------------------------------------------------
;; File/Parse Error Tests
;; -----------------------------------------------------------------------------

(deftest parse-error-test
  (testing "parse-error message"
    (let [ex (ex-info "Parse error"
                      {:type :parse-error
                       :path "/path/to/file.edn"
                       :cause "Unexpected EOF"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Failed to parse"))
      (is (str/includes? msg "/path/to/file.edn"))
      (is (str/includes? msg "Unexpected EOF"))
      (is (str/includes? msg "git history")))))

;; -----------------------------------------------------------------------------
;; Exit Code Tests
;; -----------------------------------------------------------------------------

(deftest error-type->exit-code-test
  (testing "not-found types return :not-found"
    (is (= :not-found (err/error-type->exit-code :not-found)))
    (is (= :not-found (err/error-type->exit-code :session-not-found))))

  (testing "validation-failed returns :validation-error"
    (is (= :validation-error (err/error-type->exit-code :validation-failed))))

  (testing "conflict types return :conflict"
    (is (= :conflict (err/error-type->exit-code :already-voted)))
    (is (= :conflict (err/error-type->exit-code :already-claimed)))
    (is (= :conflict (err/error-type->exit-code :proposal-exists))))

  (testing "unknown types return :error"
    (is (= :error (err/error-type->exit-code :unknown-type)))
    (is (= :error (err/error-type->exit-code nil)))))

;; -----------------------------------------------------------------------------
;; Default Fallback Tests
;; -----------------------------------------------------------------------------

(deftest unknown-error-type-test
  (testing "unknown error type falls back to message"
    (let [ex (ex-info "Something went wrong" {:type :unknown-type :extra "data"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Something went wrong"))
      (is (str/includes? msg "extra")))))

(deftest no-type-error-test
  (testing "error without type uses message"
    (let [ex (ex-info "Generic error" {:some :data})
          msg (err/format-error ex)]
      (is (str/includes? msg "Generic error")))))

;; -----------------------------------------------------------------------------
;; throw-error Helper Tests
;; -----------------------------------------------------------------------------

(deftest throw-error-test
  (testing "throw-error creates properly structured exception"
    (try
      (err/throw-error :not-found "Mote not found" {:mote-id "1.2.3"})
      (is false "Should have thrown")
      (catch clojure.lang.ExceptionInfo e
        (is (= "Mote not found" (ex-message e)))
        (is (= :not-found (:type (ex-data e))))
        (is (= "1.2.3" (:mote-id (ex-data e))))))))

;; -----------------------------------------------------------------------------
;; Levenshtein Distance Tests
;; -----------------------------------------------------------------------------

(deftest levenshtein-distance-test
  (testing "identical strings have distance 0"
    (is (= 0 (err/levenshtein-distance "verifier" "verifier")))
    (is (= 0 (err/levenshtein-distance "" ""))))

  (testing "empty string to non-empty has distance = length"
    (is (= 5 (err/levenshtein-distance "" "hello")))
    (is (= 5 (err/levenshtein-distance "hello" ""))))

  (testing "single character insertions"
    (is (= 1 (err/levenshtein-distance "verifier" "verifyer")))
    (is (= 1 (err/levenshtein-distance "advisor" "advisors"))))

  (testing "single character deletions"
    (is (= 1 (err/levenshtein-distance "proposer" "propose"))))

  (testing "single character substitutions"
    (is (= 1 (err/levenshtein-distance "verifier" "verifierx"))))

  (testing "complex edits"
    ;; "reviewer" -> "verifier" requires 4 edits
    (is (<= 3 (err/levenshtein-distance "reviewer" "verifier") 5))
    ;; "judge" -> "verifier" is very different
    (is (> (err/levenshtein-distance "judge" "verifier") 5))))

;; -----------------------------------------------------------------------------
;; Role Suggestion Tests
;; -----------------------------------------------------------------------------

(deftest suggest-role-test
  (testing "suggests correct role for typos"
    ;; "verifyer" is 1 edit from "verifier"
    (is (= :verifier (err/suggest-role :verifyer)))
    ;; "advisr" is 1 edit from "advisor"
    (is (= :advisor (err/suggest-role :advisr)))
    ;; "propser" is 1 edit from "proposer"
    (is (= :proposer (err/suggest-role :propser))))

  (testing "suggests for common misremembered names"
    ;; "reviewer" is close to "verifier"
    (is (some? (err/suggest-role :reviewer))))

  (testing "returns nil for completely wrong names"
    ;; "judge" is too far from any valid role (7 edits to verifier)
    (is (nil? (err/suggest-role :judge)))
    ;; "controller" is too far from any valid role
    (is (nil? (err/suggest-role :controller)))
    ;; "xyz" is too far from any valid role
    (is (nil? (err/suggest-role :xyz)))))

(deftest format-valid-roles-test
  (testing "formats all valid roles"
    (let [output (err/format-valid-roles)]
      (is (str/includes? output "proposer"))
      (is (str/includes? output "advisor"))
      (is (str/includes? output "prover"))
      (is (str/includes? output "verifier"))
      (is (str/includes? output "ref-checker"))
      (is (str/includes? output "counterexample"))
      ;; Contains descriptions
      (is (str/includes? output "Break claims"))
      (is (str/includes? output "Vote on claim")))))

;; -----------------------------------------------------------------------------
;; Invalid Role Error Tests (Section 2.1)
;; -----------------------------------------------------------------------------

(deftest invalid-role-error-test
  (testing "invalid-role error shows valid roles"
    (let [ex (ex-info "Invalid role"
                      {:type :invalid-role
                       :role :reviewer})
          msg (err/format-error ex)]
      (is (str/includes? msg "Invalid role: \"reviewer\""))
      (is (str/includes? msg "Valid roles:"))
      (is (str/includes? msg "proposer"))
      (is (str/includes? msg "advisor"))
      (is (str/includes? msg "verifier"))
      (is (str/includes? msg "prover"))
      (is (str/includes? msg "ref-checker"))
      (is (str/includes? msg "counterexample"))
      ;; Shows role descriptions
      (is (str/includes? msg "Break claims"))
      (is (str/includes? msg "Vote on claim"))
      ;; Shows recovery command
      (is (str/includes? msg "af ready --agent"))))

  (testing "invalid-role suggests similar role"
    (let [ex (ex-info "Invalid role"
                      {:type :invalid-role
                       :role :verifyer})
          msg (err/format-error ex)]
      (is (str/includes? msg "Did you mean: verifier?"))))

  (testing "invalid-role with string role"
    (let [ex (ex-info "Invalid role"
                      {:type :invalid-role
                       :role "critic"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Invalid role: \"critic\""))
      (is (str/includes? msg "Valid roles:")))))

;; -----------------------------------------------------------------------------
;; Improved Action Not Allowed Error Tests (Section 2.3)
;; -----------------------------------------------------------------------------

(deftest action-not-allowed-improved-error-test
  (testing "shows what role CAN do"
    (let [ex (ex-info "Action not allowed"
                      {:type :action-not-allowed
                       :role :verifier
                       :action :approve
                       :session-id "abc-123"})
          msg (err/format-error ex)]
      ;; New format: "Cannot X: your role is Y"
      (is (str/includes? msg "Cannot approve"))
      (is (str/includes? msg "verifier"))
      ;; Shows what verifier can do
      (is (str/includes? msg "af vote"))
      ;; Shows recovery path
      (is (str/includes? msg "af done"))
      (is (str/includes? msg "af ready"))))

  (testing "suggests correct role for action"
    (let [ex (ex-info "Action not allowed"
                      {:type :action-not-allowed
                       :role :verifier
                       :action :approve})
          msg (err/format-error ex)]
      ;; Approve requires advisor
      (is (str/includes? msg "advisor"))))

  (testing "proposer withdrawal error unchanged"
    (let [ex (ex-info "Action not allowed"
                      {:type :action-not-allowed
                       :agent "alice"
                       :proposer "bob"
                       :mote-id "1.2"})
          msg (err/format-error ex)]
      (is (str/includes? msg "Only the proposer"))
      (is (str/includes? msg "alice"))
      (is (str/includes? msg "bob")))))

;; -----------------------------------------------------------------------------
;; Improved Session Not Found Error Tests (Section 2.2)
;; -----------------------------------------------------------------------------

(deftest session-not-found-improved-error-test
  (testing "explains possible causes"
    (let [ex (ex-info "Session not found"
                      {:type :session-not-found
                       :session-id "abc-123-def-456-ghi"})
          msg (err/format-error ex)]
      ;; Shows truncated session ID
      (is (str/includes? msg "Session not found"))
      ;; Lists possible causes
      (is (str/includes? msg "expired"))
      (is (str/includes? msg "30 minutes"))
      (is (str/includes? msg "af done"))
      (is (str/includes? msg "incorrect"))
      ;; Shows recovery
      (is (str/includes? msg "af ready --name"))
      ;; Shows how to check status
      (is (str/includes? msg "af sessions"))))

  (testing "handles missing session-id"
    (let [ex (ex-info "Session not found"
                      {:type :session-not-found})
          msg (err/format-error ex)]
      (is (str/includes? msg "Session not found: <unknown>"))
      (is (str/includes? msg "af ready")))))
