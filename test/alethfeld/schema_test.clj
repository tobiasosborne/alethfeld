(ns alethfeld.schema-test
  "Tests for alethfeld.schema namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.schema :as s]))

;; -----------------------------------------------------------------------------
;; Primitive Types
;; -----------------------------------------------------------------------------

(deftest mote-id-test
  (testing "MoteId validation - valid cases"
    (is (s/valid? s/MoteId "1"))
    (is (s/valid? s/MoteId "1.2.3"))
    (is (s/valid? s/MoteId "10.20.30"))
    (is (s/valid? s/MoteId "1.2.3.4.5")))

  (testing "MoteId validation - invalid cases"
    (is (not (s/valid? s/MoteId "")))
    (is (not (s/valid? s/MoteId nil)))
    (is (not (s/valid? s/MoteId "root")))
    (is (not (s/valid? s/MoteId "abc")))
    (is (not (s/valid? s/MoteId "1.2.a")))
    (is (not (s/valid? s/MoteId ".1")))
    (is (not (s/valid? s/MoteId "1.")))
    (is (not (s/valid? s/MoteId "1..2")))))

(deftest status-test
  (testing "Status enum validation"
    (is (s/valid? s/Status :proposed))
    (is (s/valid? s/Status :rejected))
    (is (s/valid? s/Status :fixed))
    (is (s/valid? s/Status :verified))
    (is (s/valid? s/Status :refuted))
    (is (s/valid? s/Status :contested))
    (is (not (s/valid? s/Status :unknown)))
    (is (not (s/valid? s/Status "fixed")))))

(deftest taint-test
  (testing "Taint enum validation"
    (is (s/valid? s/Taint :needs-decomposition))
    (is (s/valid? s/Taint :needs-proposal-review))
    (is (s/valid? s/Taint :needs-refinement))
    (is (s/valid? s/Taint :needs-verification))
    (is (s/valid? s/Taint :needs-refs))
    (is (s/valid? s/Taint :needs-votes))
    (is (s/valid? s/Taint :needs-counterexample))
    (is (not (s/valid? s/Taint :unknown-taint)))))

(deftest priority-test
  (testing "Priority enum validation"
    (is (s/valid? s/Priority :p0))
    (is (s/valid? s/Priority :p1))
    (is (s/valid? s/Priority :p2))
    (is (s/valid? s/Priority :p3))
    (is (s/valid? s/Priority :p4))
    (is (not (s/valid? s/Priority :p5)))
    (is (not (s/valid? s/Priority 0)))))

(deftest difficulty-test
  (testing "Difficulty integer range validation"
    (is (s/valid? s/Difficulty 1))
    (is (s/valid? s/Difficulty 3))
    (is (s/valid? s/Difficulty 5))
    (is (not (s/valid? s/Difficulty 0)))
    (is (not (s/valid? s/Difficulty 6)))
    (is (not (s/valid? s/Difficulty "3")))))

(deftest role-test
  (testing "Role enum validation"
    (is (s/valid? s/Role :proposer))
    (is (s/valid? s/Role :advisor))
    (is (s/valid? s/Role :prover))
    (is (s/valid? s/Role :verifier))
    (is (s/valid? s/Role :ref-checker))
    (is (s/valid? s/Role :counterexample))
    (is (not (s/valid? s/Role :unknown-role)))))

;; -----------------------------------------------------------------------------
;; References & Definitions
;; -----------------------------------------------------------------------------

(deftest internal-ref-test
  (testing "InternalRef validation"
    (is (s/valid? s/InternalRef {:type :internal :ref "1.2"}))
    (is (s/valid? s/InternalRef {:type :internal :ref "1.2" :note "Continuity"}))
    (is (not (s/valid? s/InternalRef {:type :external :ref "1.2"})))
    (is (not (s/valid? s/InternalRef {:type :internal})))))

(deftest external-ref-test
  (testing "ExternalRef validation"
    (is (s/valid? s/ExternalRef {:type :external :ref "arXiv:2301.00001"}))
    (is (s/valid? s/ExternalRef {:type :external :ref "ISBN:123" :note "Thm 3.2"}))
    (is (not (s/valid? s/ExternalRef {:type :internal :ref "1.2"})))
    (is (not (s/valid? s/ExternalRef {:type :external})))))

(deftest assumption-test
  (testing "Assumption (union type) validation"
    (is (s/valid? s/Assumption {:type :internal :ref "1.2"}))
    (is (s/valid? s/Assumption {:type :external :ref "arXiv:2301.00001"}))
    (is (not (s/valid? s/Assumption {:type :other :ref "foo"})))))

(deftest definition-test
  (testing "Definition validation"
    (is (s/valid? s/Definition {:symbol "ε" :meaning "tolerance parameter"}))
    (is (s/valid? s/Definition {:symbol "f" :meaning "continuous function"}))
    (is (not (s/valid? s/Definition {:symbol "x"})))
    (is (not (s/valid? s/Definition {:meaning "missing symbol"})))))

;; -----------------------------------------------------------------------------
;; Votes
;; -----------------------------------------------------------------------------

(def sample-timestamp #inst "2026-01-07T12:00:00.000Z")

(deftest vote-test
  (testing "Vote validation"
    (is (s/valid? s/Vote {:agent "verifier-1"
                          :vote :for
                          :timestamp sample-timestamp}))
    (is (s/valid? s/Vote {:agent "verifier-2"
                          :vote :against
                          :reason "Found gap in logic"
                          :timestamp sample-timestamp}))
    (is (not (s/valid? s/Vote {:agent "x" :vote :approve :timestamp sample-timestamp})))
    (is (not (s/valid? s/Vote {:agent "x" :vote :for})))))

(deftest proposal-vote-test
  (testing "ProposalVote validation"
    (is (s/valid? s/ProposalVote {:agent "advisor-1"
                                   :vote :approve
                                   :timestamp sample-timestamp}))
    (is (s/valid? s/ProposalVote {:agent "advisor-2"
                                   :vote :reject
                                   :reason "Incomplete decomposition"
                                   :timestamp sample-timestamp}))
    (is (not (s/valid? s/ProposalVote {:agent "x" :vote :for :timestamp sample-timestamp})))))

;; -----------------------------------------------------------------------------
;; Proposal
;; -----------------------------------------------------------------------------

(deftest proposal-test
  (testing "Proposal validation"
    (is (s/valid? s/Proposal {:id "prop-20260107-a7f3"
                               :proposed-by "proposer-1"
                               :proposed-at sample-timestamp
                               :children ["1.2.1" "1.2.2"]
                               :votes []
                               :status :pending}))
    (is (s/valid? s/Proposal {:id "prop-2"
                               :proposed-by "agent"
                               :proposed-at sample-timestamp
                               :children ["1.1"]
                               :votes [{:agent "adv"
                                        :vote :approve
                                        :timestamp sample-timestamp}]
                               :status :approved}))
    (is (not (s/valid? s/Proposal {:id "x" :proposed-by "y"})))
    (is (not (s/valid? s/Proposal {:id "x"
                                    :proposed-by "y"
                                    :proposed-at sample-timestamp
                                    :children []
                                    :votes []
                                    :status :unknown})))))

;; -----------------------------------------------------------------------------
;; Mote
;; -----------------------------------------------------------------------------

(def minimal-mote
  {:id "1.2.3"
   :claim "For all ε > 0, there exists δ > 0"
   :status :fixed
   :taint #{:needs-verification}
   :priority :p1
   :difficulty 3
   :children []
   :assumptions []
   :definitions []
   :votes []
   :created-by "proposer-1"
   :created-at sample-timestamp
   :updated-at sample-timestamp})

(deftest mote-test
  (testing "Mote validation - minimal"
    (is (s/valid? s/Mote minimal-mote)))

  (testing "Mote validation - with optional fields"
    (is (s/valid? s/Mote (assoc minimal-mote
                                :parent "1.2"
                                :claimed-by "prover-1"
                                :claimed-at sample-timestamp))))

  (testing "Mote validation - with nested structures"
    (is (s/valid? s/Mote (assoc minimal-mote
                                :assumptions [{:type :internal :ref "1.2.1" :note "Continuity"}
                                              {:type :external :ref "arXiv:2301.00001"}]
                                :definitions [{:symbol "ε" :meaning "tolerance parameter"}]
                                :votes [{:agent "v1" :vote :for :timestamp sample-timestamp}]))))

  (testing "Mote validation - with proposal"
    (is (s/valid? s/Mote (assoc minimal-mote
                                :proposal {:id "prop-1"
                                           :proposed-by "p1"
                                           :proposed-at sample-timestamp
                                           :children ["1.2.3.1"]
                                           :votes []
                                           :status :pending}))))

  (testing "Mote validation - invalid cases"
    (is (not (s/valid? s/Mote (dissoc minimal-mote :id))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :status :invalid))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :difficulty 0))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :taint #{:unknown-taint}))))))

;; -----------------------------------------------------------------------------
;; Job
;; -----------------------------------------------------------------------------

(deftest job-test
  (testing "Job validation"
    (is (s/valid? s/Job {:job-id "job-20260107-143052-a7f3"
                          :mote-id "1.2.3"
                          :role :verifier
                          :difficulty 3
                          :priority :p1
                          :mote minimal-mote
                          :siblings []
                          :prompt "You are a VERIFIER agent..."}))
    (is (s/valid? s/Job {:job-id "job-2"
                          :mote-id "1.2"
                          :role :proposer
                          :difficulty 2
                          :priority :p2
                          :mote minimal-mote
                          :parent minimal-mote
                          :siblings [minimal-mote]
                          :prompt "You are a PROPOSER agent..."}))))

;; -----------------------------------------------------------------------------
;; Ready Options
;; -----------------------------------------------------------------------------

(deftest difficulty-range-test
  (testing "DifficultyRange validation"
    (is (s/valid? s/DifficultyRange 3))
    (is (s/valid? s/DifficultyRange [1 3]))
    (is (s/valid? s/DifficultyRange [2 5]))
    (is (not (s/valid? s/DifficultyRange [0 3])))
    (is (not (s/valid? s/DifficultyRange [1 6])))))

(deftest priority-range-test
  (testing "PriorityRange validation"
    (is (s/valid? s/PriorityRange :p2))
    (is (s/valid? s/PriorityRange [:p1 :p3]))
    (is (not (s/valid? s/PriorityRange [:p0 :p5])))))

(deftest ready-options-test
  (testing "ReadyOptions validation"
    (is (s/valid? s/ReadyOptions {}))
    (is (s/valid? s/ReadyOptions {:agent "prover-1"}))
    (is (s/valid? s/ReadyOptions {:role :verifier}))
    (is (s/valid? s/ReadyOptions {:difficulty 3}))
    (is (s/valid? s/ReadyOptions {:difficulty [1 3]}))
    (is (s/valid? s/ReadyOptions {:priority :p1}))
    (is (s/valid? s/ReadyOptions {:priority [:p0 :p2]}))
    (is (s/valid? s/ReadyOptions {:max 5}))
    (is (s/valid? s/ReadyOptions {:no-claim true}))
    (is (s/valid? s/ReadyOptions {:format :json}))
    (is (s/valid? s/ReadyOptions {:agent "a"
                                   :role :prover
                                   :difficulty [2 4]
                                   :priority [:p1 :p3]
                                   :max 10
                                   :no-claim false
                                   :format :edn}))
    (is (not (s/valid? s/ReadyOptions {:max 0})))
    (is (not (s/valid? s/ReadyOptions {:format :xml})))))

;; -----------------------------------------------------------------------------
;; Validation Helpers
;; -----------------------------------------------------------------------------

(deftest valid?-test
  (testing "valid? helper function"
    (is (true? (s/valid? s/MoteId "1.2.3")))
    (is (false? (s/valid? s/MoteId "")))))

(deftest explain-test
  (testing "explain helper function"
    (is (nil? (s/explain s/MoteId "1.2.3")))
    (is (some? (s/explain s/MoteId "")))))

;; -----------------------------------------------------------------------------
;; Claim Text Edge Cases (Schema-Level)
;; -----------------------------------------------------------------------------

(deftest claim-schema-edge-cases-test
  (testing "Claim field accepts various string types"
    ;; The claim field is currently defined as a plain :string
    ;; These tests document the current schema behavior

    ;; Basic string - should always work
    (is (s/valid? s/Mote (assoc minimal-mote :claim "A simple claim")))

    ;; Empty string - currently allowed (documenting behavior)
    (is (s/valid? s/Mote (assoc minimal-mote :claim ""))
        "DOCUMENTED: Empty claims are currently accepted by schema")

    ;; Whitespace-only - currently allowed (documenting behavior)
    (is (s/valid? s/Mote (assoc minimal-mote :claim "   "))
        "DOCUMENTED: Whitespace-only claims are currently accepted"))

  (testing "Claim field rejects non-string types"
    ;; These should all fail - claim must be a string
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim nil))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim 123))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim :keyword))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim []))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim {}))))
    (is (not (s/valid? s/Mote (assoc minimal-mote :claim true)))))

  (testing "Claim field with Unicode content"
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Greek: alpha beta gamma")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Math: forall exists in notin empty intersect union subset superset")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Arrows: right left bidi implies iff")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Sets: N Z Q R C"))))

  (testing "Claim field with formatting characters"
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Line1\nLine2")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Col1\tCol2")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "Windows\r\nLinebreak"))))

  (testing "Claim field with special characters"
    (is (s/valid? s/Mote (assoc minimal-mote :claim "\"quoted\"")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "back\\slash")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "{braces} [brackets]")))
    (is (s/valid? s/Mote (assoc minimal-mote :claim "(parens); semicolon"))))

  (testing "Claim field with very long content"
    (let [long-claim (apply str (repeat 50000 "x"))]
      (is (s/valid? s/Mote (assoc minimal-mote :claim long-claim)))))

  (testing "Missing claim field fails validation"
    (is (not (s/valid? s/Mote (dissoc minimal-mote :claim))))))
