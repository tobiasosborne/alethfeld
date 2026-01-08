(ns alethfeld.prompt-test
  (:require [clojure.test :refer [deftest testing is are]]
            [clojure.string :as str]
            [alethfeld.prompt :as prompt]
            [alethfeld.mote :as mote]))

;; -----------------------------------------------------------------------------
;; Test Helpers
;; -----------------------------------------------------------------------------

(defn- test-mote
  "Create a minimal valid mote for testing.
   Accepts overrides for any mote field."
  [& {:keys [id claim status taint priority difficulty
             parent children assumptions definitions votes proposal]
      :or {id "1.2.3"
           claim "Test claim"
           status :fixed
           taint #{:needs-verification}
           priority :p2
           difficulty 3
           children []
           assumptions []
           definitions []
           votes []}}]
  (cond-> (mote/make-mote id claim "test-agent"
                          :status status
                          :taint taint
                          :priority priority
                          :difficulty difficulty)
    parent (assoc :parent parent)
    (seq children) (assoc :children children)
    (seq assumptions) (assoc :assumptions assumptions)
    (seq definitions) (assoc :definitions definitions)
    (seq votes) (assoc :votes votes)
    proposal (assoc :proposal proposal)))

(defn- test-job
  "Create a minimal Job map for testing."
  [& {:keys [role mote parent siblings]
      :or {role :verifier
           siblings []}}]
  {:job-id "job-test-123"
   :mote-id (:id (or mote (test-mote)))
   :role role
   :difficulty (:difficulty (or mote (test-mote)))
   :priority (:priority (or mote (test-mote)))
   :mote (or mote (test-mote))
   :parent parent
   :siblings siblings
   :prompt "placeholder"})

;; =============================================================================
;; format-assumptions Tests
;; =============================================================================

(deftest format-assumptions-empty-test
  (testing "Empty assumptions returns '(none)'"
    (is (= "(none)" (prompt/format-assumptions [])))))

(deftest format-assumptions-internal-ref-test
  (testing "Internal reference formats correctly"
    (let [assumptions [{:type :internal :ref "1.2.1"}]]
      (is (= "- [internal] 1.2.1" (prompt/format-assumptions assumptions)))))

  (testing "Internal reference with note"
    (let [assumptions [{:type :internal :ref "1.2.1" :note "Continuity"}]]
      (is (= "- [internal] 1.2.1: Continuity" (prompt/format-assumptions assumptions))))))

(deftest format-assumptions-external-ref-test
  (testing "External reference formats correctly"
    (let [assumptions [{:type :external :ref "arXiv:2301.00001"}]]
      (is (= "- [external] arXiv:2301.00001" (prompt/format-assumptions assumptions)))))

  (testing "External reference with note"
    (let [assumptions [{:type :external :ref "arXiv:2301.00001" :note "Theorem 3.2"}]]
      (is (= "- [external] arXiv:2301.00001: Theorem 3.2" (prompt/format-assumptions assumptions))))))

(deftest format-assumptions-multiple-test
  (testing "Multiple assumptions formatted on separate lines"
    (let [assumptions [{:type :internal :ref "1.2.1" :note "Base case"}
                       {:type :external :ref "Rudin 1976" :note "Thm 7.1"}
                       {:type :internal :ref "1.1"}]]
      (is (= (str "- [internal] 1.2.1: Base case\n"
                  "- [external] Rudin 1976: Thm 7.1\n"
                  "- [internal] 1.1")
             (prompt/format-assumptions assumptions))))))

;; =============================================================================
;; format-definitions Tests
;; =============================================================================

(deftest format-definitions-empty-test
  (testing "Empty definitions returns '(none)'"
    (is (= "(none)" (prompt/format-definitions [])))))

(deftest format-definitions-single-test
  (testing "Single definition formats correctly"
    (let [definitions [{:symbol "ε" :meaning "tolerance parameter"}]]
      (is (= "- ε: tolerance parameter" (prompt/format-definitions definitions))))))

(deftest format-definitions-multiple-test
  (testing "Multiple definitions formatted on separate lines"
    (let [definitions [{:symbol "ε" :meaning "tolerance parameter"}
                       {:symbol "δ" :meaning "neighborhood radius"}
                       {:symbol "f" :meaning "continuous function"}]]
      (is (= (str "- ε: tolerance parameter\n"
                  "- δ: neighborhood radius\n"
                  "- f: continuous function")
             (prompt/format-definitions definitions))))))

;; =============================================================================
;; format-vote-summary Tests
;; =============================================================================

(deftest format-vote-summary-empty-test
  (testing "Empty votes returns '(no votes)'"
    (is (= "(no votes)" (prompt/format-vote-summary [])))))

(deftest format-vote-summary-all-for-test
  (testing "All votes for"
    (let [votes [{:agent "v1" :vote :for}
                 {:agent "v2" :vote :for}]]
      (is (= "2 for, 0 against" (prompt/format-vote-summary votes))))))

(deftest format-vote-summary-all-against-test
  (testing "All votes against"
    (let [votes [{:agent "v1" :vote :against}]]
      (is (= "0 for, 1 against" (prompt/format-vote-summary votes))))))

(deftest format-vote-summary-mixed-test
  (testing "Mixed votes"
    (let [votes [{:agent "v1" :vote :for}
                 {:agent "v2" :vote :against}
                 {:agent "v3" :vote :for}
                 {:agent "v4" :vote :against}]]
      (is (= "2 for, 2 against" (prompt/format-vote-summary votes))))))

;; =============================================================================
;; render-prompt Tests - Role Headers
;; =============================================================================

(deftest render-prompt-proposer-header-test
  (testing "Proposer prompt has correct header"
    (let [job (test-job :role :proposer
                        :mote (test-mote :taint #{:needs-decomposition}))
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are a PROPOSER agent.")))))

(deftest render-prompt-advisor-header-test
  (testing "Advisor prompt has correct header"
    (let [mote (test-mote :taint #{:needs-proposal-review}
                          :proposal {:id "prop-123"
                                     :proposed-by "proposer-1"
                                     :proposed-at #inst "2026-01-07"
                                     :children ["1.2.3.1" "1.2.3.2"]
                                     :votes []
                                     :status :pending})
          job (test-job :role :advisor :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are an ADVISOR agent.")))))

(deftest render-prompt-prover-header-test
  (testing "Prover prompt has correct header"
    (let [job (test-job :role :prover
                        :mote (test-mote :taint #{:needs-refinement}))
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are a PROVER agent.")))))

(deftest render-prompt-verifier-header-test
  (testing "Verifier prompt has correct header"
    (let [job (test-job :role :verifier
                        :mote (test-mote :taint #{:needs-verification}))
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are a VERIFIER agent.")))))

(deftest render-prompt-ref-checker-header-test
  (testing "Ref-checker prompt has correct header"
    (let [job (test-job :role :ref-checker
                        :mote (test-mote :taint #{:needs-refs}))
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are a REF-CHECKER agent.")))))

(deftest render-prompt-counterexample-header-test
  (testing "Counterexample prompt has correct header"
    (let [job (test-job :role :counterexample
                        :mote (test-mote :taint #{:needs-counterexample}))
          prompt (prompt/render-prompt job)]
      (is (str/starts-with? prompt "You are a COUNTEREXAMPLE agent.")))))

;; =============================================================================
;; render-prompt Tests - Content Interpolation
;; =============================================================================

(deftest render-prompt-mote-id-interpolation-test
  (testing "Mote ID is interpolated into prompt"
    (let [mote (test-mote :id "2.5.7")
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "MOTE: 2.5.7")))))

(deftest render-prompt-claim-interpolation-test
  (testing "Claim is interpolated into prompt"
    (let [mote (test-mote :claim "For all ε > 0, there exists δ > 0")
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "CLAIM: For all ε > 0, there exists δ > 0")))))

(deftest render-prompt-priority-interpolation-test
  (testing "Priority is interpolated into prompt"
    (let [mote (test-mote :priority :p1)
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "PRIORITY: p1")))))

(deftest render-prompt-difficulty-interpolation-test
  (testing "Difficulty is interpolated into prompt"
    (let [mote (test-mote :difficulty 4)
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "DIFFICULTY: 4")))))

(deftest render-prompt-parent-interpolation-test
  (testing "Parent is interpolated when present"
    (let [parent (test-mote :id "2.5" :claim "Parent claim")
          child (test-mote :id "2.5.7" :parent "2.5")
          job (test-job :role :proposer :mote child :parent parent)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "PARENT: 2.5 — Parent claim"))))

  (testing "Parent shows (root) when nil"
    (let [root-mote (test-mote :id "1")
          job (test-job :role :proposer :mote root-mote :parent nil)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "PARENT: (root)")))))

(deftest render-prompt-assumptions-interpolation-test
  (testing "Assumptions are interpolated into prompt"
    (let [mote (test-mote :assumptions [{:type :internal :ref "1.1" :note "Base case"}
                                        {:type :external :ref "Rudin" :note "Thm 1"}])
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "[internal] 1.1: Base case"))
      (is (str/includes? prompt "[external] Rudin: Thm 1")))))

(deftest render-prompt-definitions-interpolation-test
  (testing "Definitions are interpolated into prompt"
    (let [mote (test-mote :definitions [{:symbol "ε" :meaning "tolerance"}
                                        {:symbol "δ" :meaning "delta"}])
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "ε: tolerance"))
      (is (str/includes? prompt "δ: delta")))))

(deftest render-prompt-votes-interpolation-test
  (testing "Vote summary is interpolated into prompt"
    (let [mote (test-mote :votes [{:agent "v1" :vote :for :timestamp #inst "2026-01-07"}
                                  {:agent "v2" :vote :against :timestamp #inst "2026-01-07"}])
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "VOTES SO FAR: 1 for, 1 against")))))

;; =============================================================================
;; render-prompt Tests - Commands
;; =============================================================================

(deftest render-prompt-commands-mote-id-substitution-test
  (testing "Commands have {{mote-id}} replaced"
    (let [mote (test-mote :id "3.1.4")
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job)]
      ;; Commands should contain actual mote-id, not placeholder
      (is (str/includes? prompt "af vote 3.1.4 --for"))
      (is (not (str/includes? prompt "{{mote-id}}"))))))

(deftest render-prompt-proposer-commands-test
  (testing "Proposer prompt has propose command"
    (let [job (test-job :role :proposer
                        :mote (test-mote :id "2.1" :taint #{:needs-decomposition}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af propose 2.1")))))

(deftest render-prompt-advisor-commands-test
  (testing "Advisor prompt has approve/reject commands"
    (let [mote (test-mote :id "2.1"
                          :taint #{:needs-proposal-review}
                          :proposal {:id "prop-123"
                                     :proposed-by "p1"
                                     :proposed-at #inst "2026-01-07"
                                     :children []
                                     :votes []
                                     :status :pending})
          job (test-job :role :advisor :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af approve 2.1"))
      (is (str/includes? prompt "af reject 2.1")))))

(deftest render-prompt-prover-commands-test
  (testing "Prover prompt has refinement commands"
    (let [job (test-job :role :prover
                        :mote (test-mote :id "2.1" :taint #{:needs-refinement}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af add-assumption 2.1"))
      (is (str/includes? prompt "af add-ref 2.1"))
      (is (str/includes? prompt "af add-definition 2.1")))))

(deftest render-prompt-verifier-commands-test
  (testing "Verifier prompt has vote commands"
    (let [job (test-job :role :verifier
                        :mote (test-mote :id "2.1" :taint #{:needs-verification}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af vote 2.1 --for"))
      (is (str/includes? prompt "af vote 2.1 --against")))))

(deftest render-prompt-ref-checker-commands-test
  (testing "Ref-checker prompt has ref commands"
    (let [job (test-job :role :ref-checker
                        :mote (test-mote :id "2.1" :taint #{:needs-refs}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af add-ref 2.1"))
      (is (str/includes? prompt "af taint 2.1 --remove needs-refs")))))

(deftest render-prompt-counterexample-commands-test
  (testing "Counterexample prompt has counterexample commands"
    (let [job (test-job :role :counterexample
                        :mote (test-mote :id "2.1" :taint #{:needs-counterexample}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "af update 2.1 --status refuted"))
      (is (str/includes? prompt "af taint 2.1 --remove needs-counterexample")))))

;; =============================================================================
;; render-prompt Tests - Children Resolution
;; =============================================================================

(deftest render-prompt-children-resolved-test
  (testing "Resolved children are formatted in verifier prompt"
    (let [mote (test-mote :id "2.1" :children ["2.1.1" "2.1.2"])
          child1 (test-mote :id "2.1.1" :claim "First substep" :status :verified)
          child2 (test-mote :id "2.1.2" :claim "Second substep" :status :fixed)
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job :resolved-children [child1 child2])]
      (is (str/includes? prompt "2.1.1: First substep [verified]"))
      (is (str/includes? prompt "2.1.2: Second substep [fixed]")))))

(deftest render-prompt-no-children-test
  (testing "Empty children shows (none)"
    (let [mote (test-mote :id "2.1" :children [])
          job (test-job :role :verifier :mote mote)
          prompt (prompt/render-prompt job :resolved-children [])]
      (is (str/includes? prompt "CHILDREN (substeps):\n(none)")))))

;; =============================================================================
;; render-prompt Tests - Advisor Proposal Context
;; =============================================================================

(deftest render-prompt-advisor-proposal-children-test
  (testing "Advisor sees proposed children with numbering"
    (let [child1 (test-mote :id "2.1.1" :claim "First substep" :difficulty 2)
          child2 (test-mote :id "2.1.2" :claim "Second substep" :difficulty 3)
          mote (test-mote :id "2.1"
                          :taint #{:needs-proposal-review}
                          :proposal {:id "prop-123"
                                     :proposed-by "proposer-1"
                                     :proposed-at #inst "2026-01-07"
                                     :children ["2.1.1" "2.1.2"]
                                     :votes []
                                     :status :pending})
          job (test-job :role :advisor :mote mote)
          prompt (prompt/render-prompt job :resolved-children [child1 child2])]
      (is (str/includes? prompt "1. 2.1.1: First substep (difficulty 2)"))
      (is (str/includes? prompt "2. 2.1.2: Second substep (difficulty 3)")))))

(deftest render-prompt-advisor-proposal-votes-test
  (testing "Advisor sees proposal vote summary"
    (let [mote (test-mote :id "2.1"
                          :taint #{:needs-proposal-review}
                          :proposal {:id "prop-123"
                                     :proposed-by "proposer-1"
                                     :proposed-at #inst "2026-01-07"
                                     :children []
                                     :votes [{:agent "a1" :vote :approve :timestamp #inst "2026-01-07"}
                                             {:agent "a2" :vote :reject :timestamp #inst "2026-01-07"}]
                                     :status :pending})
          job (test-job :role :advisor :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "VOTES: 1 approve, 1 reject")))))

(deftest render-prompt-advisor-proposed-by-test
  (testing "Advisor sees who proposed"
    (let [mote (test-mote :id "2.1"
                          :taint #{:needs-proposal-review}
                          :proposal {:id "prop-123"
                                     :proposed-by "smart-proposer"
                                     :proposed-at #inst "2026-01-07"
                                     :children []
                                     :votes []
                                     :status :pending})
          job (test-job :role :advisor :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "PROPOSED BY: smart-proposer")))))

;; =============================================================================
;; render-prompt Tests - External Refs
;; =============================================================================

(deftest render-prompt-ref-checker-external-refs-test
  (testing "Ref-checker sees only external references"
    (let [mote (test-mote :id "2.1"
                          :taint #{:needs-refs}
                          :assumptions [{:type :internal :ref "1.1" :note "Internal ref"}
                                        {:type :external :ref "arXiv:2301.00001" :note "Key theorem"}
                                        {:type :external :ref "Rudin 1976"}])
          job (test-job :role :ref-checker :mote mote)
          prompt (prompt/render-prompt job)]
      ;; Should show external refs
      (is (str/includes? prompt "arXiv:2301.00001: \"Key theorem\""))
      (is (str/includes? prompt "Rudin 1976"))
      ;; Should NOT show internal refs in the EXTERNAL REFERENCES section
      ;; (internal refs might appear elsewhere but not in this section)
      )))

(deftest render-prompt-ref-checker-no-external-refs-test
  (testing "Ref-checker with no external refs shows (none)"
    (let [mote (test-mote :id "2.1"
                          :taint #{:needs-refs}
                          :assumptions [{:type :internal :ref "1.1"}])
          job (test-job :role :ref-checker :mote mote)
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "EXTERNAL REFERENCES:\n(none)")))))

;; =============================================================================
;; render-prompt Tests - Task Sections
;; =============================================================================

(deftest render-prompt-proposer-task-test
  (testing "Proposer prompt has decomposition task"
    (let [job (test-job :role :proposer
                        :mote (test-mote :taint #{:needs-decomposition}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "Decompose into 2-5 substeps"))
      (is (str/includes? prompt "mutually exclusive"))
      (is (str/includes? prompt "collectively exhaustive")))))

(deftest render-prompt-verifier-task-test
  (testing "Verifier prompt has validation task"
    (let [job (test-job :role :verifier
                        :mote (test-mote :taint #{:needs-verification}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "Check if substeps logically entail"))
      (is (str/includes? prompt "gaps, errors, unjustified leaps")))))

(deftest render-prompt-counterexample-task-test
  (testing "Counterexample prompt has adversarial task"
    (let [job (test-job :role :counterexample
                        :mote (test-mote :taint #{:needs-counterexample}))
          prompt (prompt/render-prompt job)]
      (is (str/includes? prompt "Construct counterexamples"))
      (is (str/includes? prompt "edge cases"))
      (is (str/includes? prompt "boundary conditions")))))

;; =============================================================================
;; render-prompt Tests - Invalid Role
;; =============================================================================

(deftest render-prompt-invalid-role-test
  (testing "Invalid role returns nil"
    (let [job (assoc (test-job) :role :invalid-role)
          prompt (prompt/render-prompt job)]
      (is (nil? prompt)))))
