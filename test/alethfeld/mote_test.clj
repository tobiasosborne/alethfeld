(ns alethfeld.mote-test
  "Tests for alethfeld.mote namespace."
  (:require [clojure.test :refer [deftest is testing]]
            [alethfeld.mote :as m]
            [alethfeld.schema :as s]))

;; -----------------------------------------------------------------------------
;; Vote Constructor Tests
;; -----------------------------------------------------------------------------

(deftest make-vote-test
  (testing "make-vote creates valid verification vote"
    (let [vote (m/make-vote "verifier-1" :for)]
      (is (s/valid? s/Vote vote))
      (is (= "verifier-1" (:agent vote)))
      (is (= :for (:vote vote)))
      (is (inst? (:timestamp vote)))
      (is (nil? (:reason vote)))))

  (testing "make-vote with optional reason"
    (let [vote (m/make-vote "verifier-2" :against :reason "Gap in logic")]
      (is (s/valid? s/Vote vote))
      (is (= :against (:vote vote)))
      (is (= "Gap in logic" (:reason vote)))))

  (testing "make-vote with explicit timestamp"
    (let [ts #inst "2026-01-07T12:00:00Z"
          vote (m/make-vote "v1" :for :timestamp ts)]
      (is (= ts (:timestamp vote))))))

(deftest make-proposal-vote-test
  (testing "make-proposal-vote creates valid proposal vote"
    (let [vote (m/make-proposal-vote "advisor-1" :approve)]
      (is (s/valid? s/ProposalVote vote))
      (is (= "advisor-1" (:agent vote)))
      (is (= :approve (:vote vote)))
      (is (inst? (:timestamp vote)))))

  (testing "make-proposal-vote with reject"
    (let [vote (m/make-proposal-vote "advisor-2" :reject :reason "Incomplete")]
      (is (s/valid? s/ProposalVote vote))
      (is (= :reject (:vote vote)))
      (is (= "Incomplete" (:reason vote))))))

;; -----------------------------------------------------------------------------
;; Proposal Constructor Tests
;; -----------------------------------------------------------------------------

(deftest make-proposal-test
  (testing "make-proposal creates valid proposal with defaults"
    (let [proposal (m/make-proposal "proposer-1" ["1.1" "1.2"])]
      (is (s/valid? s/Proposal proposal))
      (is (string? (:id proposal)))
      (is (clojure.string/starts-with? (:id proposal) "prop-"))
      (is (= "proposer-1" (:proposed-by proposal)))
      (is (= ["1.1" "1.2"] (:children proposal)))
      (is (= [] (:votes proposal)))
      (is (= :pending (:status proposal)))
      (is (inst? (:proposed-at proposal)))))

  (testing "make-proposal with explicit options"
    (let [ts #inst "2026-01-07T12:00:00Z"
          votes [(m/make-proposal-vote "adv" :approve :timestamp ts)]
          proposal (m/make-proposal "p1" ["2.1"]
                                    :id "custom-id"
                                    :proposed-at ts
                                    :votes votes
                                    :status :approved)]
      (is (s/valid? s/Proposal proposal))
      (is (= "custom-id" (:id proposal)))
      (is (= ts (:proposed-at proposal)))
      (is (= 1 (count (:votes proposal))))
      (is (= :approved (:status proposal))))))

;; -----------------------------------------------------------------------------
;; Mote Constructor Tests
;; -----------------------------------------------------------------------------

(deftest make-mote-test
  (testing "make-mote creates valid mote with defaults"
    (let [mote (m/make-mote "1.2.3" "For all e > 0..." "prover-1")]
      (is (s/valid? s/Mote mote))
      (is (= "1.2.3" (:id mote)))
      (is (= "For all e > 0..." (:claim mote)))
      (is (= "prover-1" (:created-by mote)))
      (is (= :fixed (:status mote)))
      (is (= #{:needs-verification} (:taint mote)))
      (is (= :p2 (:priority mote)))
      (is (= 3 (:difficulty mote)))
      (is (= [] (:children mote)))
      (is (= [] (:assumptions mote)))
      (is (= [] (:definitions mote)))
      (is (= [] (:votes mote)))
      (is (nil? (:parent mote)))
      (is (nil? (:claimed-by mote)))
      (is (inst? (:created-at mote)))
      (is (inst? (:updated-at mote)))))

  (testing "make-mote with explicit options"
    (let [ts #inst "2026-01-07T12:00:00Z"
          mote (m/make-mote "2" "Root claim" "human"
                            :status :verified
                            :taint #{:needs-votes}
                            :priority :p1
                            :difficulty 5
                            :created-at ts
                            :updated-at ts)]
      (is (s/valid? s/Mote mote))
      (is (= :verified (:status mote)))
      (is (= #{:needs-votes} (:taint mote)))
      (is (= :p1 (:priority mote)))
      (is (= 5 (:difficulty mote)))
      (is (= ts (:created-at mote)))))

  (testing "make-mote with parent and children"
    (let [mote (m/make-mote "1.2" "Child claim" "agent"
                            :parent "1"
                            :children ["1.2.1" "1.2.2"])]
      (is (s/valid? s/Mote mote))
      (is (= "1" (:parent mote)))
      (is (= ["1.2.1" "1.2.2"] (:children mote)))))

  (testing "make-mote with nested structures"
    (let [ts #inst "2026-01-07T12:00:00Z"
          mote (m/make-mote "1" "Claim" "agent"
                            :assumptions [{:type :internal :ref "0" :note "Base case"}
                                          {:type :external :ref "arXiv:123"}]
                            :definitions [{:symbol "x" :meaning "variable"}]
                            :votes [(m/make-vote "v1" :for :timestamp ts)])]
      (is (s/valid? s/Mote mote))
      (is (= 2 (count (:assumptions mote))))
      (is (= 1 (count (:definitions mote))))
      (is (= 1 (count (:votes mote))))))

  (testing "make-mote with claimed-by"
    (let [ts #inst "2026-01-07T12:00:00Z"
          mote (m/make-mote "1" "Claim" "agent"
                            :claimed-by "worker-1"
                            :claimed-at ts)]
      (is (s/valid? s/Mote mote))
      (is (= "worker-1" (:claimed-by mote)))
      (is (= ts (:claimed-at mote))))))

;; -----------------------------------------------------------------------------
;; Root Mote Constructor Tests
;; -----------------------------------------------------------------------------

(deftest make-root-mote-test
  (testing "make-root-mote creates valid root mote"
    (let [mote (m/make-root-mote "1" "Root theorem" "human")]
      (is (s/valid? s/Mote mote))
      (is (= "1" (:id mote)))
      (is (nil? (:parent mote)))
      (is (= :p2 (:priority mote)))
      (is (= 3 (:difficulty mote)))))

  (testing "make-root-mote with explicit priority/difficulty"
    (let [mote (m/make-root-mote "2" "Hard theorem" "human"
                                  :priority :p0
                                  :difficulty 5)]
      (is (s/valid? s/Mote mote))
      (is (= :p0 (:priority mote)))
      (is (= 5 (:difficulty mote))))))

;; -----------------------------------------------------------------------------
;; Child Mote Constructor Tests
;; -----------------------------------------------------------------------------

(deftest make-child-mote-test
  (testing "make-child-mote inherits from parent"
    (let [parent (m/make-root-mote "1" "Parent" "human" :priority :p1 :difficulty 4)
          child (m/make-child-mote "1.1" "Child step" "agent" parent)]
      (is (s/valid? s/Mote child))
      (is (= "1.1" (:id child)))
      (is (= "1" (:parent child)))
      (is (= :p1 (:priority child)) "Should inherit parent's priority")
      (is (= 4 (:difficulty child)) "Should inherit parent's difficulty")))

  (testing "make-child-mote can override inherited values"
    (let [parent (m/make-root-mote "1" "Parent" "human" :priority :p1 :difficulty 4)
          child (m/make-child-mote "1.1" "Easy step" "agent" parent
                                    :priority :p3
                                    :difficulty 1)]
      (is (s/valid? s/Mote child))
      (is (= :p3 (:priority child)))
      (is (= 1 (:difficulty child)))))

  (testing "make-child-mote with other options"
    (let [parent (m/make-root-mote "1" "Parent" "human")
          child (m/make-child-mote "1.1" "Substep" "agent" parent
                                    :taint #{:needs-verification}
                                    :status :proposed)]
      (is (s/valid? s/Mote child))
      (is (= #{:needs-verification} (:taint child)))
      (is (= :proposed (:status child))))))

;; -----------------------------------------------------------------------------
;; Validation Helper Tests
;; -----------------------------------------------------------------------------

(deftest valid-mote?-test
  (testing "valid-mote? returns true for valid mote"
    (let [mote (m/make-mote "1" "Claim" "agent")]
      (is (true? (m/valid-mote? mote)))))

  (testing "valid-mote? returns false for invalid mote"
    (is (false? (m/valid-mote? {:id "1"})))))

(deftest valid-proposal?-test
  (testing "valid-proposal? returns true for valid proposal"
    (let [proposal (m/make-proposal "agent" ["1.1"])]
      (is (true? (m/valid-proposal? proposal)))))

  (testing "valid-proposal? returns false for invalid proposal"
    (is (false? (m/valid-proposal? {:id "x"})))))

(deftest valid-vote?-test
  (testing "valid-vote? returns true for valid vote"
    (let [vote (m/make-vote "agent" :for)]
      (is (true? (m/valid-vote? vote)))))

  (testing "valid-vote? returns false for invalid vote"
    (is (false? (m/valid-vote? {:agent "x"})))))

(deftest valid-proposal-vote?-test
  (testing "valid-proposal-vote? returns true for valid proposal vote"
    (let [vote (m/make-proposal-vote "agent" :approve)]
      (is (true? (m/valid-proposal-vote? vote)))))

  (testing "valid-proposal-vote? returns false for invalid proposal vote"
    (is (false? (m/valid-proposal-vote? {:agent "x" :vote :for})))))

;; -----------------------------------------------------------------------------
;; ID Generation Tests
;; -----------------------------------------------------------------------------

(deftest generate-id-test
  (testing "generate-id creates unique IDs"
    (let [ids (repeatedly 100 m/generate-id)]
      (is (= 100 (count (set ids))) "All IDs should be unique")))

  (testing "generate-id format is correct"
    (let [id (m/generate-id)]
      (is (re-matches #"\d{8}-\d{9}-[0-9a-f]{4}" id)))))

;; -----------------------------------------------------------------------------
;; Mote Transformation Tests
;; -----------------------------------------------------------------------------

(defn- base-mote
  "Create a base mote for transformation tests."
  []
  (m/make-mote "1" "Test claim" "agent"))

(deftest add-assumption-test
  (testing "add-assumption adds to assumptions vector"
    (let [mote (base-mote)
          assumption {:type :internal :ref "2" :note "dependency"}
          result (m/add-assumption mote assumption)]
      (is (s/valid? s/Mote result))
      (is (= 1 (count (:assumptions result))))
      (is (= assumption (first (:assumptions result))))))

  (testing "add-assumption appends to existing assumptions"
    (let [existing {:type :external :ref "arXiv:123"}
          mote (m/make-mote "1" "Claim" "agent" :assumptions [existing])
          new-assumption {:type :internal :ref "2"}
          result (m/add-assumption mote new-assumption)]
      (is (= 2 (count (:assumptions result))))
      (is (= existing (first (:assumptions result))))
      (is (= new-assumption (second (:assumptions result)))))))

(deftest add-definition-test
  (testing "add-definition adds to definitions vector"
    (let [mote (base-mote)
          definition {:symbol "x" :meaning "a variable"}
          result (m/add-definition mote definition)]
      (is (s/valid? s/Mote result))
      (is (= 1 (count (:definitions result))))
      (is (= definition (first (:definitions result)))))))

(deftest add-dep-test
  (testing "add-dep adds to depends-on vector"
    (let [mote (base-mote)
          dep {:ref "2" :reason "uses evenness lemma"}
          result (m/add-dep mote dep)]
      (is (s/valid? s/Mote result))
      (is (= 1 (count (:depends-on result))))
      (is (= dep (first (:depends-on result))))))

  (testing "add-dep creates depends-on if not present"
    (let [mote (base-mote)
          dep {:ref "2"}
          result (m/add-dep mote dep)]
      (is (vector? (:depends-on result)))
      (is (= 1 (count (:depends-on result))))))

  (testing "add-dep appends to existing dependencies"
    (let [mote (assoc (base-mote) :depends-on [{:ref "1"}])
          new-dep {:ref "2" :reason "also depends"}
          result (m/add-dep mote new-dep)]
      (is (= 2 (count (:depends-on result))))
      (is (= "1" (:ref (first (:depends-on result)))))
      (is (= "2" (:ref (second (:depends-on result))))))))

(deftest add-vote-test
  (testing "add-vote adds to votes vector"
    (let [mote (base-mote)
          vote (m/make-vote "verifier-1" :for)
          result (m/add-vote mote vote)]
      (is (s/valid? s/Mote result))
      (is (= 1 (count (:votes result))))
      (is (= "verifier-1" (:agent (first (:votes result))))))))

(deftest add-taint-test
  (testing "add-taint adds flag to taint set"
    (let [mote (m/make-mote "1" "Claim" "agent" :taint #{})
          result (m/add-taint mote :needs-verification)]
      (is (s/valid? s/Mote result))
      (is (contains? (:taint result) :needs-verification))))

  (testing "add-taint is idempotent"
    (let [mote (m/make-mote "1" "Claim" "agent" :taint #{:needs-verification})
          result (m/add-taint mote :needs-verification)]
      (is (= #{:needs-verification} (:taint result))))))

(deftest remove-taint-test
  (testing "remove-taint removes flag from taint set"
    (let [mote (m/make-mote "1" "Claim" "agent" :taint #{:needs-decomposition :needs-verification})
          result (m/remove-taint mote :needs-decomposition)]
      (is (s/valid? s/Mote result))
      (is (not (contains? (:taint result) :needs-decomposition)))
      (is (contains? (:taint result) :needs-verification))))

  (testing "remove-taint is idempotent for missing flags"
    (let [mote (m/make-mote "1" "Claim" "agent" :taint #{})
          result (m/remove-taint mote :needs-decomposition)]
      (is (= #{} (:taint result))))))

(deftest set-status-test
  (testing "set-status changes mote status"
    (let [mote (base-mote)
          result (m/set-status mote :verified)]
      (is (s/valid? s/Mote result))
      (is (= :verified (:status result)))))

  (testing "set-status updates updated-at timestamp"
    (let [ts #inst "2026-01-01T00:00:00Z"
          mote (m/make-mote "1" "Claim" "agent" :updated-at ts)
          result (m/set-status mote :verified)]
      (is (not= ts (:updated-at result))))))

(deftest set-claimed-by-test
  (testing "set-claimed-by sets agent and timestamp"
    (let [mote (base-mote)
          result (m/set-claimed-by mote "worker-1")]
      (is (s/valid? s/Mote result))
      (is (= "worker-1" (:claimed-by result)))
      (is (inst? (:claimed-at result))))))

(deftest clear-claim-test
  (testing "clear-claim removes claimed-by and claimed-at"
    (let [mote (m/make-mote "1" "Claim" "agent"
                            :claimed-by "worker-1"
                            :claimed-at #inst "2026-01-07T12:00:00Z")
          result (m/clear-claim mote)]
      (is (s/valid? s/Mote result))
      (is (nil? (:claimed-by result)))
      (is (nil? (:claimed-at result))))))

(deftest set-proposal-test
  (testing "set-proposal adds proposal to mote"
    (let [mote (base-mote)
          proposal (m/make-proposal "proposer" ["1.1" "1.2"])
          result (m/set-proposal mote proposal)]
      (is (s/valid? s/Mote result))
      (is (some? (:proposal result)))
      (is (= ["1.1" "1.2"] (get-in result [:proposal :children]))))))

(deftest clear-proposal-test
  (testing "clear-proposal removes proposal from mote"
    (let [proposal (m/make-proposal "proposer" ["1.1"])
          mote (m/make-mote "1" "Claim" "agent" :proposal proposal)
          result (m/clear-proposal mote)]
      (is (s/valid? s/Mote result))
      (is (nil? (:proposal result))))))

(deftest add-child-test
  (testing "add-child appends child ID to children vector"
    (let [mote (base-mote)
          result (m/add-child mote "1.1")]
      (is (s/valid? s/Mote result))
      (is (= ["1.1"] (:children result)))))

  (testing "add-child appends to existing children"
    (let [mote (m/make-mote "1" "Claim" "agent" :children ["1.1"])
          result (m/add-child mote "1.2")]
      (is (= ["1.1" "1.2"] (:children result))))))

(deftest set-priority-test
  (testing "set-priority changes priority"
    (let [mote (base-mote)
          result (m/set-priority mote :p0)]
      (is (s/valid? s/Mote result))
      (is (= :p0 (:priority result))))))

(deftest set-difficulty-test
  (testing "set-difficulty changes difficulty"
    (let [mote (base-mote)
          result (m/set-difficulty mote 5)]
      (is (s/valid? s/Mote result))
      (is (= 5 (:difficulty result))))))

(deftest set-claim-test
  (testing "set-claim changes claim text"
    (let [mote (base-mote)
          result (m/set-claim mote "Updated claim text")]
      (is (s/valid? s/Mote result))
      (is (= "Updated claim text" (:claim result))))))

;; -----------------------------------------------------------------------------
;; Claim Expiration Tests
;; -----------------------------------------------------------------------------

(deftest claim-expired-test
  (testing "claim-expired? returns false for unclaimed mote"
    (let [mote (base-mote)]
      (is (false? (m/claim-expired? mote 30)))))

  (testing "claim-expired? returns false for mote with no claimed-at"
    (let [mote (assoc (base-mote) :claimed-by "agent-1")]
      (is (false? (m/claim-expired? mote 30)))))

  (testing "claim-expired? returns false for fresh claim"
    (let [mote (m/set-claimed-by (base-mote) "agent-1")]
      (is (false? (m/claim-expired? mote 30)))))

  (testing "claim-expired? returns true for expired claim"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 60 60 1000))) ;; 60 minutes ago
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at old-time))]
      (is (true? (m/claim-expired? mote 30)))))

  (testing "claim-expired? respects timeout value"
    (let [old-time (java.util.Date. (- (.getTime (java.util.Date.)) (* 20 60 1000))) ;; 20 minutes ago
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at old-time))]
      ;; Not expired with 30-minute timeout
      (is (false? (m/claim-expired? mote 30)))
      ;; Expired with 15-minute timeout
      (is (true? (m/claim-expired? mote 15)))))

  (testing "claim-expired? with explicit now parameter for consistent comparisons"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at claimed-time))
          ;; 29 minutes later - not expired with 30 min timeout
          now-29min (.plus base-instant (java.time.Duration/ofMinutes 29))
          ;; 31 minutes later - expired with 30 min timeout
          now-31min (.plus base-instant (java.time.Duration/ofMinutes 31))]
      (is (false? (m/claim-expired? mote 30 :now now-29min)))
      (is (true? (m/claim-expired? mote 30 :now now-31min)))))

  (testing "claim-expired? boundary condition: exactly at expiration time"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at claimed-time))
          ;; Exactly 30 minutes later - NOT expired (boundary is exclusive)
          now-exactly-30min (.plus base-instant (java.time.Duration/ofMinutes 30))]
      ;; At exactly the boundary, isAfter returns false (not strictly after)
      (is (false? (m/claim-expired? mote 30 :now now-exactly-30min)))))

  (testing "claim-expired? boundary condition: one millisecond after expiration"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at claimed-time))
          ;; 30 minutes + 1 millisecond - now expired
          now-just-after (.plus base-instant (java.time.Duration/ofMinutes 30))
          now-just-after (.plusMillis now-just-after 1)]
      (is (true? (m/claim-expired? mote 30 :now now-just-after)))))

  (testing "claim-expired? boundary condition: one millisecond before expiration"
    (let [base-instant (java.time.Instant/parse "2026-01-07T12:00:00Z")
          claimed-time (java.util.Date/from base-instant)
          mote (-> (base-mote)
                   (assoc :claimed-by "agent-1")
                   (assoc :claimed-at claimed-time))
          ;; 30 minutes - 1 millisecond - not expired
          now-just-before (.plus base-instant (java.time.Duration/ofMinutes 30))
          now-just-before (.minusMillis now-just-before 1)]
      (is (false? (m/claim-expired? mote 30 :now now-just-before))))))

;; -----------------------------------------------------------------------------
;; Claim Text Edge Cases
;; -----------------------------------------------------------------------------

(deftest claim-text-edge-cases-test
  (testing "Empty claim text - behavior documentation"
    ;; An empty claim provides no meaningful information.
    ;; Note: Current schema allows empty strings. This test documents behavior.
    (let [mote (m/make-mote "1" "" "agent")]
      ;; DOCUMENTED BEHAVIOR: Empty claims currently pass validation.
      ;; This may be considered a bug - claims should arguably be non-empty.
      (is (s/valid? s/Mote mote) "Current behavior: empty claims are accepted")))

  (testing "Very long claim text (10K+ characters) should be valid"
    ;; Mathematical proofs can require very long, detailed claims.
    ;; There should be no artificial length limit on claim text.
    (let [long-claim (apply str (repeat 10000 "x"))
          mote (m/make-mote "1" long-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= 10000 (count (:claim mote))))))

  (testing "Extremely long claim text (100K+ characters) should be valid"
    ;; Ensure no practical length limit exists
    (let [very-long-claim (apply str (repeat 100000 "a"))
          mote (m/make-mote "1" very-long-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= 100000 (count (:claim mote))))))

  (testing "Unicode characters in claims should be valid"
    ;; Mathematical proofs use Greek letters, mathematical symbols, etc.
    (let [unicode-claim "For all e > 0, there exists d > 0 such that |x - x0| < d implies |f(x) - L| < e"
          mote (m/make-mote "1" unicode-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= unicode-claim (:claim mote)))))

  (testing "Mathematical symbols and Greek letters should be valid"
    (let [math-claim "For all x in R, integral from 0 to infinity of e^(-x^2) dx = sqrt(pi)/2. Also: alpha beta gamma delta in Sigma"
          mote (m/make-mote "1" math-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= math-claim (:claim mote)))))

  (testing "Emoji in claims should be valid"
    ;; While unusual for formal proofs, emoji are valid Unicode and should work.
    (let [emoji-claim "The target of this proof is to show num + num = 2*num"
          mote (m/make-mote "1" emoji-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= emoji-claim (:claim mote)))))

  (testing "Claims with newlines should be valid"
    ;; Multi-line claims are common for complex mathematical statements.
    (let [multiline-claim "Let f: X -> Y be a continuous function.\nThen:\n  1. f preserves limits\n  2. f^(-1)(open) is open"
          mote (m/make-mote "1" multiline-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= multiline-claim (:claim mote)))))

  (testing "Claims with carriage returns and tabs should be valid"
    ;; Various whitespace characters should all be preserved.
    (let [formatted-claim "Line1\r\nLine2\tindented"
          mote (m/make-mote "1" formatted-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= formatted-claim (:claim mote)))))

  (testing "Claims with special characters (quotes, backslashes) should be valid"
    ;; These are common in mathematical notation and examples.
    (let [special-claim "Let \"x\" be s.t. x \\ {0} is not empty. Also: a\\b and c/d."
          mote (m/make-mote "1" special-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= special-claim (:claim mote)))))

  (testing "Claims with EDN-special characters should be valid"
    ;; Braces, brackets, semicolons - all valid in claims
    (let [edn-special-claim "Consider {a, b, c} where [a, b] subset S; then (a + b) = c"
          mote (m/make-mote "1" edn-special-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= edn-special-claim (:claim mote)))))

  (testing "Claims with leading/trailing whitespace - behavior documentation"
    ;; Current behavior: whitespace is preserved as-is
    (let [leading-ws "   Leading spaces claim"
          trailing-ws "Trailing spaces claim   "
          both-ws "   Both sides   "
          leading-mote (m/make-mote "1" leading-ws "agent")
          trailing-mote (m/make-mote "2" trailing-ws "agent")
          both-mote (m/make-mote "3" both-ws "agent")]
      ;; DOCUMENTED BEHAVIOR: Whitespace is NOT trimmed
      (is (s/valid? s/Mote leading-mote))
      (is (s/valid? s/Mote trailing-mote))
      (is (s/valid? s/Mote both-mote))
      (is (= leading-ws (:claim leading-mote)) "Leading whitespace preserved")
      (is (= trailing-ws (:claim trailing-mote)) "Trailing whitespace preserved")
      (is (= both-ws (:claim both-mote)) "Both-sides whitespace preserved")))

  (testing "Whitespace-only claims - behavior documentation"
    ;; DOCUMENTED BEHAVIOR: Currently accepted but arguably should fail.
    ;; A claim that is only whitespace provides no meaningful information.
    (let [space-only "     "
          tabs-only "\t\t\t"
          mixed-ws " \t \n \r "
          space-mote (m/make-mote "1" space-only "agent")
          tab-mote (m/make-mote "2" tabs-only "agent")
          mixed-mote (m/make-mote "3" mixed-ws "agent")]
      (is (s/valid? s/Mote space-mote) "Current behavior: space-only claims accepted")
      (is (s/valid? s/Mote tab-mote) "Current behavior: tab-only claims accepted")
      (is (s/valid? s/Mote mixed-mote) "Current behavior: mixed whitespace claims accepted")))

  (testing "Claims with null bytes should be handled"
    ;; Null bytes are unusual but technically valid string characters
    (let [null-claim "Before\u0000After"
          mote (m/make-mote "1" null-claim "agent")]
      ;; Null bytes in strings are valid in Clojure
      (is (s/valid? s/Mote mote))
      (is (= null-claim (:claim mote)))))

  (testing "Claims with combining characters should be valid"
    ;; Combining diacritical marks are common in international mathematics
    (let [combining-claim "e with acute = e\u0301, n with tilde = n\u0303"  ; combining accent and tilde
          mote (m/make-mote "1" combining-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= combining-claim (:claim mote)))))

  (testing "Claims with right-to-left text should be valid"
    ;; Some mathematical notation or citations may use RTL languages
    (let [rtl-claim "Consider the Hebrew letter aleph in set theory"
          mote (m/make-mote "1" rtl-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= rtl-claim (:claim mote)))))

  (testing "make-root-mote with edge case claims"
    (let [complex-claim "For all epsilon>0 there exists delta>0: |x-a|<delta implies |f(x)-f(a)|<epsilon\nLine2\t\"quoted\""
          mote (m/make-root-mote "1" complex-claim "agent")]
      (is (s/valid? s/Mote mote))
      (is (= complex-claim (:claim mote)))))

  (testing "make-child-mote with edge case claims"
    (let [parent (m/make-root-mote "1" "Parent" "agent")
          child-claim "Child: integral sum product with\nnewlines"
          child (m/make-child-mote "1.1" child-claim "agent" parent)]
      (is (s/valid? s/Mote child))
      (is (= child-claim (:claim child)))))

  (testing "set-claim with edge case values"
    (let [mote (base-mote)
          unicode-result (m/set-claim mote "Updated: epsilon approaches 0")
          newline-result (m/set-claim mote "Line1\nLine2")
          long-result (m/set-claim mote (apply str (repeat 5000 "x")))]
      (is (s/valid? s/Mote unicode-result))
      (is (s/valid? s/Mote newline-result))
      (is (s/valid? s/Mote long-result))
      (is (= "Updated: epsilon approaches 0" (:claim unicode-result)))
      (is (= "Line1\nLine2" (:claim newline-result)))
      (is (= 5000 (count (:claim long-result)))))))
