(ns alethfeld.integration-realistic-test
  "Integration tests with realistic data and proper isolation.

   Improvements over basic integration tests:
   1. Generated IDs - No hardcoded :1-abc123 style IDs
   2. Realistic statements - Lean/LaTeX style, kilobyte-sized
   3. Transaction-style isolation - Each test starts fresh
   4. Complex mathematical content - Greek letters, formulas, proofs

   These tests simulate real proof development workflows with
   production-realistic data sizes and content."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.string :as str]
            [alethfeld.ops.init :as init]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.ops.delete-node :as delete-node]
            [alethfeld.ops.replace-node :as replace-node]
            [alethfeld.ops.extract-lemma :as extract-lemma]
            [alethfeld.ops.external-ref :as external-ref]
            [alethfeld.graph :as graph]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as validators]
            [alethfeld.fixtures :refer [make-partial-node]]))

;; =============================================================================
;; ID Generation - No Hardcoded IDs
;; =============================================================================

(defn gen-id
  "Generate a unique node ID with given depth prefix.
   Format: :<depth>-<random-hex>"
  ([] (gen-id 1))
  ([depth]
   (keyword (str depth "-" (format "%06x" (rand-int 0xFFFFFF))))))

(defn gen-assumption-id
  "Generate ID for assumption (depth 0)."
  []
  (gen-id 0))

(defn gen-claim-id
  "Generate ID for claim (depth 1)."
  []
  (gen-id 1))

(defn gen-graph-id
  "Generate unique graph ID."
  []
  (str "graph-" (System/currentTimeMillis) "-" (format "%04x" (rand-int 0xFFFF))))

;; =============================================================================
;; Realistic Statement Generators - Lean/LaTeX Style
;; =============================================================================

(def fourier-theorem-statement
  "For U = I - 2|\\psi\\rangle\\langle\\psi| where |\\psi\\rangle = \\bigotimes_k |\\phi_k\\rangle
   is a product state with Bloch vectors \\{\\vec{r}_k\\}_{k=1}^n, the Fourier
   coefficients satisfy:

   \\hat{U}(\\alpha) = \\delta_{\\alpha,0} - 2^{1-n} \\prod_{k=1}^n r_k^{\\alpha_k}

   where \\alpha \\in \\{0,1\\}^n is a multi-index and r_k = |\\vec{r}_k|.")

(def entropy-theorem-statement
  "Let X be a discrete random variable with probability distribution
   p = (p_1, p_2, \\ldots, p_n) where p_i \\geq 0 and \\sum_{i=1}^n p_i = 1.
   The Shannon entropy H(X) = -\\sum_{i=1}^n p_i \\log p_i achieves its
   maximum value \\log n if and only if p_i = 1/n for all i \\in \\{1,\\ldots,n\\}.

   Proof uses Gibbs' inequality: D_{KL}(p \\| q) \\geq 0 with equality iff p = q.")

(def cauchy-schwarz-statement
  "For vectors u, v in an inner product space V, the Cauchy-Schwarz inequality states:

   |\\langle u, v \\rangle|^2 \\leq \\langle u, u \\rangle \\cdot \\langle v, v \\rangle

   with equality if and only if u and v are linearly dependent.

   Equivalently: |\\langle u, v \\rangle| \\leq \\|u\\| \\cdot \\|v\\|")

(defn gen-lean-proof-step
  "Generate a realistic Lean-style proof step statement."
  [step-num context]
  (let [templates
        [{:type :definition
          :template "Definition %d: Let %s be defined as %s. This satisfies the
                     required properties by construction."}
         {:type :lemma
          :template "Lemma %d (%s): We show that %s.
                     By the induction hypothesis, the claim holds for n-1.
                     The base case follows from direct computation."}
         {:type :calculation
          :template "Step %d (Calculation): We compute
                     \\begin{align}
                       %s &= %s \\\\
                          &= %s \\\\
                          &= %s
                     \\end{align}
                     where the second equality uses %s."}
         {:type :rewrite
          :template "Step %d (Rewriting): Applying %s to the expression
                     %s, we obtain %s. This follows from the
                     definition of %s combined with algebraic manipulation."}
         {:type :application
          :template "Step %d (Application of %s): Since the hypotheses of %s
                     are satisfied, we may apply it to conclude %s.
                     The required conditions were verified in steps %s."}]]
    (let [{:keys [template]} (rand-nth templates)
          vars ["\\alpha" "\\beta" "\\gamma" "\\delta" "\\epsilon"
                "\\phi" "\\psi" "\\theta" "\\lambda" "\\mu"]
          ops ["\\sum_{i=1}^n" "\\prod_{k=1}^m" "\\int_0^1" "\\lim_{n\\to\\infty}"]
          result (rand-nth ["f(x)" "g(y)" "h(z)" "F(\\alpha)" "G(\\beta)"])]
      (format template
              step-num
              (rand-nth vars)
              (rand-nth ops)
              result
              (rand-nth vars)
              context))))

(defn gen-realistic-statement
  "Generate a realistic mathematical statement of given approximate size."
  [target-bytes]
  (let [base-statements [fourier-theorem-statement
                         entropy-theorem-statement
                         cauchy-schwarz-statement]
        base (rand-nth base-statements)
        base-len (count base)]
    (if (<= target-bytes base-len)
      base
      ;; Pad with additional mathematical content
      (let [padding-needed (- target-bytes base-len)
            padding-chunks (for [i (range (quot padding-needed 200))]
                             (gen-lean-proof-step i "previous step"))]
        (str base "\n\n" (str/join "\n\n" padding-chunks))))))

(defn gen-kb-statement
  "Generate a statement of approximately n kilobytes."
  [kb]
  (gen-realistic-statement (* kb 1024)))

;; =============================================================================
;; Test Helpers
;; =============================================================================

(defn assert-ok [result]
  (is (:ok result) (str "Expected success, got: " (pr-str (:error result))))
  (:ok result))

(defn assert-error [result expected-type]
  (is (:error result) "Expected error")
  (when expected-type
    (is (some #(= expected-type (:type %)) (:error result))
        (str "Expected error type " expected-type ", got: " (pr-str (:error result)))))
  result)

(defn fresh-graph
  "Create a fresh, isolated graph for testing."
  [theorem-statement]
  (-> (init/init-graph theorem-statement)
      assert-ok
      (assoc :graph-id (gen-graph-id))))

;; =============================================================================
;; Realistic Workflow Tests with Generated IDs
;; =============================================================================

(deftest realistic-proof-workflow-test
  (testing "Complete proof workflow with realistic Lean-style content"
    (let [;; Step 1: Initialize with realistic theorem
          graph (fresh-graph fourier-theorem-statement)

          ;; Step 2: Add assumption with generated ID
          assume-id (gen-assumption-id)
          assume-node (make-partial-node assume-id
                                         :type :assumption
                                         :statement "Let $|\\psi\\rangle = \\bigotimes_{k=1}^n |\\phi_k\\rangle$
                                                     be an n-qubit product state where each $|\\phi_k\\rangle$
                                                     has Bloch vector $\\vec{r}_k = (r_k \\sin\\theta_k \\cos\\phi_k,
                                                     r_k \\sin\\theta_k \\sin\\phi_k, r_k \\cos\\theta_k)$."
                                         :justification :assumption
                                         :depth 0)
          graph (assert-ok (add-node/add-node graph assume-node))

          ;; Step 3: Add definition expansion step
          def-id (gen-claim-id)
          def-node (make-partial-node def-id
                                      :type :claim
                                      :statement "By definition, the rank-1 projector $P = |\\psi\\rangle\\langle\\psi|$
                                                  satisfies $U = I - 2P$. The Fourier coefficient is then:
                                                  \\[\\hat{U}(\\alpha) = 2^{-n} \\text{Tr}(\\sigma^\\alpha U)
                                                  = 2^{-n} \\text{Tr}(\\sigma^\\alpha) - 2^{1-n} \\text{Tr}(\\sigma^\\alpha P)\\]"
                                      :deps #{assume-id}
                                      :justification :definition-expansion
                                      :order 1)
          graph (assert-ok (add-node/add-node graph def-node))

          ;; Step 4: Add trace computation step (large statement)
          trace-id (gen-claim-id)
          trace-statement (str "Using the trace cyclic property and the fact that
                                $\\text{Tr}(\\sigma^\\alpha) = 2^n \\delta_{\\alpha,0}$, we compute:
                                \\begin{align}
                                  \\text{Tr}(\\sigma^\\alpha P) &= \\langle\\psi|\\sigma^\\alpha|\\psi\\rangle \\\\
                                  &= \\prod_{k=1}^n \\langle\\phi_k|\\sigma^{\\alpha_k}|\\phi_k\\rangle \\\\
                                  &= \\prod_{k=1}^n r_k^{\\alpha_k}
                                \\end{align}
                                The last equality follows from the Bloch sphere representation
                                where $\\langle\\phi|\\sigma^0|\\phi\\rangle = 1$ and
                                $\\langle\\phi|\\sigma^j|\\phi\\rangle = r_j$ for $j \\in \\{1,2,3\\}$.
                                "
                               ;; Add more content to reach ~2KB
                               (apply str (repeat 50 "This step is verified by direct computation. ")))
          trace-node (make-partial-node trace-id
                                        :type :claim
                                        :statement trace-statement
                                        :deps #{def-id}
                                        :justification :algebraic-rewrite
                                        :order 2)
          graph (assert-ok (add-node/add-node graph trace-node))

          ;; Step 5: Add QED
          qed-id (gen-claim-id)
          qed-node (make-partial-node qed-id
                                      :type :qed
                                      :statement "Combining the above, we obtain:
                                                  \\[\\hat{U}(\\alpha) = \\delta_{\\alpha,0} - 2^{1-n} \\prod_{k=1}^n r_k^{\\alpha_k}\\]
                                                  which completes the proof. \\qed"
                                      :deps #{trace-id}
                                      :justification :qed
                                      :order 3)
          graph (assert-ok (add-node/add-node graph qed-node))

          ;; Step 6: Verify all claims
          graph (assert-ok (update-status/update-status graph def-id :verified))
          graph (assert-ok (update-status/update-status graph trace-id :verified))
          graph (assert-ok (update-status/update-status graph qed-id :verified))

          ;; Step 7: Extract as lemma with generated name
          lemma-name (str "L1-fourier-" (format "%04x" (rand-int 0xFFFF)))
          extract-result (extract-lemma/extract-lemma graph qed-id lemma-name)
          graph (assert-ok extract-result)]

      ;; Verify: Large statement was handled correctly
      (is (> (count trace-statement) 2000) "Statement should be > 2KB")

      ;; Verify: Lemma was created with correct properties
      (is (contains? (:lemmas graph) lemma-name))
      (is (= :proven (get-in graph [:lemmas lemma-name :status])))

      ;; Verify: Generated IDs were used (not hardcoded)
      (is (not= assume-id :0-A1) "Should use generated IDs")
      (is (contains? (:nodes graph) assume-id))

      ;; Verify: Graph validates
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (validators/validate-semantics graph))))))

(deftest large-statement-workflow-test
  (testing "Workflow with kilobyte-sized statements (realistic Lean proof size)"
    (let [graph (fresh-graph (gen-kb-statement 1))

          ;; Add nodes with progressively larger statements
          ids (atom [])
          graph (reduce
                 (fn [g i]
                   (let [id (if (zero? i) (gen-assumption-id) (gen-claim-id))
                         deps (if (zero? i) #{} #{(last @ids)})
                         stmt-size (+ 500 (* i 200))  ; 500B, 700B, 900B, 1.1KB, 1.3KB
                         node (make-partial-node id
                                                 :type (if (zero? i) :assumption :claim)
                                                 :statement (gen-realistic-statement stmt-size)
                                                 :deps deps
                                                 :justification (if (zero? i) :assumption :modus-ponens)
                                                 :depth (if (zero? i) 0 1)
                                                 :order i)]
                     (swap! ids conj id)
                     (assert-ok (add-node/add-node g node))))
                 graph
                 (range 5))]

      ;; Verify: All nodes created with varying statement sizes
      (is (= 5 (count (:nodes graph))))

      ;; Verify: Token estimation handles large statements
      (let [estimates (map #(graph/estimate-node-tokens (graph/get-node graph %)) @ids)]
        (is (every? pos? estimates))
        ;; Later nodes generally have larger statements, but randomness may cause variation
        ;; Just verify the range is reasonable (first < last on average)
        (is (< (first estimates) (apply max estimates))
            "Larger statements should have higher token estimates"))

      ;; Verify: Graph validates despite large content
      (is (:valid (schema/validate-schema graph))))))

(deftest isolated-mutation-test
  (testing "Each test operates on an isolated graph instance"
    (let [;; Create two completely independent graphs
          graph1 (fresh-graph "Theorem 1: First independent theorem")
          graph2 (fresh-graph "Theorem 2: Second independent theorem")

          ;; Mutate graph1
          id1 (gen-assumption-id)
          node1 (make-partial-node id1 :type :assumption :justification :assumption :depth 0)
          graph1 (assert-ok (add-node/add-node graph1 node1))

          ;; Mutate graph2 with different content
          id2 (gen-assumption-id)
          node2 (make-partial-node id2 :type :assumption :justification :assumption :depth 0
                                   :statement "Completely different assumption")]
      (let [graph2 (assert-ok (add-node/add-node graph2 node2))]

        ;; Verify: Graphs are truly independent
        (is (not= (:graph-id graph1) (:graph-id graph2)))
        (is (not= id1 id2) "Generated IDs should be unique")
        (is (contains? (:nodes graph1) id1))
        (is (not (contains? (:nodes graph1) id2)))
        (is (contains? (:nodes graph2) id2))
        (is (not (contains? (:nodes graph2) id1)))))))

(deftest complex-dependency-graph-test
  (testing "Complex DAG with diamond pattern and realistic content"
    (let [graph (fresh-graph entropy-theorem-statement)

          ;; Build diamond: A -> B,C -> D
          a-id (gen-assumption-id)
          a-node (make-partial-node a-id
                                    :type :assumption
                                    :statement "Let $p = (p_1, \\ldots, p_n)$ be a probability distribution
                                                with $p_i \\geq 0$ and $\\sum_i p_i = 1$."
                                    :justification :assumption
                                    :depth 0)
          graph (assert-ok (add-node/add-node graph a-node))

          b-id (gen-claim-id)
          b-node (make-partial-node b-id
                                    :type :claim
                                    :statement "The Shannon entropy $H(p) = -\\sum_i p_i \\log p_i$
                                                is well-defined and non-negative for all probability
                                                distributions. This follows from $0 \\leq p_i \\leq 1$
                                                and the convention $0 \\log 0 = 0$."
                                    :deps #{a-id}
                                    :justification :definition-expansion
                                    :order 1)
          graph (assert-ok (add-node/add-node graph b-node))

          c-id (gen-claim-id)
          c-node (make-partial-node c-id
                                    :type :claim
                                    :statement "Gibbs' inequality states that for any two probability
                                                distributions $p$ and $q$: $D_{KL}(p \\| q) \\geq 0$
                                                with equality if and only if $p = q$ almost everywhere.
                                                Taking $q$ to be the uniform distribution gives the bound."
                                    :deps #{a-id}
                                    :justification :lemma-application
                                    :order 2)
          graph (assert-ok (add-node/add-node graph c-node))

          d-id (gen-claim-id)
          d-node (make-partial-node d-id
                                    :type :qed
                                    :statement "Combining the non-negativity of entropy from (B) with
                                                Gibbs' inequality from (C), we conclude:
                                                $H(p) \\leq \\log n$ with equality iff $p_i = 1/n$.
                                                This completes the proof of the maximum entropy theorem."
                                    :deps #{b-id c-id}
                                    :justification :qed
                                    :order 3)
          graph (assert-ok (add-node/add-node graph d-node))]

      ;; Verify: Diamond structure
      (is (= #{a-id} (get-in graph [:nodes b-id :dependencies])))
      (is (= #{a-id} (get-in graph [:nodes c-id :dependencies])))
      (is (= #{b-id c-id} (get-in graph [:nodes d-id :dependencies])))

      ;; Verify: Topological sort respects dependencies
      (let [sorted (graph/topological-sort graph)]
        (is (< (.indexOf sorted a-id) (.indexOf sorted b-id)))
        (is (< (.indexOf sorted a-id) (.indexOf sorted c-id)))
        (is (< (.indexOf sorted b-id) (.indexOf sorted d-id)))
        (is (< (.indexOf sorted c-id) (.indexOf sorted d-id))))

      ;; Verify: Graph validates
      (is (:valid (schema/validate-schema graph))))))

(deftest taint-propagation-realistic-test
  (testing "Taint propagation with realistic admitted step"
    (let [graph (fresh-graph cauchy-schwarz-statement)

          assume-id (gen-assumption-id)
          assume-node (make-partial-node assume-id
                                         :type :assumption
                                         :statement "Let $V$ be an inner product space over $\\mathbb{C}$
                                                     with inner product $\\langle \\cdot, \\cdot \\rangle$."
                                         :justification :assumption
                                         :depth 0)
          graph (assert-ok (add-node/add-node graph assume-node))

          ;; Add an admitted step (gap in proof)
          admitted-id (gen-claim-id)
          admitted-node (make-partial-node admitted-id
                                           :type :claim
                                           :statement "The function $f(t) = \\langle u + tv, u + tv \\rangle$
                                                       is a non-negative quadratic in $t \\in \\mathbb{R}$.
                                                       [ADMITTED: Full verification requires completing the
                                                       quadratic discriminant analysis. This is standard but
                                                       the formal argument is deferred.]"
                                           :deps #{assume-id}
                                           :justification :admitted
                                           :order 1)
          graph (assert-ok (add-node/add-node graph admitted-node))
          graph (assert-ok (update-status/update-status graph admitted-id :admitted))

          ;; Add dependent step
          dep-id (gen-claim-id)
          dep-node (make-partial-node dep-id
                                      :type :claim
                                      :statement "Since $f(t) \\geq 0$ for all $t$, the discriminant
                                                  $B^2 - 4AC \\leq 0$ where $A = \\langle v, v \\rangle$,
                                                  $B = 2\\text{Re}\\langle u, v \\rangle$, $C = \\langle u, u \\rangle$.
                                                  This yields $|\\langle u, v \\rangle|^2 \\leq \\langle u, u \\rangle \\langle v, v \\rangle$."
                                      :deps #{admitted-id}
                                      :order 2)
          graph (assert-ok (add-node/add-node graph dep-node))]

      ;; Verify: Taint propagates correctly
      (is (= :self-admitted (get-in graph [:nodes admitted-id :taint])))
      (is (= :tainted (get-in graph [:nodes dep-id :taint])))

      ;; Verify: Graph still validates (taint is valid state)
      (is (:valid (schema/validate-schema graph)))
      (is (:valid (validators/validate-semantics graph))))))

(deftest external-reference-realistic-test
  (testing "External reference workflow with realistic citation"
    (let [graph (fresh-graph "Application of classical results to quantum setting")

          ;; Add real-looking external reference
          ext-ref {:id (str "ref-" (format "%06x" (rand-int 0xFFFFFF)))
                   :doi "10.1103/PhysRevLett.69.2881"
                   :claimed-statement "Bennett et al. (1993): Teleporting an unknown quantum state
                                       via dual classical and Einstein-Podolsky-Rosen channels.
                                       Physical Review Letters, 70(13), 1895-1899.

                                       Key result: Quantum teleportation protocol achieving perfect
                                       state transfer using shared entanglement and classical
                                       communication (2 classical bits per qubit)."
                   :verification-status :verified
                   :bibdata {:authors ["Charles H. Bennett" "Gilles Brassard" "Claude Crépeau"
                                       "Richard Jozsa" "Asher Peres" "William K. Wootters"]
                             :title "Teleporting an Unknown Quantum State via Dual Classical and EPR Channels"
                             :year 1993
                             :journal "Physical Review Letters"}}
          ext-id (:id ext-ref)
          graph (assert-ok (external-ref/add-external-ref graph ext-ref))

          assume-id (gen-assumption-id)
          assume-node (make-partial-node assume-id :type :assumption :justification :assumption :depth 0)
          graph (assert-ok (add-node/add-node graph assume-node))

          ;; Reference the external result
          ref-id (gen-claim-id)
          ref-node (make-partial-node ref-id
                                      :type :external-ref
                                      :statement "By the quantum teleportation theorem [Bennett et al. 1993],
                                                  Alice can transmit an unknown qubit state $|\\psi\\rangle$
                                                  to Bob using only classical communication, provided they
                                                  share an EPR pair $|\\Phi^+\\rangle = (|00\\rangle + |11\\rangle)/\\sqrt{2}$."
                                      :deps #{assume-id}
                                      :justification :external-application
                                      :external-id ext-id
                                      :order 1)
          graph (assert-ok (add-node/add-node graph ref-node))]

      ;; Verify: External reference properly linked
      (is (contains? (:external-refs graph) ext-id))
      (is (= ext-id (get-in graph [:nodes ref-id :external-id])))
      (is (= :verified (get-in graph [:external-refs ext-id :verification-status])))

      ;; Verify: Bibdata preserved
      (is (= 1993 (get-in graph [:external-refs ext-id :bibdata :year])))
      (is (= 6 (count (get-in graph [:external-refs ext-id :bibdata :authors]))))

      ;; Verify: Graph validates
      (is (:valid (schema/validate-schema graph))))))

(deftest rapid-mutation-sequence-test
  (testing "Rapid sequence of mutations with generated IDs"
    (let [graph (fresh-graph "Stress test theorem")
          mutations (atom 0)

          ;; Perform 20 rapid add/verify cycles
          [graph final-ids]
          (reduce
           (fn [[g ids] i]
             (let [id (if (zero? i) (gen-assumption-id) (gen-claim-id))
                   deps (if (zero? i) #{} #{(last ids)})
                   node (make-partial-node id
                                           :type (if (zero? i) :assumption :claim)
                                           :statement (gen-realistic-statement 300)
                                           :deps deps
                                           :justification (if (zero? i) :assumption :modus-ponens)
                                           :depth (if (zero? i) 0 1)
                                           :order i)
                   g (assert-ok (add-node/add-node g node))
                   _ (swap! mutations inc)
                   ;; Verify every 5th node
                   g (if (and (pos? i) (zero? (mod i 5)))
                       (do (swap! mutations inc)
                           (assert-ok (update-status/update-status g id :verified)))
                       g)]
               [g (conj ids id)]))
           [graph []]
           (range 20))]

      ;; Verify: All mutations completed
      (is (= 20 (count (:nodes graph))))
      (is (>= @mutations 20))

      ;; Verify: Version incremented correctly
      (is (>= (:version graph) 20))

      ;; Verify: All generated IDs are unique
      (is (= 20 (count (set final-ids))))

      ;; Verify: Graph validates after rapid mutations
      (is (:valid (schema/validate-schema graph))))))
