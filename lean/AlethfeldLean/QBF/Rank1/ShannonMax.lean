/-
  AlethfeldLean.QBF.Rank1.ShannonMax

  Shannon Maximum Entropy Theorem - Main Import File

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  Status: CLEAN

  This file imports all components of the Shannon Maximum Entropy proof.

  **Theorem Statement:**
  For any probability distribution p = (p₁, p₂, p₃) on three outcomes with
  pᵢ ≥ 0 and Σᵢ pᵢ = 1, the Shannon entropy satisfies:

    H(p) = -Σᵢ pᵢ log₂ pᵢ ≤ log₂ 3

  with equality if and only if p₁ = p₂ = p₃ = 1/3.

  **Proof Structure (7 files, corresponding to EDN depth-1 nodes):**

  1. `Step1_Definitions` (:1-def-H, :1-def-u)
     - ProbDist3: Probability distributions on 3 outcomes
     - uniformDist: The uniform distribution (1/3, 1/3, 1/3)
     - log₂: Binary logarithm
     - entropyTerm, shannonEntropy: Shannon entropy with 0·log(0) = 0 convention

  2. `Step2_LogInequality` (:1-log-ineq, :2-def-f through :2-log-ineq-eq)
     - log_le_sub_one: ln(x) ≤ x - 1 for x > 0
     - log_eq_sub_one_iff: Equality iff x = 1

  3. `Step3_GibbsInequality` (:1-gibbs, :2-gibbs-* nodes)
     - klDivergence: Relative entropy D(p||q)
     - gibbs_inequality: D(p||q) ≥ 0
     - gibbs_equality_iff: D(p||q) = 0 iff p = q

  4. `Step4_EntropyBound` (:1-H-bound, :2-bound-* nodes)
     - entropy_le_log2_three: H(p) ≤ log₂(3)

  5. `Step5_EqualityCondition` (:1-H-equality, :2-eq-* nodes)
     - entropy_eq_max_iff_uniform: H(p) = log₂(3) iff p = uniform

  6. `Step6_MainTheorem` (:1-qed)
     - shannon_maximum_entropy_full: Combined theorem statement
     - entropy_maximizer_is_uniform: Uniform is the unique maximizer

  **Usage:**
  ```lean
  import AlethfeldLean.QBF.Rank1.ShannonMax

  example (p : Alethfeld.QBF.Rank1.ShannonMax.ProbDist3) :
      Alethfeld.QBF.Rank1.ShannonMax.shannonEntropy p ≤
      Alethfeld.QBF.Rank1.ShannonMax.log2 3 :=
    Alethfeld.QBF.Rank1.ShannonMax.shannon_maximum_entropy_bound p
  ```
-/

-- Import all steps in order
import AlethfeldLean.QBF.Rank1.ShannonMax.Step1_Definitions
import AlethfeldLean.QBF.Rank1.ShannonMax.Step2_LogInequality
import AlethfeldLean.QBF.Rank1.ShannonMax.Step3_GibbsInequality
import AlethfeldLean.QBF.Rank1.ShannonMax.Step4_EntropyBound
import AlethfeldLean.QBF.Rank1.ShannonMax.Step5_EqualityCondition
import AlethfeldLean.QBF.Rank1.ShannonMax.Step6_MainTheorem
