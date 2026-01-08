/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step6_MainTheorem

  Step 6: Shannon Maximum Entropy Theorem (Final QED)

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-qed
  Status: CLEAN

  Main Theorem: For any probability distribution p = (p₁, p₂, p₃) on three
  outcomes with pᵢ ≥ 0 and Σᵢ pᵢ = 1, the Shannon entropy satisfies:

    H(p) = -Σᵢ pᵢ log₂ pᵢ ≤ log₂ 3

  with equality if and only if p₁ = p₂ = p₃ = 1/3.

  This file combines all previous steps into the final theorem statement.
-/
import AlethfeldLean.QBF.Rank1.ShannonMax.Step5_EqualityCondition

namespace Alethfeld.QBF.Rank1.ShannonMax

open scoped BigOperators

/-! ## :1-qed - Main Theorem Statement -/

/--
**Shannon Maximum Entropy Theorem (3 outcomes, positive probabilities)**

For any probability distribution p = (p₁, p₂, p₃) with all pᵢ > 0:
1. H(p) ≤ log₂(3)
2. Equality holds iff p = (1/3, 1/3, 1/3)

This is the core result for strictly positive distributions.
-/
theorem shannon_maximum_entropy_pos (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p ≤ log2 3 ∧
    (shannonEntropy p = log2 3 ↔ ∀ i, p.p i = 1/3) := by
  constructor
  · -- Part 1: H(p) ≤ log₂(3)
    exact entropy_le_log2_three_pos p hpos
  · -- Part 2: H(p) = log₂(3) iff p = uniform
    rw [entropy_eq_max_iff_uniform p hpos]
    constructor
    · intro h i
      have : p.p = uniformDist.p := h
      simp [this, uniform_val]
    · intro h
      funext i
      simp [h i, uniform_val]

/--
**Shannon Maximum Entropy Theorem (3 outcomes, general)**

For any probability distribution p = (p₁, p₂, p₃) with pᵢ ≥ 0 and Σᵢ pᵢ = 1:

  H(p) ≤ log₂(3)

This is the general bound allowing zero probabilities.
-/
theorem shannon_maximum_entropy_bound (p : ProbDist3) :
    shannonEntropy p ≤ log2 3 :=
  entropy_le_log2_three p

/--
**Shannon Maximum Entropy Theorem (Combined Statement)**

For any probability distribution p on three outcomes:
- H(p) is non-negative
- H(p) ≤ log₂(3)
- The maximum log₂(3) is achieved uniquely by the uniform distribution
-/
theorem shannon_maximum_entropy_full :
    (∀ p : ProbDist3, shannonEntropy p ≥ 0) ∧
    (∀ p : ProbDist3, shannonEntropy p ≤ log2 3) ∧
    (shannonEntropy uniformDist = log2 3) ∧
    (∀ p : ProbDist3, (∀ i, p.p i > 0) →
      (shannonEntropy p = log2 3 ↔ p.p = uniformDist.p)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Non-negativity
    exact shannonEntropy_nonneg
  · -- Upper bound
    exact entropy_le_log2_three
  · -- Uniform achieves maximum
    exact uniform_entropy_is_max
  · -- Equality characterization
    intro p hpos
    exact entropy_eq_max_iff_uniform p hpos

/-! ## Alternative Formulations -/

/-- Entropy is maximized at the uniform distribution -/
theorem entropy_maximizer_is_uniform :
    ∀ p : ProbDist3, shannonEntropy p ≤ shannonEntropy uniformDist := by
  intro p
  rw [uniform_entropy_is_max]
  exact entropy_le_log2_three p

/-- The uniform distribution is the unique maximizer (among positive distributions) -/
theorem entropy_unique_maximizer (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p = shannonEntropy uniformDist ↔ p.p = uniformDist.p := by
  rw [uniform_entropy_is_max]
  exact entropy_eq_max_iff_uniform p hpos

/-! ## Numerical Value -/

/-- log₂(3) is the numerical maximum: approximately 1.585 bits -/
theorem entropy_max_value : log2 3 = Real.log 3 / Real.log 2 := rfl

/-- The maximum entropy is positive -/
theorem entropy_max_pos : log2 3 > 0 := log2_three_pos

/-! ## Summary

This completes the formalization of the Shannon Maximum Entropy Theorem
for probability distributions on 3 outcomes.

**Proof Structure:**
1. Step1_Definitions: Defined ProbDist3, uniformDist, log₂, entropyTerm, shannonEntropy
2. Step2_LogInequality: Proved ln(x) ≤ x - 1 with equality iff x = 1
3. Step3_GibbsInequality: Proved D(p||q) ≥ 0 with equality iff p = q
4. Step4_EntropyBound: Proved H(p) ≤ log₂(3) using Gibbs with uniform
5. Step5_EqualityCondition: Proved H(p) = log₂(3) iff p = uniform
6. Step6_MainTheorem: Combined into final theorem statement

**Key Dependencies:**
- Mathlib.Analysis.SpecialFunctions.Log.Basic (logarithm properties)
- Mathlib.Analysis.SpecialFunctions.Log.Deriv (differentiability)
- Mathlib.Analysis.Calculus.MeanValue (for exp/log inequalities)

**Taint Status:** CLEAN (no admitted steps)
**Sorry Count:** 0
-/

end Alethfeld.QBF.Rank1.ShannonMax
