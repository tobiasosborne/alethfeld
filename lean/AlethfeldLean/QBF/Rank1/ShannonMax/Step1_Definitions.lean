/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step1_Definitions

  Step 1: Basic Definitions for Shannon Maximum Entropy Theorem

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-def-H, :1-def-u
  Status: CLEAN

  This file defines:
  - Shannon entropy H(p) for probability distributions on 3 outcomes
  - The uniform distribution u = (1/3, 1/3, 1/3)
  - The 0·log(0) = 0 convention
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Alethfeld.QBF.Rank1.ShannonMax

open scoped BigOperators
open Real

/-! ## Basic Definitions -/

/-- A probability distribution on 3 outcomes is a function p : Fin 3 → ℝ
    with p_i ≥ 0 and Σ p_i = 1 -/
structure ProbDist3 where
  /-- The probability values -/
  p : Fin 3 → ℝ
  /-- Non-negativity: p_i ≥ 0 -/
  nonneg : ∀ i, p i ≥ 0
  /-- Normalization: Σ p_i = 1 -/
  sum_eq_one : ∑ i, p i = 1

/-! ## :1-def-u - Uniform Distribution Definition

Define uniform distribution u = (1/3, 1/3, 1/3).
-/

/-- The uniform distribution on 3 outcomes -/
noncomputable def uniformDist : ProbDist3 where
  p := fun _ => 1/3
  nonneg := fun _ => by norm_num
  sum_eq_one := by simp only [Fin.sum_univ_three]; norm_num

/-- The uniform distribution value -/
theorem uniform_val (i : Fin 3) : uniformDist.p i = 1/3 := rfl

/-- The uniform distribution is positive -/
theorem uniform_pos (i : Fin 3) : uniformDist.p i > 0 := by
  simp only [uniformDist]; norm_num

/-! ## Binary Logarithm -/

/-- Binary logarithm: log₂(x) = ln(x) / ln(2) -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- log 2 > 0 -/
theorem log_two_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- log 2 ≠ 0 -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt log_two_pos

/-- log₂(2) = 1 -/
theorem log2_two : log2 2 = 1 := by
  unfold log2
  rw [div_self log_two_ne_zero]

/-- log₂(1) = 0 -/
theorem log2_one : log2 1 = 0 := by
  unfold log2
  simp [Real.log_one]

/-- log₂(3) > 0 -/
theorem log2_three_pos : log2 3 > 0 := by
  unfold log2
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3)
  · exact log_two_pos

/-- log₂(1/3) = -log₂(3) -/
theorem log2_one_third : log2 (1/3) = -log2 3 := by
  unfold log2
  rw [show (1 : ℝ) / 3 = 3⁻¹ by norm_num, Real.log_inv, neg_div]

/-- Logarithm product rule for log₂ -/
theorem log2_mul {x y : ℝ} (hx : x > 0) (hy : y > 0) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  ring

/-! ## :1-def-H - Shannon Entropy Definition

Define H(p) = -Σᵢ pᵢ log₂ pᵢ with convention 0·log₂(0) := 0.
-/

/-- Shannon entropy term: -p log₂ p with convention 0 log 0 = 0 -/
noncomputable def entropyTerm (p : ℝ) : ℝ :=
  if p > 0 then -p * log2 p else 0

/-- entropyTerm when p > 0 -/
theorem entropyTerm_pos (p : ℝ) (hp : p > 0) : entropyTerm p = -p * log2 p := by
  unfold entropyTerm
  simp [hp]

/-- entropyTerm when p = 0 -/
theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  unfold entropyTerm
  simp

/-- entropyTerm is non-negative for 0 ≤ p ≤ 1 -/
theorem entropyTerm_nonneg {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) : entropyTerm p ≥ 0 := by
  unfold entropyTerm
  split_ifs with h
  · -- p > 0 case: need -p * log₂(p) ≥ 0
    -- Since 0 < p ≤ 1, log₂(p) ≤ 0, so -log₂(p) ≥ 0
    unfold log2
    have hlog : Real.log p ≤ 0 := Real.log_nonpos (le_of_lt h) hp1
    have hlog2pos : Real.log 2 > 0 := log_two_pos
    have hlog2 : Real.log p / Real.log 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hlog2pos)
    have hneg : -(Real.log p / Real.log 2) ≥ 0 := by linarith
    calc -p * (Real.log p / Real.log 2) = p * (-(Real.log p / Real.log 2)) := by ring
      _ ≥ 0 := mul_nonneg (le_of_lt h) hneg
  · -- p ≤ 0 case
    linarith

/-- Shannon entropy of a probability distribution on 3 outcomes -/
noncomputable def shannonEntropy (dist : ProbDist3) : ℝ :=
  ∑ i, entropyTerm (dist.p i)

/-- Alternative formula: H(p) = -Σᵢ pᵢ log₂ pᵢ when all p_i > 0 -/
theorem shannonEntropy_eq_neg_sum (dist : ProbDist3) (hpos : ∀ i, dist.p i > 0) :
    shannonEntropy dist = -∑ i, dist.p i * log2 (dist.p i) := by
  unfold shannonEntropy
  simp only [entropyTerm_pos _ (hpos _)]
  simp only [neg_mul]
  rw [← Finset.sum_neg_distrib]

/-- Shannon entropy is non-negative -/
theorem shannonEntropy_nonneg (dist : ProbDist3) : shannonEntropy dist ≥ 0 := by
  unfold shannonEntropy
  apply Finset.sum_nonneg
  intro i _
  have hp0 : dist.p i ≥ 0 := dist.nonneg i
  have hp1 : dist.p i ≤ 1 := by
    have hsum := dist.sum_eq_one
    have hother : ∑ j ∈ Finset.univ.erase i, dist.p j ≥ 0 := by
      apply Finset.sum_nonneg
      intro j _
      exact dist.nonneg j
    calc dist.p i = 1 - ∑ j ∈ Finset.univ.erase i, dist.p j := by
          rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          ring
      _ ≤ 1 := by linarith
  exact entropyTerm_nonneg hp0 hp1

/-- Entropy of uniform distribution equals log₂(3) -/
theorem entropy_uniform : shannonEntropy uniformDist = log2 3 := by
  unfold shannonEntropy
  simp only [Fin.sum_univ_three, uniform_val]
  simp only [entropyTerm_pos (1/3) (by norm_num : (1:ℝ)/3 > 0)]
  rw [log2_one_third]
  ring

/-! ## Useful Lemmas -/

/-- A distribution value is bounded by 1 -/
theorem dist_le_one (dist : ProbDist3) (i : Fin 3) : dist.p i ≤ 1 := by
  have hsum := dist.sum_eq_one
  have hother : ∑ j ∈ Finset.univ.erase i, dist.p j ≥ 0 := by
    apply Finset.sum_nonneg
    intro j _
    exact dist.nonneg j
  calc dist.p i = 1 - ∑ j ∈ Finset.univ.erase i, dist.p j := by
        rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        ring
    _ ≤ 1 := by linarith

end Alethfeld.QBF.Rank1.ShannonMax
