/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step4_InfluenceTerm

  Step 4: Influence Term Expansion

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-step2, :L5-step2-1 through :L5-step2-4b
  Status: CLEAN

  This file proves:
  - (2n-2)(1-p_0) = 4(n-1)*epsilon - (2n-2)*epsilon^2
  - The error term (2n-2)*epsilon^2 = O(n * 4^{-n})

  Key result (L5-step2):
    (2n-2)(1-p_0) = 4(n-1)*epsilon + O(n*epsilon^2)
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step2_EpsilonSetup

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy

/-! ## L5-step2-1: 1 - p_0 = 2*epsilon - epsilon^2 -/

/-- L5-step2-1: From L5-assume-4, 1 - p_0 = 2*epsilon - epsilon^2. -/
theorem influence_one_minus_p0 (n : ℕ) :
    1 - p_zero n = 2 * epsilon n - (epsilon n)^2 :=
  one_minus_p_zero_eq_eps n

/-! ## L5-step2-2: Distribution -/

/-- L5-step2-2a: Distributivity: a(b-c) = ab - ac. -/
theorem distrib_left (a b c : ℝ) : a * (b - c) = a * b - a * c := by ring

/-- L5-step2-2: (2n-2)(2*epsilon - epsilon^2) = (2n-2)*2*epsilon - (2n-2)*epsilon^2. -/
theorem influence_distributed (n : ℕ) :
    (2*(n : ℝ) - 2) * (2 * epsilon n - (epsilon n)^2) =
    (2*(n : ℝ) - 2) * 2 * epsilon n - (2*(n : ℝ) - 2) * (epsilon n)^2 := by
  ring

/-! ## L5-step2-3: Main term simplification -/

/-- L5-step2-3a: 2n-2 = 2(n-1), so (2n-2)*2 = 4(n-1). -/
theorem two_n_minus_two_eq (n : ℕ) : 2*(n : ℝ) - 2 = 2*((n : ℝ) - 1) := by ring

theorem coeff_simplify (n : ℕ) : (2*(n : ℝ) - 2) * 2 = 4*((n : ℝ) - 1) := by ring

/-- L5-step2-3: (2n-2)*2*epsilon = 4(n-1)*epsilon. -/
theorem influence_main_term (n : ℕ) :
    (2*(n : ℝ) - 2) * 2 * epsilon n = 4*((n : ℝ) - 1) * epsilon n := by
  rw [coeff_simplify]

/-! ## L5-step2-4: Error term bound -/

/-- L5-step2-4a: epsilon^2 = 2^{2-2n} = 4/4^n. -/
theorem epsilon_sq_eq_four_div {n : ℕ} :
    (epsilon n)^2 = 4 / (4 : ℝ)^n := by
  rw [epsilon_sq]
  -- 2^{2-2n} = 2^2 * 2^{-2n} = 4 * 2^{-2n} = 4 / 2^{2n} = 4 / 4^n
  have hexp : (2 - 2*(n : ℤ) : ℤ) = (2 : ℤ) + (-(2*(n : ℤ))) := by ring
  rw [hexp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h4 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
  rw [h4, zpow_neg]
  have h2n : (2 : ℝ)^(2*(n : ℤ)) = (4 : ℝ)^n := by
    rw [show (2*(n : ℤ) : ℤ) = ((2*n : ℕ) : ℤ) by simp, zpow_natCast]
    calc (2 : ℝ)^(2*n) = ((2 : ℝ)^2)^n := by rw [pow_mul]
      _ = (4 : ℝ)^n := by norm_num
  rw [h2n]
  field_simp

/-- L5-step2-4b: (2n-2) * 4/4^n <= 2n * 4/4^n = 8n/4^n = O(n * 4^{-n}). -/
theorem influence_error_bound {n : ℕ} (hn : n ≥ 1) :
    |(2*(n : ℝ) - 2) * (epsilon n)^2| ≤ 8*(n : ℝ) / (4 : ℝ)^n := by
  rw [epsilon_sq_eq_four_div]
  have hnn : (2*(n : ℝ) - 2) ≤ 2*(n : ℝ) := by linarith
  have hnn0 : 0 ≤ 2*(n : ℝ) - 2 := by
    have : (1 : ℕ) ≤ n := hn
    have : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
    linarith
  calc |(2*(n : ℝ) - 2) * (4 / (4 : ℝ)^n)|
      = (2*(n : ℝ) - 2) * (4 / (4 : ℝ)^n) := by
        rw [abs_of_nonneg]
        apply mul_nonneg hnn0
        apply div_nonneg (by norm_num)
        exact pow_nonneg (by norm_num) n
    _ ≤ 2*(n : ℝ) * (4 / (4 : ℝ)^n) := by
        apply mul_le_mul_of_nonneg_right hnn
        apply div_nonneg (by norm_num)
        exact pow_nonneg (by norm_num) n
    _ = 8*(n : ℝ) / (4 : ℝ)^n := by ring

/-- The error term is O(n * epsilon^2). -/
theorem influence_error_is_small {n : ℕ} (hn : n ≥ 2) :
    |(2*(n : ℝ) - 2) * (epsilon n)^2| ≤ 2*(n : ℝ) * (epsilon n)^2 := by
  have hnn0 : 0 ≤ 2*(n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
    linarith
  have hnn : 2*(n : ℝ) - 2 ≤ 2*(n : ℝ) := by linarith
  calc |(2*(n : ℝ) - 2) * (epsilon n)^2|
      = (2*(n : ℝ) - 2) * (epsilon n)^2 := by
        rw [abs_of_nonneg]
        exact mul_nonneg hnn0 (sq_nonneg _)
    _ ≤ 2*(n : ℝ) * (epsilon n)^2 := by
        apply mul_le_mul_of_nonneg_right hnn (sq_nonneg _)

/-! ## L5-step2: Main result -/

/-- L5-step2 (Main Result): (2n-2)(1-p_0) = 4(n-1)*epsilon - (2n-2)*epsilon^2.

    The first term is the leading term, the second is the error.
    This is exact, not an approximation. -/
theorem influenceTerm_exact (n : ℕ) :
    (2*(n : ℝ) - 2) * (1 - p_zero n) =
    4*((n : ℝ) - 1) * epsilon n - (2*(n : ℝ) - 2) * (epsilon n)^2 := by
  rw [one_minus_p_zero_eq_eps]
  ring

/-- Alternative form with O notation style. -/
theorem influenceTerm_expansion {n : ℕ} (hn : n ≥ 1) :
    ∃ R : ℝ, |R| ≤ 8*(n : ℝ) / (4 : ℝ)^n ∧
      influenceTerm_p0 n = 4*((n : ℝ) - 1) * epsilon n - R := by
  unfold influenceTerm_p0
  use (2*(n : ℝ) - 2) * (epsilon n)^2
  constructor
  · exact influence_error_bound hn
  · exact influenceTerm_exact n

/-- The influence term is asymptotically 4(n-1)*epsilon. -/
theorem influenceTerm_asymptotic {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 2*(n : ℝ) * (epsilon n)^2 ∧
      influenceTerm_p0 n = 4*((n : ℝ) - 1) * epsilon n + R := by
  unfold influenceTerm_p0
  use -(2*(n : ℝ) - 2) * (epsilon n)^2
  constructor
  · -- |-(2n-2) * eps^2| = |(2n-2) * eps^2|
    have h : -(2*(n : ℝ) - 2) * (epsilon n)^2 = -((2*(n : ℝ) - 2) * (epsilon n)^2) := by ring
    rw [h, abs_neg]
    exact influence_error_is_small hn
  · rw [influenceTerm_exact]
    ring

end Alethfeld.QBF.Rank1.L5Asymptotic
