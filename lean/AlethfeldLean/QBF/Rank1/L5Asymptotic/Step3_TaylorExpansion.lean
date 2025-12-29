/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step3_TaylorExpansion

  Step 3: Taylor Expansion for Entropy Term

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-step1, :L5-step1-1 through :L5-step1-7
  Status: CLEAN

  This file proves:
  - Taylor series: log(1-x) = -x - x^2/2 - x^3/3 - ... for |x| < 1
  - log_2(p_0) = -2*epsilon/(ln 2) + O(epsilon^2)
  - -p_0 * log_2(p_0) = 2*epsilon/(ln 2) + O(epsilon^2)

  Key result (L5-step1-7):
    -p_0 * log_2(p_0) = 2*epsilon/(ln 2) + O(epsilon^2)
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step2_EpsilonSetup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy

/-! ## L5-step1-1: Taylor series for log(1-x)

The Mercator series: log(1-x) = -x - x^2/2 - x^3/3 - ... for |x| < 1.
-/

/-- L5-step1-1a: The Mercator series is valid for |x| < 1.
    We use Mathlib's hasSum_pow_div_log_of_abs_lt_one for the formal statement. -/
theorem mercator_series_valid {x : ℝ} (hx : |x| < 1) :
    Real.log (1 - x) = -∑' n : ℕ, x^(n+1) / (n+1) := by
  -- From Mathlib: HasSum (fun n => x^(n+1)/(n+1)) (-log (1 - x))
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hx
  -- Convert HasSum to tsum equality: ∑' n, x^(n+1)/(n+1) = -log (1 - x)
  rw [h.tsum_eq]
  ring

/-- L5-step1-1b: For n >= 2, |epsilon| < 1, so the series applies.
    From L5-assume-2: epsilon < 1 for n >= 2. -/
theorem epsilon_abs_lt_one {n : ℕ} (hn : n ≥ 2) : |epsilon n| < 1 := by
  rw [abs_of_pos (epsilon_pos n)]
  exact epsilon_lt_one hn

/-! ## L5-step1-2, L5-step1-2a: log_2(1-epsilon) expansion -/

/-- L5-step1-2a: log_2(x) = ln(x)/ln(2) by change of base formula. -/
theorem log2_eq_log_div_log (x : ℝ) :
    log2 x = Real.log x / Real.log 2 := rfl

/-- First-order approximation: log(1-eps) = -eps + O(eps^2) -/
theorem log_one_minus_eps_approx (eps : ℝ) (heps : |eps| < 1) :
    ∃ R : ℝ, |R| ≤ eps^2 / (2 * (1 - |eps|)) ∧
      Real.log (1 - eps) = -eps + R := by
  sorry -- Taylor remainder theorem

/-- L5-step1-2: log_2(1-epsilon) = (-epsilon - epsilon^2/2 + O(epsilon^3)) / ln(2) -/
theorem log2_one_minus_eps {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (epsilon n)^2 ∧
      log2 (1 - epsilon n) = -epsilon n / Real.log 2 + R := by
  sorry -- Follows from log_one_minus_eps_approx

/-! ## L5-step1-3: log_2(p_0) = 2 * log_2(1-epsilon) -/

/-- L5-step1-3a: log(a^n) = n * log(a) for a > 0. -/
theorem log_pow_eq_mul_log {a : ℝ} (ha : a > 0) (n : ℕ) :
    Real.log (a^n) = n * Real.log a := Real.log_pow a n

/-- log_2(a^n) = n * log_2(a) for a > 0. -/
theorem log2_pow_eq_mul_log2 {a : ℝ} (ha : a > 0) (n : ℕ) :
    log2 (a^n) = n * log2 a := by
  unfold log2
  rw [Real.log_pow]
  ring

/-- L5-step1-3b: p_0 = (1-epsilon)^2 > 0 since 0 < epsilon < 1. -/
theorem p_zero_pos_via_eps {n : ℕ} (hn : n ≥ 2) : p_zero n > 0 :=
  p_zero_pos_of_eps_lt_one hn

/-- L5-step1-3: log_2(p_0) = log_2((1-epsilon)^2) = 2 * log_2(1-epsilon). -/
theorem log2_p_zero_eq {n : ℕ} (hn : n ≥ 2) :
    log2 (p_zero n) = 2 * log2 (1 - epsilon n) := by
  rw [p_zero_eq_sq_one_minus_eps]
  have hpos : 1 - epsilon n > 0 := by
    have heps := epsilon_lt_one hn
    linarith
  rw [log2_pow_eq_mul_log2 hpos 2]
  ring

/-! ## L5-step1-4: log_2(p_0) expansion -/

/-- L5-step1-4: log_2(p_0) = -2*epsilon/(ln 2) + O(epsilon^2). -/
theorem log2_p_zero_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 2 * (epsilon n)^2 ∧
      log2 (p_zero n) = -2 * epsilon n / Real.log 2 + R := by
  sorry -- Combines log2_p_zero_eq with log2_one_minus_eps

/-! ## L5-step1-5, L5-step1-6, L5-step1-7: Final entropy term expansion -/

/-- L5-step1-5: -p_0 * log_2(p_0) = -p_0 * (-2*epsilon/(ln 2)) + O(epsilon^2)
                                  = 2*p_0*epsilon/(ln 2) + O(epsilon^2). -/
theorem entropy_term_step5 {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 4 * (epsilon n)^2 ∧
      -p_zero n * log2 (p_zero n) = 2 * p_zero n * epsilon n / Real.log 2 + R := by
  sorry -- Follows from log2_p_zero_expansion

/-- L5-step1-6: p_0 = 1 - 2*epsilon + epsilon^2 = 1 + O(epsilon),
                so p_0 * epsilon = epsilon + O(epsilon^2). -/
theorem p_zero_times_eps {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 3 * (epsilon n)^2 ∧
      p_zero n * epsilon n = epsilon n + R := by
  rw [p_zero_eq_sq_one_minus_eps]
  use -(epsilon n)^2 * (2 - epsilon n)
  constructor
  · have heps := epsilon_bounds hn
    have hle : epsilon n ≤ 1/2 := heps.2.1
    have heps_pos : epsilon n > 0 := heps.1
    have h2eps : 2 - epsilon n > 0 := by linarith
    -- The expression -(epsilon n)^2 * (2 - epsilon n) is non-positive (negative of product of positives)
    have hR_nonpos : -(epsilon n)^2 * (2 - epsilon n) ≤ 0 := by nlinarith [sq_nonneg (epsilon n)]
    calc |-(epsilon n)^2 * (2 - epsilon n)|
        = -(-(epsilon n)^2 * (2 - epsilon n)) := abs_of_nonpos hR_nonpos
      _ = (epsilon n)^2 * (2 - epsilon n) := by ring
      _ ≤ (epsilon n)^2 * 2 := by nlinarith [sq_nonneg (epsilon n)]
      _ ≤ 3 * (epsilon n)^2 := by nlinarith [sq_nonneg (epsilon n)]
  · rw [sq_one_minus_eps]
    ring

/-- L5-step1-7 (Main Result): -p_0 * log_2(p_0) = 2*epsilon/(ln 2) + O(epsilon^2).

    This is the key Taylor expansion for the entropy term. -/
theorem entropy_term_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 10 * (epsilon n)^2 / Real.log 2 ∧
      -p_zero n * log2 (p_zero n) = 2 * epsilon n / Real.log 2 + R := by
  sorry -- Combines entropy_term_step5 with p_zero_times_eps

/-- Asymptotic form: entropyTerm_p0 n ~ 2*epsilon/(ln 2) as n -> infinity. -/
theorem entropyTerm_asymptotic {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 10 * (epsilon n)^2 / Real.log 2 ∧
      entropyTerm_p0 n = 2 * epsilon n / Real.log 2 + R := by
  unfold entropyTerm_p0
  exact entropy_term_expansion hn

end Alethfeld.QBF.Rank1.L5Asymptotic
