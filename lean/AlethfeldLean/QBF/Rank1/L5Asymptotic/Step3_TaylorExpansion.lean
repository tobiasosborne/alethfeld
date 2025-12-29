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

/-- First-order approximation: log(1-eps) = -eps + O(eps^2).

Uses Mathlib's abs_log_sub_add_sum_range_le with n=1:
  |∑ i ∈ range 1, eps^(i+1)/(i+1) + log(1-eps)| ≤ |eps|^2 / (1-|eps|)

Since range 1 = {0}, the sum is just eps^1/1 = eps, giving:
  |eps + log(1-eps)| ≤ eps^2 / (1-|eps|)

Note: The bound eps^2/(1-|eps|) is slightly weaker than the tighter
eps^2/(2(1-|eps|)) mentioned in some textbooks, but it's sufficient
for the asymptotic analysis since both are O(eps^2).
-/
theorem log_one_minus_eps_approx (eps : ℝ) (heps : |eps| < 1) :
    ∃ R : ℝ, |R| ≤ eps^2 / (1 - |eps|) ∧
      Real.log (1 - eps) = -eps + R := by
  have h1 : 1 - |eps| > 0 := by linarith
  use Real.log (1 - eps) + eps
  constructor
  · -- Use Mathlib's abs_log_sub_add_sum_range_le with n=1
    have h := Real.abs_log_sub_add_sum_range_le heps 1
    -- range 1 = {0}, so sum is eps^(0+1)/(0+1) = eps
    simp only [Finset.range_one, Finset.sum_singleton] at h
    simp only [zero_add, pow_one, Nat.cast_zero, div_one] at h
    -- h : |eps + log(1 - eps)| ≤ |eps|^2 / (1 - |eps|)
    convert h using 2
    · ring
    · rw [sq_abs]
  · ring

/-- L5-step1-2: log_2(1-epsilon) = -epsilon/ln(2) + O(epsilon^2).

Proof: From log_one_minus_eps_approx:
  log(1-eps) = -eps + R where |R| ≤ eps²/(1-|eps|)

Since log₂(x) = log(x)/log(2):
  log₂(1-eps) = (-eps + R)/log(2) = -eps/log(2) + R/log(2)

For n ≥ 2, eps ≤ 1/2, so 1-|eps| ≥ 1/2, giving:
  |R/log(2)| ≤ eps²/((1-|eps|)*log(2)) ≤ 2*eps²/log(2)
-/
theorem log2_one_minus_eps {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 2 * (epsilon n)^2 / Real.log 2 ∧
      log2 (1 - epsilon n) = -epsilon n / Real.log 2 + R := by
  -- Get the log approximation
  have heps_lt_one := epsilon_abs_lt_one hn
  obtain ⟨R, hR_bound, hR_eq⟩ := log_one_minus_eps_approx (epsilon n) heps_lt_one
  -- The log2 remainder is R / log(2)
  use R / Real.log 2
  constructor
  · -- Bound: |R/log(2)| ≤ 2*eps²/log(2)
    have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [abs_div, abs_of_pos hlog2_pos]
    -- |R| ≤ eps²/(1-|eps|) and for n ≥ 2, 1-|eps| ≥ 1/2, so |R| ≤ 2*eps²
    have heps := epsilon_bounds hn
    have heps_pos : epsilon n > 0 := heps.1
    have heps_le : epsilon n ≤ 1/2 := heps.2.1
    have h_one_minus : 1 - |epsilon n| ≥ 1/2 := by
      rw [abs_of_pos heps_pos]
      linarith
    have h_one_minus_pos : 1 - |epsilon n| > 0 := by linarith
    calc |R| / Real.log 2
        ≤ (epsilon n)^2 / (1 - |epsilon n|) / Real.log 2 := by
          apply div_le_div_of_nonneg_right hR_bound (le_of_lt hlog2_pos)
      _ = (epsilon n)^2 / ((1 - |epsilon n|) * Real.log 2) := by
          rw [div_div, mul_comm]
      _ ≤ (epsilon n)^2 / ((1/2) * Real.log 2) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _)
          · positivity
          · apply mul_le_mul_of_nonneg_right h_one_minus (le_of_lt hlog2_pos)
      _ = 2 * (epsilon n)^2 / Real.log 2 := by ring
  · -- Equation: log₂(1-eps) = -eps/log(2) + R/log(2)
    unfold log2
    rw [hR_eq]
    ring

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

/-- L5-step1-4: log_2(p_0) = -2*epsilon/(ln 2) + O(epsilon^2).

Proof: From log2_p_zero_eq:
  log₂(p₀) = 2 * log₂(1-ε)

From log2_one_minus_eps:
  log₂(1-ε) = -ε/log(2) + R where |R| ≤ 2*ε²/log(2)

Therefore:
  log₂(p₀) = 2*(-ε/log(2) + R) = -2ε/log(2) + 2R
  with |2R| ≤ 4*ε²/log(2)
-/
theorem log2_p_zero_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 4 * (epsilon n)^2 / Real.log 2 ∧
      log2 (p_zero n) = -2 * epsilon n / Real.log 2 + R := by
  -- Get the log2(1-eps) expansion
  obtain ⟨R, hR_bound, hR_eq⟩ := log2_one_minus_eps hn
  -- The p_zero remainder is 2R
  use 2 * R
  constructor
  · -- Bound: |2R| ≤ 4*eps²/log(2)
    calc |2 * R| = 2 * |R| := by rw [abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0)]
      _ ≤ 2 * (2 * (epsilon n)^2 / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left hR_bound (by norm_num : (0:ℝ) ≤ 2)
      _ = 4 * (epsilon n)^2 / Real.log 2 := by ring
  · -- Equation: log₂(p₀) = -2ε/log(2) + 2R
    rw [log2_p_zero_eq hn, hR_eq]
    ring

/-! ## L5-step1-5, L5-step1-6, L5-step1-7: Final entropy term expansion -/

/-- L5-step1-5: -p_0 * log_2(p_0) = -p_0 * (-2*epsilon/(ln 2)) + O(epsilon^2)
                                  = 2*p_0*epsilon/(ln 2) + O(epsilon^2).

Proof: From log2_p_zero_expansion:
  log₂(p₀) = -2ε/log(2) + R where |R| ≤ 4*ε²/log(2)

Then:
  -p₀ * log₂(p₀) = -p₀ * (-2ε/log(2) + R) = 2*p₀*ε/log(2) - p₀*R

Since p₀ ≤ 1, the remainder -p₀*R satisfies |-p₀*R| ≤ |R| ≤ 4*ε²/log(2).
-/
theorem entropy_term_step5 {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 4 * (epsilon n)^2 / Real.log 2 ∧
      -p_zero n * log2 (p_zero n) = 2 * p_zero n * epsilon n / Real.log 2 + R := by
  -- Get the log2(p_zero) expansion
  obtain ⟨R, hR_bound, hR_eq⟩ := log2_p_zero_expansion hn
  -- The entropy term remainder is -p_zero * R
  use -p_zero n * R
  constructor
  · -- Bound: |-p_zero * R| ≤ 4*eps²/log(2)
    have hp0_pos : p_zero n > 0 := p_zero_pos_via_eps hn
    have hn1 : n ≥ 1 := Nat.one_le_of_lt hn
    have hp0_le_one : p_zero n ≤ 1 := p_zero_le_one hn1
    rw [abs_mul, abs_neg, abs_of_pos hp0_pos]
    calc p_zero n * |R|
        ≤ 1 * |R| := by apply mul_le_mul_of_nonneg_right hp0_le_one (abs_nonneg _)
      _ = |R| := by ring
      _ ≤ 4 * (epsilon n)^2 / Real.log 2 := hR_bound
  · -- Equation: -p₀ * log₂(p₀) = 2*p₀*ε/log(2) - p₀*R
    rw [hR_eq]
    ring

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

Proof: From entropy_term_step5:
  -p₀ * log₂(p₀) = 2*p₀*ε/log(2) + R₁ where |R₁| ≤ 4*ε²/log(2)

From p_zero_times_eps:
  p₀ * ε = ε + R₂ where |R₂| ≤ 3*ε²

Substituting: 2*p₀*ε/log(2) = 2*(ε + R₂)/log(2) = 2ε/log(2) + 2R₂/log(2)

Total remainder R = R₁ + 2R₂/log(2) with:
  |R| ≤ 4ε²/log(2) + 6ε²/log(2) = 10ε²/log(2)
-/
theorem entropy_term_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 10 * (epsilon n)^2 / Real.log 2 ∧
      -p_zero n * log2 (p_zero n) = 2 * epsilon n / Real.log 2 + R := by
  -- Get the two component expansions
  obtain ⟨R₁, hR₁_bound, hR₁_eq⟩ := entropy_term_step5 hn
  obtain ⟨R₂, hR₂_bound, hR₂_eq⟩ := p_zero_times_eps hn
  -- Total remainder: R₁ + 2*R₂/log(2)
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  use R₁ + 2 * R₂ / Real.log 2
  constructor
  · -- Bound: |R₁ + 2R₂/log(2)| ≤ 10*eps²/log(2)
    calc |R₁ + 2 * R₂ / Real.log 2|
        ≤ |R₁| + |2 * R₂ / Real.log 2| := abs_add_le _ _
      _ = |R₁| + 2 * |R₂| / Real.log 2 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0),
              abs_of_pos hlog2_pos]
      _ ≤ 4 * (epsilon n)^2 / Real.log 2 + 2 * (3 * (epsilon n)^2) / Real.log 2 := by
          apply add_le_add hR₁_bound
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hR₂_bound (by norm_num : (0:ℝ) ≤ 2)
          · exact le_of_lt hlog2_pos
      _ = 10 * (epsilon n)^2 / Real.log 2 := by ring
  · -- Equation: substitute p₀*ε = ε + R₂ into 2*p₀*ε/log(2) + R₁
    have key : 2 * p_zero n * epsilon n = 2 * (epsilon n + R₂) := by
      calc 2 * p_zero n * epsilon n
          = 2 * (p_zero n * epsilon n) := by ring
        _ = 2 * (epsilon n + R₂) := by rw [hR₂_eq]
    calc -p_zero n * log2 (p_zero n)
        = 2 * p_zero n * epsilon n / Real.log 2 + R₁ := hR₁_eq
      _ = 2 * (epsilon n + R₂) / Real.log 2 + R₁ := by rw [key]
      _ = 2 * epsilon n / Real.log 2 + (R₁ + 2 * R₂ / Real.log 2) := by ring

/-- Asymptotic form: entropyTerm_p0 n ~ 2*epsilon/(ln 2) as n -> infinity. -/
theorem entropyTerm_asymptotic {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 10 * (epsilon n)^2 / Real.log 2 ∧
      entropyTerm_p0 n = 2 * epsilon n / Real.log 2 + R := by
  unfold entropyTerm_p0
  exact entropy_term_expansion hn

end Alethfeld.QBF.Rank1.L5Asymptotic
