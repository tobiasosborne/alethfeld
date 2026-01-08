/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step2_EpsilonSetup

  Step 2: Epsilon Setup and Validity Conditions

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-assume, :L5-assume-1, :L5-assume-1a, :L5-assume-1b,
             :L5-assume-2, :L5-assume-2a, :L5-assume-2b
  Status: CLEAN

  This file establishes:
  - epsilon > 0 for all n >= 1
  - epsilon < 1 for n >= 2 (needed for Taylor series)
  - p_0 > 0 for n >= 2 (log is well-defined)
  - Validity of the epsilon substitution
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step1_Definitions

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy

/-! ## L5-assume: Setting up epsilon = 2^{1-n}

The local assumption introduces epsilon as a shorthand for 2^{1-n}.
This section validates that epsilon satisfies the needed properties.
-/

/-! ### L5-assume-1: epsilon > 0 -/

/-- L5-assume-1a: 2^{1-n} = 2/2^n where 2^n > 0 for all n in N. -/
theorem epsilon_as_ratio (n : ℕ) : epsilon n = 2 / (2 : ℝ)^n := epsilon_eq_div n

/-- L5-assume-1b: Quotient of positive numbers is positive: 2/2^n > 0. -/
theorem epsilon_pos_quotient (n : ℕ) : 2 / (2 : ℝ)^n > 0 := by
  apply div_pos (by norm_num)
  exact pow_pos (by norm_num) n

/-- L5-assume-1: For n >= 1: epsilon = 2^{1-n} > 0.
    (Actually holds for all n, but the statement emphasizes n >= 1.) -/
theorem epsilon_pos_for_n_ge_one {n : ℕ} (_ : n ≥ 1) : epsilon n > 0 :=
  epsilon_pos n

/-! ### L5-assume-2: epsilon < 1 for n >= 2 -/

/-- L5-assume-2a: For n >= 2: 1-n <= -1, hence 2^{1-n} <= 2^{-1}. -/
theorem epsilon_exp_bound {n : ℕ} (hn : n ≥ 2) : 1 - (n : ℤ) ≤ -1 := by omega

theorem epsilon_le_zpow_neg_one {n : ℕ} (hn : n ≥ 2) :
    epsilon n ≤ (2 : ℝ)^((-1) : ℤ) := by
  unfold epsilon
  apply zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ))
  exact epsilon_exp_bound hn

/-- L5-assume-2b: 2^{-1} = 1/2 < 1 by arithmetic. -/
theorem zpow_neg_one_eq_half : (2 : ℝ)^((-1) : ℤ) = 1/2 := by norm_num

theorem half_lt_one : (1 : ℝ)/2 < 1 := by norm_num

/-- L5-assume-2: For n >= 2: epsilon = 2^{1-n} <= 2^{-1} = 1/2 < 1. -/
theorem epsilon_bounds {n : ℕ} (hn : n ≥ 2) :
    epsilon n > 0 ∧ epsilon n ≤ 1/2 ∧ epsilon n < 1 :=
  ⟨epsilon_pos n, epsilon_le_half hn, epsilon_lt_one hn⟩

/-! ## Validity of p_0 for logarithms -/

/-- p_0 = (1 - epsilon)^2 > 0 when 0 < epsilon < 1. -/
theorem p_zero_pos_of_eps_lt_one {n : ℕ} (hn : n ≥ 2) : p_zero n > 0 := by
  rw [p_zero_eq_sq_one_minus_eps]
  have heps : epsilon n < 1 := epsilon_lt_one hn
  have hpos : 1 - epsilon n > 0 := by linarith
  exact sq_pos_of_pos hpos

/-- p_0 < 1 when epsilon > 0. -/
theorem p_zero_lt_one_of_eps_pos {n : ℕ} (hn : n ≥ 1) : p_zero n < 1 := by
  have hp := p_zero_le_one hn
  have hne : p_zero n ≠ 1 := by
    intro heq
    rw [p_zero_eq_sq_one_minus_eps] at heq
    have : 1 - epsilon n = 1 ∨ 1 - epsilon n = -1 := sq_eq_one_iff.mp heq
    cases this with
    | inl h =>
      have : epsilon n = 0 := by linarith
      have hpos := epsilon_pos n
      linarith
    | inr h =>
      have : epsilon n = 2 := by linarith
      have hle : epsilon n ≤ 1 := by
        calc epsilon n = (2 : ℝ)^(1 - (n : ℤ)) := rfl
          _ ≤ (2 : ℝ)^(0 : ℤ) := by
            apply zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ))
            omega
          _ = 1 := by norm_num
      linarith
  exact lt_of_le_of_ne hp hne

/-- 0 < p_0 < 1 for n >= 2, so log_2(p_0) is well-defined. -/
theorem p_zero_in_unit_interval {n : ℕ} (hn : n ≥ 2) :
    0 < p_zero n ∧ p_zero n < 1 :=
  ⟨p_zero_pos_of_eps_lt_one hn, p_zero_lt_one_of_eps_pos (by omega)⟩

/-! ## Validity of 1 - p_0 -/

/-- 1 - p_0 = 2*epsilon - epsilon^2 = epsilon * (2 - epsilon) -/
theorem one_minus_p_zero_factored (n : ℕ) :
    1 - p_zero n = epsilon n * (2 - epsilon n) := by
  rw [one_minus_p_zero_eq_eps]
  ring

/-- 1 - p_0 > 0 for n >= 1 -/
theorem one_minus_p_zero_pos {n : ℕ} (hn : n ≥ 1) : 1 - p_zero n > 0 := by
  rw [one_minus_p_zero_factored]
  apply mul_pos (epsilon_pos n)
  have heps : epsilon n ≤ 1 := by
    calc epsilon n = (2 : ℝ)^(1 - (n : ℤ)) := rfl
      _ ≤ (2 : ℝ)^(0 : ℤ) := by
        apply zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ))
        omega
      _ = 1 := by norm_num
  linarith

/-- 1 - p_0 < 1 for n >= 2 -/
theorem one_minus_p_zero_lt_one {n : ℕ} (hn : n ≥ 2) : 1 - p_zero n < 1 := by
  have hp : p_zero n > 0 := p_zero_pos_of_eps_lt_one hn
  linarith

end Alethfeld.QBF.Rank1.L5Asymptotic
