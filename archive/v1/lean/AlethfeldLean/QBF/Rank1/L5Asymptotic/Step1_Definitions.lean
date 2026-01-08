/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step1_Definitions

  Step 1: Core Definitions for L5 Asymptotic Theorem

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :0-D-eps, :0-L4cor, :L5-assume-3, :L5-assume-4
  Status: CLEAN

  This file defines:
  - epsilon n: The small parameter epsilon = 2^{1-n}
  - p_zero_eps: p_0 = (1 - epsilon)^2
  - one_minus_p_zero_eps: 1 - p_0 = 2*epsilon - epsilon^2
  - g_n: The correction term g(n) = S/I - log_2(3)
-/
import AlethfeldLean.QBF.Rank1.L4Maximum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy
open Alethfeld.QBF.Rank1.ShannonMax

/-! ## 0-D-eps: Definition of epsilon -/

/-- The small parameter epsilon = 2^{1-n}.
    For large n, epsilon -> 0. -/
noncomputable def epsilon (n : ℕ) : ℝ := (2 : ℝ)^(1 - (n : ℤ))

/-- epsilon n = 2/2^n -/
theorem epsilon_eq_div (n : ℕ) : epsilon n = 2 / (2 : ℝ)^n := by
  unfold epsilon
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp [zpow_natCast]

/-- epsilon n > 0 for all n -/
theorem epsilon_pos (n : ℕ) : epsilon n > 0 := by
  unfold epsilon
  exact zpow_pos (by norm_num : (0 : ℝ) < 2) _

/-- epsilon n <= 1/2 for n >= 2 -/
theorem epsilon_le_half {n : ℕ} (hn : n ≥ 2) : epsilon n ≤ 1/2 := by
  unfold epsilon
  have hexp : 1 - (n : ℤ) ≤ -1 := by omega
  calc (2 : ℝ)^(1 - (n : ℤ))
      ≤ (2 : ℝ)^((-1) : ℤ) := by
        apply zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp
    _ = 1/2 := by norm_num

/-- epsilon n < 1 for n >= 2 -/
theorem epsilon_lt_one {n : ℕ} (hn : n ≥ 2) : epsilon n < 1 := by
  calc epsilon n ≤ 1/2 := epsilon_le_half hn
    _ < 1 := by norm_num

/-- epsilon n -> 0 as n -> infinity -/
theorem epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0) := by
  -- epsilon n = 2 / 2^n = 2 * (2^n)^{-1}
  -- Since 2^n -> ∞, (2^n)^{-1} -> 0, so 2 * (2^n)^{-1} -> 0
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hinv := hpow.inv_tendsto_atTop
  have hmul := hinv.const_mul 2
  simp only [mul_zero] at hmul
  refine Tendsto.congr ?_ hmul
  intro n
  rw [epsilon_eq_div, Pi.inv_apply]
  ring

/-! ## p_0 and 1 - p_0 in terms of epsilon -/

/-- p_0 = (1 - epsilon)^2 (from L5-assume-3) -/
theorem p_zero_eq_sq_one_minus_eps (n : ℕ) :
    p_zero n = (1 - epsilon n)^2 := by
  unfold p_zero epsilon
  ring

/-- 1 - p_0 = 2*epsilon - epsilon^2 (from L5-assume-4) -/
theorem one_minus_p_zero_eq_eps (n : ℕ) :
    1 - p_zero n = 2 * epsilon n - (epsilon n)^2 := by
  rw [p_zero_eq_sq_one_minus_eps]
  ring

/-- Binomial expansion: (1 - epsilon)^2 = 1 - 2*epsilon + epsilon^2 (from L5-assume-4a) -/
theorem sq_one_minus_eps (eps : ℝ) :
    (1 - eps)^2 = 1 - 2*eps + eps^2 := by ring

/-- 1 - (1 - 2*eps + eps^2) = 2*eps - eps^2 (from L5-assume-4b) -/
theorem one_minus_expand (eps : ℝ) :
    1 - (1 - 2*eps + eps^2) = 2*eps - eps^2 := by ring

/-! ## The correction term g(n) -/

/-- The correction term g(n) = S/I - log_2(3).

    From L4-cor (assumption :0-L4cor):
      S/I = log_2(3) + (2^{n-1}/n) * [-p_0 * log_2(p_0) + (2n-2)(1-p_0)]

    So g(n) = (2^{n-1}/n) * [-p_0 * log_2(p_0) + (2n-2)(1-p_0)]

    The main theorem will show lim_{n->∞} g(n) = 4.
-/
noncomputable def g (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (2 : ℝ)^(n - 1) / n * (-p_zero n * L3Entropy.log2 (p_zero n) + (2*n - 2) * (1 - p_zero n))

/-- Alternative form: g(n) = (2^{n-1}/n) * (entropy term + influence term) -/
noncomputable def entropyTerm_p0 (n : ℕ) : ℝ := -p_zero n * L3Entropy.log2 (p_zero n)
noncomputable def influenceTerm_p0 (n : ℕ) : ℝ := (2*(n : ℝ) - 2) * (1 - p_zero n)

theorem g_eq_sum {n : ℕ} (hn : n ≠ 0) :
    g n = (2 : ℝ)^(n - 1) / n * (entropyTerm_p0 n + influenceTerm_p0 n) := by
  unfold g entropyTerm_p0 influenceTerm_p0
  simp [hn]

/-! ## Helper lemmas for 2^{n-1} -/

/-- 2^{n-1} as integer power -/
theorem two_pow_pred (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ)^(n - 1) = (2 : ℝ)^((n : ℤ) - 1) := by
  rw [← zpow_natCast]
  congr 1
  have h : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  exact h.symm

/-- Key identity: 2^{n-1} * epsilon n = 1 (from L5-step4-1) -/
theorem two_pow_pred_mul_eps (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ)^(n - 1) * epsilon n = 1 := by
  unfold epsilon
  rw [two_pow_pred n hn]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h : ((n : ℤ) - 1) + (1 - (n : ℤ)) = 0 := by ring
  rw [h, zpow_zero]

/-- Corollary: 2^{n-1} * 2^{1-n} = 1 (exponent form from L5-step4-1a, L5-step4-1b) -/
theorem zpow_add_cancel (n : ℤ) :
    (2 : ℝ)^(n - 1) * (2 : ℝ)^(1 - n) = 1 := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h : (n - 1) + (1 - n) = 0 := by ring
  rw [h, zpow_zero]

/-! ## epsilon^2 formulas -/

/-- epsilon^2 = 2^{2-2n} = 4/4^n (from L5-step2-4a) -/
theorem epsilon_sq (n : ℕ) : (epsilon n)^2 = (2 : ℝ)^(2 - 2*(n : ℤ)) := by
  unfold epsilon
  rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- epsilon^2 = 4^{1-n} (alternative form) -/
theorem epsilon_sq_alt (n : ℕ) : (epsilon n)^2 = (4 : ℝ)^(1 - (n : ℤ)) := by
  rw [epsilon_sq]
  have h : (4 : ℝ)^(1 - (n : ℤ)) = (2 : ℝ)^(2 * (1 - (n : ℤ))) := by
    have h4 : (4 : ℝ) = (2 : ℝ)^(2 : ℤ) := by norm_num
    rw [h4, ← zpow_mul (2 : ℝ)]
  rw [h]
  congr 1
  ring

end Alethfeld.QBF.Rank1.L5Asymptotic
