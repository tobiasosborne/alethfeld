/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step6_Cancellation

  Step 6: Key Cancellation

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-step4-1, :L5-step4-1a, :L5-step4-1b, :L5-step4-2, :L5-step4-3, :L5-step4-3a
  Status: CLEAN

  This file proves the key cancellation:
  - 2^{n-1} * epsilon = 2^{n-1} * 2^{1-n} = 2^0 = 1

  This remarkable identity allows g(n) to simplify dramatically:
  - g(n) = (2^{n-1}/n) * epsilon * [...] + O(eps)
         = (1/n) * [...] + O(eps)

  Key result (L5-step4-2):
    g(n) = (1/n) * [2/(ln 2) + 4(n-1)] + O(epsilon)
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step5_GnSubstitution

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy

/-! ## L5-step4-1: The key cancellation -/

/-- L5-step4-1a: Exponent law: 2^a * 2^b = 2^{a+b}. -/
theorem exp_add_law (a b : ℤ) : (2 : ℝ)^a * (2 : ℝ)^b = (2 : ℝ)^(a + b) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- L5-step4-1b: (n-1) + (1-n) = n - 1 + 1 - n = 0. -/
theorem exp_cancellation (n : ℤ) : (n - 1) + (1 - n) = 0 := by ring

/-- L5-step4-1 (KEY): 2^{n-1} * epsilon n = 2^{n-1} * 2^{1-n} = 2^0 = 1.

    This is the crucial identity that makes the limit work. -/
theorem key_cancellation (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ)^(n - 1) * epsilon n = 1 := two_pow_pred_mul_eps n hn

/-- Alternative form: (2^{n-1}/n) * epsilon = 1/n. -/
theorem key_cancellation_div (n : ℕ) (hn : n ≥ 1) (hnn : n ≠ 0) :
    (2 : ℝ)^(n - 1) / n * epsilon n = 1 / n := by
  have h := key_cancellation n hn
  field_simp
  linarith [h]

/-! ## L5-step4-2: Simplified g(n) -/

/-- L5-step4-2: g(n) = (1/n) * [2/(ln 2) + 4(n-1)] + O(epsilon).

    Apply the key cancellation to simplify g(n). -/
theorem g_simplified {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (10 / Real.log 2 + 2) * (1 + 1/(n : ℝ)) * epsilon n ∧
      g n = (1 / n) * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R := by
  obtain ⟨R, hR, hg⟩ := g_expansion hn
  use R
  constructor
  · exact hR
  · rw [hg]
    have hkey := key_cancellation_div n (by omega) (by omega)
    calc (2 : ℝ)^(n - 1) / n * epsilon n * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R
        = ((2 : ℝ)^(n - 1) / n * epsilon n) * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R := by ring
      _ = (1 / n) * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R := by rw [hkey]

/-! ## L5-step4-3: Distribute 1/n -/

/-- L5-step4-3a: Distribute (1/n): (1/n)[a + b] = a/n + b/n. -/
theorem distribute_inv (n : ℝ) (a b : ℝ) (hn : n ≠ 0) :
    (1/n) * (a + b) = a/n + b/n := by field_simp

/-- L5-step4-3: g(n) = 2/(n * ln 2) + 4(n-1)/n + O(epsilon). -/
theorem g_distributed {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (10 / Real.log 2 + 2) * (1 + 1/(n : ℝ)) * epsilon n ∧
      g n = 2 / (n * Real.log 2) + 4*((n : ℝ) - 1) / n + R := by
  obtain ⟨R, hR, hg⟩ := g_simplified hn
  use R
  constructor
  · exact hR
  · rw [hg]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    ring_nf

/-! ## Preparation for limit computation -/

/-- 4(n-1)/n = 4 - 4/n (from L5-step4-4, L5-step4-4a, L5-step4-4b). -/
theorem four_n_minus_one_div_n (n : ℝ) (hn : n ≠ 0) :
    4 * (n - 1) / n = 4 - 4/n := by field_simp

/-- L5-step4-5: g(n) = 2/(n * ln 2) + 4 - 4/n + O(epsilon). -/
theorem g_final_form {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (10 / Real.log 2 + 2) * (1 + 1/(n : ℝ)) * epsilon n ∧
      g n = 2 / (n * Real.log 2) + 4 - 4 / n + R := by
  obtain ⟨R, hR, hg⟩ := g_distributed hn
  use R
  constructor
  · exact hR
  · rw [hg]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h4 := four_n_minus_one_div_n (n : ℝ) hn0
    rw [h4]
    ring

end Alethfeld.QBF.Rank1.L5Asymptotic
