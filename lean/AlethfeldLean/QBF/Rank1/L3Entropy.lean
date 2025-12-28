/-
  AlethfeldLean.QBF.Rank1.L3Entropy

  Lemma L3: General Entropy Formula for Rank-1 Product State QBFs

  Alethfeld Verified Proof
  Status: IN PROGRESS | Taint: CLEAN

  Key Result: For any rank-1 product state QBF on n qubits,
    S(U) = -p₀ log₂ p₀ + (2n-2)(1-p₀) + 2^{1-n} Σₖ fₖ
  where fₖ = H(xₖ², yₖ², zₖ²) is the Bloch entropy.
-/
import AlethfeldLean.QBF.Rank1.L2Influence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Alethfeld.QBF.Rank1.L3Entropy

open scoped Matrix ComplexConjugate BigOperators
open Real Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L2Influence

variable {n : ℕ}

/-! ## Shannon Entropy Definitions -/

/-- Binary logarithm: log₂(x) = ln(x) / ln(2) -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- log₂(2^k) = k for integer exponents -/
theorem log2_zpow (k : ℤ) : log2 ((2 : ℝ)^k) = k := by
  unfold log2
  rw [Real.log_zpow]
  field_simp

/-- log 2 ≠ 0 -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 := by
  have h : (1 : ℝ) < 2 := by norm_num
  exact ne_of_gt (Real.log_pos h)

/-- log₂(2) = 1 -/
theorem log2_two : log2 2 = 1 := by
  unfold log2
  rw [div_self log_two_ne_zero]

/-- log₂(1) = 0 -/
theorem log2_one : log2 1 = 0 := by
  unfold log2
  simp [Real.log_one]

/-- Logarithm product rule for log₂ -/
theorem log2_mul {x y : ℝ} (hx : x > 0) (hy : y > 0) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  ring

/-- Logarithm of product equals sum of logarithms -/
theorem log2_prod {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, f i > 0) :
    log2 (∏ i, f i) = ∑ i, log2 (f i) := by
  simp only [log2, ← Finset.sum_div]
  congr 1
  have h : ∀ i ∈ Finset.univ, f i ≠ 0 := fun i _ => ne_of_gt (hf i)
  exact Real.log_prod h

/-- Shannon entropy term: -p log₂ p with convention 0 log 0 = 0 -/
noncomputable def entropyTerm (p : ℝ) : ℝ :=
  if p > 0 then -p * log2 p else 0

/-- Bloch entropy: H(x², y², z²) = -Σₗ qₗ log₂ qₗ for ℓ ∈ {1,2,3}
    This is the entropy of the squared Bloch components. -/
noncomputable def blochEntropy (v : BlochVector) : ℝ :=
  entropyTerm (v.q 1) + entropyTerm (v.q 2) + entropyTerm (v.q 3)

/-! ## Probability Distribution Definitions -/

/-- p₀ = (1 - 2^{1-n})² is the Fourier weight of the zero multi-index -/
noncomputable def p_zero (n : ℕ) : ℝ := (1 - (2 : ℝ)^(1 - (n : ℤ)))^2

/-- Fourier weight for α ≠ 0: p_α = 2^{2-2n} ∏_k q_k^{α_k}
    This is the same as L2Influence.probability -/
noncomputable abbrev fourierWeight (bloch : Fin n → BlochVector) (α : MultiIndex n) : ℝ :=
  probability bloch α

/-- Sum of all Fourier weights for α ≠ 0 equals 1 - p₀ -/
theorem sum_fourier_weights (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
    1 - p_zero n := by
  sorry -- Will prove later using Parseval's identity

/-- Total Shannon entropy S(U) of the Fourier distribution -/
noncomputable def totalEntropy (bloch : Fin n → BlochVector) : ℝ :=
  entropyTerm (p_zero n) +
  ∑ α : MultiIndex n, if (∃ k, α k ≠ 0) then entropyTerm (fourierWeight bloch α) else 0

/-! ## Core Lemmas -/

/-! ### L3-step1: Log decomposition for nonzero α

For α ≠ 0, using p_α = 2^{2-2n} ∏_k q_k^{α_k}:
  -p_α log₂ p_α = p_α(2n-2) - p_α Σ_k log₂ q_k^{α_k}
-/

/-- Fourier weight is non-negative -/
theorem fourierWeight_nonneg (bloch : Fin n → BlochVector) (α : MultiIndex n) :
    fourierWeight bloch α ≥ 0 := by
  unfold fourierWeight probability qProduct
  apply mul_nonneg
  · exact le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
  · apply Finset.prod_nonneg
    intro k _
    exact BlochVector.q_nonneg (bloch k) (α k)

/-- qProduct is positive when all q values are positive -/
theorem qProduct_pos (bloch : Fin n → BlochVector) (α : MultiIndex n)
    (hq : ∀ k, (bloch k).q (α k) > 0) : qProduct bloch α > 0 := by
  unfold qProduct
  apply Finset.prod_pos
  intro k _
  exact hq k

/-- Fourier weight is positive when qProduct is positive -/
theorem fourierWeight_pos_of_qProduct_pos (bloch : Fin n → BlochVector) (α : MultiIndex n)
    (hq : ∀ k, (bloch k).q (α k) > 0) : fourierWeight bloch α > 0 := by
  unfold fourierWeight probability
  apply mul_pos
  · exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
  · exact qProduct_pos bloch α hq

/-- Log₂ of fourier weight decomposes as constant plus sum of logs -/
theorem log2_fourierWeight (bloch : Fin n → BlochVector) (α : MultiIndex n)
    (hq : ∀ k, (bloch k).q (α k) > 0) :
    log2 (fourierWeight bloch α) = (2 - 2*(n : ℤ)) + ∑ k, log2 ((bloch k).q (α k)) := by
  unfold fourierWeight probability qProduct
  rw [log2_mul (zpow_pos (by norm_num : (0 : ℝ) < 2) _) (Finset.prod_pos (fun k _ => hq k))]
  rw [log2_zpow]
  rw [log2_prod _ hq]
  -- Goal: ↑(2 - ↑n * 2) + ∑ i, log2 ... = (2 - 2 * ↑n) + ∑ i, log2 ...
  congr 1
  push_cast
  ring

/-- L3-step1: Log decomposition for entropy term
    For α ≠ 0: -p_α log₂ p_α = p_α(2n-2) - p_α Σ_k log₂ q_k^{α_k} -/
theorem log_decomposition (bloch : Fin n → BlochVector) (α : MultiIndex n)
    (hq : ∀ k, (bloch k).q (α k) > 0) :
    -fourierWeight bloch α * log2 (fourierWeight bloch α) =
    fourierWeight bloch α * (2*(n : ℤ) - 2) -
    fourierWeight bloch α * ∑ k, log2 ((bloch k).q (α k)) := by
  rw [log2_fourierWeight bloch α hq]
  ring

/-! ### L3-step2: First sum formula

Σ_{α≠0} p_α(2n-2) = (2n-2)(1-p₀)
-/

/-- First sum in entropy decomposition: factoring out the constant -/
theorem first_sum_formula (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n,
      (if ∃ k, α k ≠ 0 then fourierWeight bloch α * (2*(n : ℤ) - 2) else 0) =
    (2*(n : ℤ) - 2) * (1 - p_zero n) := by
  rw [← Finset.sum_mul]
  congr 1
  conv_lhs =>
    congr
    ext α
    rw [show (if ∃ k, α k ≠ 0 then fourierWeight bloch α * (2*(n : ℤ) - 2) else 0) =
            (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) * (2*(n : ℤ) - 2) by
      split_ifs <;> ring]
  rw [Finset.sum_mul]
  rw [sum_fourier_weights bloch]

/-! ### L3-step3: Zero case helpers

When α_k = 0, we have q^{(0)} = 1, so log₂(q^{(0)}) = 0.
This means only α_k ≠ 0 contributes to the log sum.
-/

/-- q^{(0)} = 1 for any Bloch vector -/
theorem BlochVector.q_zero_eq_one (v : BlochVector) : v.q 0 = 1 := by
  unfold BlochVector.q
  simp

/-- log₂(q^{(0)}) = 0 since q^{(0)} = 1 -/
theorem log2_q_zero (v : BlochVector) : log2 (v.q 0) = 0 := by
  rw [BlochVector.q_zero_eq_one]
  exact log2_one

/-- When α_k = 0, the log contribution from qubit k is zero -/
theorem log2_q_of_alpha_zero (v : BlochVector) (α : Fin 4) (hα : α = 0) :
    log2 (v.q α) = 0 := by
  rw [hα]
  exact log2_q_zero v

/-- Sum of logs only gets contributions from non-zero α_k -/
theorem sum_log2_q_eq_sum_nonzero (bloch : Fin n → BlochVector) (α : MultiIndex n) :
    ∑ k, log2 ((bloch k).q (α k)) =
    ∑ k, if α k ≠ 0 then log2 ((bloch k).q (α k)) else 0 := by
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rfl
  · push_neg at h
    rw [h, log2_q_zero]
-- TODO: Prove qubit_log_contribution (alethfeld-680)
-- TODO: Prove entropy sum factorization (alethfeld-esk)

/-! ## Main Theorem -/

-- TODO: Prove entropy_formula (alethfeld-7j9)

/-! ## Corollaries -/

-- TODO: Prove entropy_nonneg (alethfeld-xi1)

end Alethfeld.QBF.Rank1.L3Entropy
