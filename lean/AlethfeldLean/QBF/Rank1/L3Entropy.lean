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

/-- The zero multi-index (all components are 0) -/
def zeroMultiIndex : MultiIndex n := fun _ => 0

/-- qProduct at zero multi-index is 1 -/
theorem qProduct_zero (bloch : Fin n → BlochVector) :
    qProduct bloch zeroMultiIndex = 1 := by
  unfold qProduct zeroMultiIndex
  simp only [BlochVector.q_zero_eq_one, Finset.prod_const_one]

/-- fourierWeight at zero multi-index -/
theorem fourierWeight_zero (bloch : Fin n → BlochVector) :
    fourierWeight bloch zeroMultiIndex = (2 : ℝ)^(2 - 2*(n : ℤ)) := by
  unfold fourierWeight probability
  rw [qProduct_zero, mul_one]

/-- Sum of qProducts over all multi-indices (Fubini) -/
theorem sum_qProduct (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, qProduct bloch α = (2 : ℝ)^n := by
  unfold qProduct
  -- Apply Fubini: ∑_α ∏_k f(α_k) = ∏_k ∑_m f(m)
  rw [Fintype.prod_sum]
  -- Each factor is ∑_m q_k^m = 2
  have h : ∀ k : Fin n, ∑ m : Fin 4, (bloch k).q m = 2 := fun k => sum_q_eq_two (bloch k)
  simp only [h]
  -- Product of 2's is 2^n
  simp only [Finset.prod_const, Finset.card_fin]
  norm_cast

/-- Sum of all Fourier weights (including α = 0) -/
theorem sum_all_fourier_weights (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, fourierWeight bloch α = (2 : ℝ)^(2 - (n : ℤ)) := by
  unfold fourierWeight probability
  rw [← Finset.sum_mul]
  rw [sum_qProduct]
  -- 2^{2-2n} * 2^n = 2^{2-n}
  rw [← zpow_natCast (2 : ℝ) n]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

/-- α = 0 iff ∀ k, α k = 0 -/
theorem multiIndex_eq_zero_iff (α : MultiIndex n) :
    α = zeroMultiIndex ↔ ∀ k, α k = 0 := by
  constructor
  · intro h k
    rw [h]
    rfl
  · intro h
    ext k
    exact h k

/-- ¬(∃ k, α k ≠ 0) iff α = 0 -/
theorem not_exists_ne_zero_iff (α : MultiIndex n) :
    ¬(∃ k, α k ≠ 0) ↔ α = zeroMultiIndex := by
  rw [multiIndex_eq_zero_iff]
  push_neg
  constructor
  · intro h k
    by_contra hc
    exact h k hc
  · intro h k hk
    exact hk (h k)

/-- Simplify 1 - p_zero n -/
theorem one_minus_p_zero (n : ℕ) :
    1 - p_zero n = (2 : ℝ)^(2 - (n : ℤ)) - (2 : ℝ)^(2 - 2*(n : ℤ)) := by
  unfold p_zero
  -- (1 - 2^{1-n})² = 1 - 2·2^{1-n} + 2^{2-2n}
  -- So 1 - (1 - 2^{1-n})² = 2·2^{1-n} - 2^{2-2n} = 2^{2-n} - 2^{2-2n}
  have h1 : (1 - (2 : ℝ)^(1 - (n : ℤ)))^2 =
            1 - 2 * (2 : ℝ)^(1 - (n : ℤ)) + (2 : ℝ)^(2 - 2*(n : ℤ)) := by
    have hpow : (2 : ℝ)^(1 - (n : ℤ)) * (2 : ℝ)^(1 - (n : ℤ)) = (2 : ℝ)^(2 - 2*(n : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      omega
    ring_nf
    rw [hpow]
    ring
  rw [h1]
  have h2 : 2 * (2 : ℝ)^(1 - (n : ℤ)) = (2 : ℝ)^(2 - (n : ℤ)) := by
    have : (2 : ℝ) = (2 : ℝ)^(1 : ℤ) := by simp
    rw [this, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [h2]
  ring

/-- Sum of all Fourier weights for α ≠ 0 equals 1 - p₀ -/
theorem sum_fourier_weights (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
    1 - p_zero n := by
  -- Strategy: total sum - contribution at α=0 = sum over α≠0
  -- Split: ∑_α f(α) = ∑_{α≠0} f(α) + f(0)
  have h_split : ∑ α : MultiIndex n, fourierWeight bloch α =
      ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) +
      fourierWeight bloch zeroMultiIndex := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    by_cases h : ∃ k, α k ≠ 0
    · simp only [h, ↓reduceIte, add_zero]
    · simp only [h, ↓reduceIte, zero_add]
      rw [not_exists_ne_zero_iff] at h
      rw [h]
  -- Rearrange to get the sum we want
  rw [sum_all_fourier_weights, fourierWeight_zero] at h_split
  -- ∑_{α≠0} f = total - f(0) = 2^{2-n} - 2^{2-2n}
  have h_result : ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
      (2 : ℝ)^(2 - (n : ℤ)) - (2 : ℝ)^(2 - 2*(n : ℤ)) := by
    linarith
  rw [h_result, ← one_minus_p_zero]

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
/-! ### L3-step5: Qubit log contribution

The log contribution from qubit j equals 2^{1-n} times the Bloch entropy f_j.
-Σ_{α: α_j≠0} p_α log₂ q_j^{α_j} = 2^{1-n} f_j
-/

/-- Sum over α with α_j = ℓ of p_α equals partial sum (helper) -/
theorem sum_prob_fixed_j (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) :
    ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α else 0) =
    partialSum bloch j ℓ := rfl

/-- Log contribution from qubit j for fixed α_j = ℓ -/
theorem log_contribution_fixed_ell (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0)
    (hq : (bloch j).q ℓ > 0) :
    ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α * log2 ((bloch j).q ℓ) else 0) =
    (2 : ℝ)^(1 - (n : ℤ)) * (bloch j).q ℓ * log2 ((bloch j).q ℓ) := by
  -- Factor out the log term (it's constant across all α with α_j = ℓ)
  have factor_log : ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α * log2 ((bloch j).q ℓ) else 0) =
      log2 ((bloch j).q ℓ) * ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> ring
  rw [factor_log, sum_prob_fixed_j, partial_sum_simplified bloch j ℓ hℓ]
  ring

/-- Sum of log contributions for nonzero ℓ -/
theorem sum_log_contributions (bloch : Fin n → BlochVector) (j : Fin n)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0) :
    ∑ ℓ : Fin 4, (if ℓ ≠ 0 then
      ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α * log2 ((bloch j).q ℓ) else 0)
    else 0) =
    (2 : ℝ)^(1 - (n : ℤ)) * ∑ ℓ : Fin 4, (if ℓ ≠ 0 then (bloch j).q ℓ * log2 ((bloch j).q ℓ) else 0) := by
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  -- Apply log_contribution_fixed_ell to each nonzero term
  rw [log_contribution_fixed_ell bloch j 1 (by decide) (hq 1 (by decide)),
      log_contribution_fixed_ell bloch j 2 (by decide) (hq 2 (by decide)),
      log_contribution_fixed_ell bloch j 3 (by decide) (hq 3 (by decide))]
  ring

/-- Relating entropyTerm sum to direct computation -/
theorem blochEntropy_eq_sum (v : BlochVector) (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) :
    blochEntropy v = -∑ ℓ : Fin 4, (if ℓ ≠ 0 then v.q ℓ * log2 (v.q ℓ) else 0) := by
  unfold blochEntropy entropyTerm
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  simp only [hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), ↓reduceIte]
  ring

/-- Partition the α-sum by value of α_j -/
theorem sum_partition_by_j (bloch : Fin n → BlochVector) (j : Fin n) (f : MultiIndex n → ℝ) :
    ∑ α : MultiIndex n, (if α j ≠ 0 then f α else 0) =
    ∑ ℓ : Fin 4, (if ℓ ≠ 0 then ∑ α : MultiIndex n, (if α j = ℓ then f α else 0) else 0) := by
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  conv_lhs =>
    arg 2
    ext α
    rw [show (if α j ≠ 0 then f α else 0) =
            (if α j = 1 then f α else 0) + (if α j = 2 then f α else 0) +
            (if α j = 3 then f α else 0) by
      rcases Fin.eq_zero_or_eq_succ (α j) with h0 | ⟨k, hk⟩
      · simp [h0]
      · rcases Fin.eq_zero_or_eq_succ k with hk0 | ⟨k', hk'⟩
        · simp [hk, hk0]
        · rcases Fin.eq_zero_or_eq_succ k' with hk'0 | ⟨k'', hk''⟩
          · simp [hk, hk', hk'0]
          · have : k'' = 0 := Fin.eq_zero k''
            simp [hk, hk', hk'', this]]
  simp only [Finset.sum_add_distrib]

/-- L3-step5: Qubit log contribution
    The negative sum of p_α log₂(q_j^{α_j}) over α with α_j ≠ 0 equals 2^{1-n} * f_j -/
theorem qubit_log_contribution (bloch : Fin n → BlochVector) (j : Fin n)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0) :
    -∑ α : MultiIndex n, (if α j ≠ 0 then fourierWeight bloch α * log2 ((bloch j).q (α j)) else 0) =
    (2 : ℝ)^(1 - (n : ℤ)) * blochEntropy (bloch j) := by
  -- Step 1: Partition the sum by α_j = ℓ
  rw [sum_partition_by_j bloch j (fun α => fourierWeight bloch α * log2 ((bloch j).q (α j)))]
  -- Step 2: For each ℓ, the inner sum simplifies because log₂(q_j^{α_j}) = log₂(q_j^ℓ) when α_j = ℓ
  have h_inner : ∀ ℓ : Fin 4, ℓ ≠ 0 →
      ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α * log2 ((bloch j).q (α j)) else 0) =
      ∑ α : MultiIndex n, (if α j = ℓ then fourierWeight bloch α * log2 ((bloch j).q ℓ) else 0) := by
    intro ℓ _
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with h
    · rw [h]
    · rfl
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  rw [h_inner 1 (by decide), h_inner 2 (by decide), h_inner 3 (by decide)]
  -- Step 3: Apply sum_log_contributions (but manually since we already expanded)
  rw [log_contribution_fixed_ell bloch j 1 (by decide) (hq 1 (by decide)),
      log_contribution_fixed_ell bloch j 2 (by decide) (hq 2 (by decide)),
      log_contribution_fixed_ell bloch j 3 (by decide) (hq 3 (by decide))]
  -- Step 4: Factor and use blochEntropy_eq_sum
  rw [blochEntropy_eq_sum (bloch j) hq]
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  ring

/-! ### L3-step6: Entropy sum factorization

The sum over all qubits of log contributions equals 2^{1-n} times the sum of Bloch entropies.
-/

/-- Sum of Bloch entropies over all qubits -/
noncomputable def totalBlochEntropy (bloch : Fin n → BlochVector) : ℝ :=
  ∑ j, blochEntropy (bloch j)

/-- L3-step6: Sum of qubit log contributions factors as 2^{1-n} * Σ_k f_k -/
theorem entropy_sum_factorization (bloch : Fin n → BlochVector)
    (hq : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0) :
    ∑ j : Fin n, -∑ α : MultiIndex n,
      (if α j ≠ 0 then fourierWeight bloch α * log2 ((bloch j).q (α j)) else 0) =
    (2 : ℝ)^(1 - (n : ℤ)) * totalBlochEntropy bloch := by
  unfold totalBlochEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact qubit_log_contribution bloch j (hq j)

/-! ## Main Theorem -/

/-- Expand entropyTerm when p > 0 -/
theorem entropyTerm_pos (p : ℝ) (hp : p > 0) : entropyTerm p = -p * log2 p := by
  unfold entropyTerm
  simp [hp]

/-- Sum of entropy terms equals decomposed form (helper) -/
theorem entropy_sum_decomposition (bloch : Fin n → BlochVector)
    (hq_all : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0)
    (hp : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) → fourierWeight bloch α > 0) :
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then entropyTerm (fourierWeight bloch α) else 0) =
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α * (2*(n : ℤ) - 2) else 0) -
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then
      fourierWeight bloch α * ∑ k, log2 ((bloch k).q (α k)) else 0) := by
  -- Expand entropyTerm using log_decomposition
  have h_expand : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) →
      entropyTerm (fourierWeight bloch α) =
      fourierWeight bloch α * (2*(n : ℤ) - 2) -
      fourierWeight bloch α * ∑ k, log2 ((bloch k).q (α k)) := by
    intro α hα
    have hpos := hp α hα
    rw [entropyTerm_pos _ hpos]
    -- Need hypothesis that all q values are positive for log_decomposition
    have hq : ∀ k, (bloch k).q (α k) > 0 := by
      intro k
      by_cases hk : α k = 0
      · rw [hk, BlochVector.q_zero_eq_one]; norm_num
      · exact hq_all k (α k) hk
    rw [log_decomposition bloch α hq]
    ring
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with h
  · exact h_expand α h
  · ring

/-- L3-qed: General Entropy Formula for Rank-1 Product State QBFs

For any rank-1 product state QBF on n qubits with generic Bloch vectors:
  S(U) = entropyTerm(p₀) + (2n-2)(1-p₀) + 2^{1-n} Σₖ fₖ

where:
- p₀ = (1 - 2^{1-n})² is the Fourier weight of the zero index
- fₖ = H(xₖ², yₖ², zₖ²) is the Bloch entropy of qubit k
-/
theorem entropy_formula (bloch : Fin n → BlochVector)
    (hq_all : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0)
    (hp : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) → fourierWeight bloch α > 0) :
    totalEntropy bloch =
    entropyTerm (p_zero n) + (2*(n : ℤ) - 2) * (1 - p_zero n) +
    (2 : ℝ)^(1 - (n : ℤ)) * totalBlochEntropy bloch := by
  unfold totalEntropy
  -- Step 1: Apply entropy_sum_decomposition
  rw [entropy_sum_decomposition bloch hq_all hp]
  -- Step 2: The first sum gives (2n-2)(1-p₀) by first_sum_formula
  rw [first_sum_formula]
  -- Step 3: The second sum needs to be converted to entropy_sum_factorization form
  -- We need to exchange sum over α with sum over k
  have h_exchange : ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then
        fourierWeight bloch α * ∑ k, log2 ((bloch k).q (α k)) else 0) =
      ∑ j : Fin n, ∑ α : MultiIndex n,
        (if α j ≠ 0 then fourierWeight bloch α * log2 ((bloch j).q (α j)) else 0) := by
    -- First, use sum_log2_q_eq_sum_nonzero to only sum over nonzero α_k
    conv_lhs =>
      arg 2
      ext α
      rw [show (if ∃ k, α k ≠ 0 then fourierWeight bloch α * ∑ k, log2 ((bloch k).q (α k)) else 0) =
              (if ∃ k, α k ≠ 0 then fourierWeight bloch α *
                ∑ k, (if α k ≠ 0 then log2 ((bloch k).q (α k)) else 0) else 0) by
        split_ifs with h
        · rw [sum_log2_q_eq_sum_nonzero]
        · rfl]
    -- Distribute the product into the sum
    conv_lhs =>
      arg 2
      ext α
      rw [show (if ∃ k, α k ≠ 0 then fourierWeight bloch α *
                ∑ k, (if α k ≠ 0 then log2 ((bloch k).q (α k)) else 0) else 0) =
              ∑ k, (if ∃ j, α j ≠ 0 then
                (if α k ≠ 0 then fourierWeight bloch α * log2 ((bloch k).q (α k)) else 0) else 0) by
        split_ifs with h
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> ring
        · simp]
    -- Exchange sums
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    -- Simplify: if (∃k, αk≠0) ∧ (αj≠0) then ... else 0
    -- But if αj≠0 then ∃k, αk≠0, so we can simplify
    split_ifs with h1 h2
    · rfl
    · exfalso; exact h2 ⟨j, h1⟩
    · rfl
    · rfl
  rw [h_exchange]
  -- Step 4: Apply entropy_sum_factorization
  rw [← entropy_sum_factorization bloch hq_all]
  ring

/-! ## Corollaries -/

-- TODO: Prove entropy_nonneg (alethfeld-xi1)

end Alethfeld.QBF.Rank1.L3Entropy
