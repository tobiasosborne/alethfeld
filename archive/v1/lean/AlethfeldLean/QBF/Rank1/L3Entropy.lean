/-
  AlethfeldLean.QBF.Rank1.L3Entropy

  Lemma L3: General Entropy Formula for Rank-1 Product State QBFs

  Alethfeld Verified Proof
  Status: VERIFIED | Taint: CLEAN

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
  rw [← Fintype.prod_sum (fun k m => (bloch k).q m)]
  -- Each factor is ∑_m q_k^m = 2
  have h : ∀ k : Fin n, ∑ m : Fin 4, (bloch k).q m = 2 := fun k => sum_q_eq_two (bloch k)
  simp only [h, Finset.prod_const, Finset.card_fin, Nat.cast_pow]

/-- Sum of all Fourier weights (including α = 0) -/
theorem sum_all_fourier_weights (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, fourierWeight bloch α = (2 : ℝ)^(2 - (n : ℤ)) := by
  unfold fourierWeight probability
  rw [← Finset.mul_sum]
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
    funext k
    exact h k

/-- ¬(∃ k, α k ≠ 0) iff α = 0 -/
theorem not_exists_ne_zero_iff (α : MultiIndex n) :
    ¬(∃ k, α k ≠ 0) ↔ α = zeroMultiIndex := by
  rw [multiIndex_eq_zero_iff]
  push_neg
  simp only [not_not]

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
    calc (1 - (2 : ℝ)^(1 - (n : ℤ)))^2
        = 1 - 2 * (2 : ℝ)^(1 - (n : ℤ)) + (2 : ℝ)^(1 - (n : ℤ)) * (2 : ℝ)^(1 - (n : ℤ)) := by ring
      _ = 1 - 2 * (2 : ℝ)^(1 - (n : ℤ)) + (2 : ℝ)^(2 - 2*(n : ℤ)) := by rw [hpow]
  rw [h1]
  have h2 : 2 * (2 : ℝ)^(1 - (n : ℤ)) = (2 : ℝ)^(2 - (n : ℤ)) := by
    calc 2 * (2 : ℝ)^(1 - (n : ℤ))
        = (2 : ℝ)^(1 : ℤ) * (2 : ℝ)^(1 - (n : ℤ)) := by simp
      _ = (2 : ℝ)^(1 + (1 - (n : ℤ))) := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ)^(2 - (n : ℤ)) := by congr 1; omega
  rw [h2]
  ring

/-- Sum of all Fourier weights for α ≠ 0 equals 1 - p₀ -/
theorem sum_fourier_weights (bloch : Fin n → BlochVector) :
    ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
    1 - p_zero n := by
  -- Strategy: ∑_{α≠0} p_α = ∑_α p_α - p_0 = 2^{2-n} - 2^{2-2n} = 1 - p_zero n
  have h_total : ∑ α : MultiIndex n, fourierWeight bloch α = (2 : ℝ)^(2 - (n : ℤ)) :=
    sum_all_fourier_weights bloch
  have h_zero : fourierWeight bloch zeroMultiIndex = (2 : ℝ)^(2 - 2*(n : ℤ)) :=
    fourierWeight_zero bloch
  -- The sum with the if-condition equals the sum over nonzero terms plus 0 for zero term
  have h_if_sum : ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
      ∑ α : MultiIndex n, fourierWeight bloch α - fourierWeight bloch zeroMultiIndex := by
    have h1 : ∑ α : MultiIndex n, fourierWeight bloch α =
        fourierWeight bloch zeroMultiIndex +
        ∑ α ∈ Finset.univ.erase zeroMultiIndex, fourierWeight bloch α := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ zeroMultiIndex)]
    have h2 : ∑ α : MultiIndex n, (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) =
        ∑ α ∈ Finset.univ.erase zeroMultiIndex, fourierWeight bloch α := by
      rw [← Finset.sum_filter]
      congr 1
      ext α
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
      constructor
      · intro ⟨k, hk⟩
        constructor
        · intro h
          have heq : α k = zeroMultiIndex k := by rw [h]
          simp only [zeroMultiIndex] at heq
          exact hk heq
        · trivial
      · intro ⟨hne, _⟩
        by_contra h
        push_neg at h
        have heq : α = zeroMultiIndex := by funext k; exact h k
        exact hne heq
    rw [h2, h1]
    ring
  -- Now substitute and solve
  rw [h_if_sum, h_total, h_zero, ← one_minus_p_zero]

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
  -- Factor out the constant: ∑ p_α * c = c * ∑ p_α
  have h : ∑ α : MultiIndex n,
      (if ∃ k, α k ≠ 0 then fourierWeight bloch α * (2*(n : ℤ) - 2) else 0) =
      (2*(n : ℤ) - 2) * ∑ α : MultiIndex n,
      (if ∃ k, α k ≠ 0 then fourierWeight bloch α else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> ring
  rw [h, sum_fourier_weights]

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
  -- Use Finset.sum_sub_distrib to combine the RHS
  rw [← Finset.sum_sub_distrib]
  -- Now show each term is equal
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with h
  · -- For nonzero α, use entropyTerm_pos and log_decomposition
    have hpos : fourierWeight bloch α > 0 := hp α h
    rw [entropyTerm_pos _ hpos]
    -- Need to show: -p_α * log₂(p_α) = p_α(2n-2) - p_α Σ_k log₂(q_k^{α_k})
    -- First we need the hypotheses for log_decomposition
    have hq : ∀ k, (bloch k).q (α k) > 0 := by
      intro k
      by_cases hk : α k = 0
      · rw [hk, BlochVector.q_zero_eq_one]; exact one_pos
      · have hne : α k ≠ 0 := hk
        -- α k ∈ {1, 2, 3}, so use hq_all
        exact hq_all k (α k) hne
    exact log_decomposition bloch α hq
  · -- For zero α, both sides are 0
    ring

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
    -- Simplify: if (∃k, αk≠0) then (if αj≠0 then X else 0) else 0 = if αj≠0 then X else 0
    -- When αj≠0: LHS = X, RHS = X
    -- When αj=0: LHS = 0, RHS = 0
    by_cases hαj : α j ≠ 0
    · -- α j ≠ 0 case: both sides equal the inner expression
      have hex : ∃ k, α k ≠ 0 := ⟨j, hαj⟩
      simp only [hαj, hex, ↓reduceIte, ite_true]
    · -- α j = 0 case: both sides equal 0
      push_neg at hαj
      simp only [hαj, ne_eq, not_true_eq_false, ↓reduceIte, ite_false]
      split_ifs <;> rfl
  rw [h_exchange]
  -- Step 4: Apply entropy_sum_factorization
  rw [← entropy_sum_factorization bloch hq_all]
  -- The goal needs: a + (b - ∑∑f) = a + b + ∑(-∑f)
  -- First convert -∑∑f to ∑(-∑f)
  have h_sum_neg : -∑ x : Fin n, ∑ x_1 : MultiIndex n,
      (if x_1 x ≠ 0 then fourierWeight bloch x_1 * log2 ((bloch x).q (x_1 x)) else 0) =
      ∑ x : Fin n, -∑ x_1 : MultiIndex n,
      (if x_1 x ≠ 0 then fourierWeight bloch x_1 * log2 ((bloch x).q (x_1 x)) else 0) := by
    rw [Finset.sum_neg_distrib]
  linarith [h_sum_neg]

/-! ## Corollaries -/

/-- log₂(x) ≤ 0 for 0 < x ≤ 1 -/
theorem log2_nonpos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : log2 x ≤ 0 := by
  unfold log2
  apply div_nonpos_of_nonpos_of_nonneg
  · exact Real.log_nonpos (le_of_lt hx0) hx1
  · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- entropyTerm is non-negative for 0 ≤ p ≤ 1 -/
theorem entropyTerm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : entropyTerm p ≥ 0 := by
  unfold entropyTerm
  split_ifs with h
  · -- p > 0 case: need -p * log₂(p) ≥ 0
    -- Since 0 < p ≤ 1, log₂(p) ≤ 0, so -log₂(p) ≥ 0, thus -p * log₂(p) ≥ 0
    have hlog : log2 p ≤ 0 := log2_nonpos_of_le_one h hp1
    have : -log2 p ≥ 0 := by linarith
    calc -p * log2 p = p * (-log2 p) := by ring
      _ ≥ 0 := mul_nonneg (le_of_lt h) this
  · -- p ≤ 0 case: result is 0
    linarith

/-- Bloch vector q components are bounded: 0 ≤ q ℓ ≤ 1 for ℓ ∈ {1,2,3} -/
theorem BlochVector.q_le_one (v : BlochVector) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) : v.q ℓ ≤ 1 := by
  -- v.q 1 = x², v.q 2 = y², v.q 3 = z²
  -- Since x² + y² + z² = 1, each component is ≤ 1
  have hsum : v.q 1 + v.q 2 + v.q 3 = 1 := by
    unfold BlochVector.q
    simp only [Fin.isValue, Fin.val_one, ↓reduceIte, Fin.reduceFinMk, Fin.reduceLT, Fin.val_two,
      ite_true, ite_false]
    have := v.norm_sq
    linarith
  have h1 : v.q 1 ≥ 0 := BlochVector.q_nonneg v 1
  have h2 : v.q 2 ≥ 0 := BlochVector.q_nonneg v 2
  have h3 : v.q 3 ≥ 0 := BlochVector.q_nonneg v 3
  fin_cases ℓ <;> simp_all <;> linarith

/-- Bloch entropy is non-negative -/
theorem blochEntropy_nonneg (v : BlochVector) : blochEntropy v ≥ 0 := by
  unfold blochEntropy
  have h1 : entropyTerm (v.q 1) ≥ 0 :=
    entropyTerm_nonneg (BlochVector.q_nonneg v 1) (BlochVector.q_le_one v 1 (by decide))
  have h2 : entropyTerm (v.q 2) ≥ 0 :=
    entropyTerm_nonneg (BlochVector.q_nonneg v 2) (BlochVector.q_le_one v 2 (by decide))
  have h3 : entropyTerm (v.q 3) ≥ 0 :=
    entropyTerm_nonneg (BlochVector.q_nonneg v 3) (BlochVector.q_le_one v 3 (by decide))
  linarith

/-- Total Bloch entropy is non-negative -/
theorem totalBlochEntropy_nonneg (bloch : Fin n → BlochVector) : totalBlochEntropy bloch ≥ 0 := by
  unfold totalBlochEntropy
  apply Finset.sum_nonneg
  intro j _
  exact blochEntropy_nonneg (bloch j)

/-- p_zero n is non-negative -/
theorem p_zero_nonneg (n : ℕ) : p_zero n ≥ 0 := by
  unfold p_zero
  exact sq_nonneg _

/-- p_zero n ≤ 1 for n ≥ 1 -/
theorem p_zero_le_one {n : ℕ} (hn : n ≥ 1) : p_zero n ≤ 1 := by
  unfold p_zero
  have h : (2 : ℝ)^(1 - (n : ℤ)) ≤ 1 := by
    have hexp : 1 - (n : ℤ) ≤ 0 := by omega
    exact zpow_le_one_of_nonpos₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp
  have hpos : (2 : ℝ)^(1 - (n : ℤ)) > 0 := zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have h' : 1 - (2 : ℝ)^(1 - (n : ℤ)) ≥ 0 := by linarith
  have h'' : 1 - (2 : ℝ)^(1 - (n : ℤ)) ≤ 1 := by linarith
  calc (1 - (2 : ℝ)^(1 - (n : ℤ)))^2 ≤ 1^2 := by
        apply sq_le_sq'
        · linarith
        · linarith
    _ = 1 := by ring

/-- 1 - p_zero n ≥ 0 for n ≥ 1 -/
theorem one_minus_p_zero_nonneg {n : ℕ} (hn : n ≥ 1) : 1 - p_zero n ≥ 0 := by
  have h := p_zero_le_one hn
  linarith

/-- L3 Corollary: Entropy is non-negative

For any rank-1 product state QBF on n ≥ 1 qubits:
  S(U) ≥ 0
-/
theorem entropy_nonneg (bloch : Fin n → BlochVector)
    (hn : n ≥ 1)
    (hq_all : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0)
    (hp : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) → fourierWeight bloch α > 0) :
    totalEntropy bloch ≥ 0 := by
  rw [entropy_formula bloch hq_all hp]
  have h1 : entropyTerm (p_zero n) ≥ 0 :=
    entropyTerm_nonneg (p_zero_nonneg n) (p_zero_le_one hn)
  have h2 : (2*(n : ℤ) - 2) * (1 - p_zero n) ≥ 0 := by
    apply mul_nonneg
    · have hint : (0 : ℤ) ≤ 2 * (n : ℤ) - 2 := by omega
      have : (0 : ℝ) ≤ ((2 * (n : ℤ) - 2) : ℤ) := by exact Int.cast_nonneg hint
      convert this using 1
      push_cast
      ring
    · exact one_minus_p_zero_nonneg hn
  have h3 : (2 : ℝ)^(1 - (n : ℤ)) * totalBlochEntropy bloch ≥ 0 := by
    apply mul_nonneg
    · exact le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    · exact totalBlochEntropy_nonneg bloch
  linarith

end Alethfeld.QBF.Rank1.L3Entropy
