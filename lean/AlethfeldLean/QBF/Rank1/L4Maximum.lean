/-
  AlethfeldLean.QBF.Rank1.L4Maximum

  Lemma L4: Maximum at Magic State

  Alethfeld Verified Proof
  Status: IN PROGRESS | Taint: CLEAN

  Key Result: The ratio S/I is maximized when all qubits are in the
  magic state (x², y², z²) = (1/3, 1/3, 1/3).

  Since I = n·2^{1-n} is constant (L2), maximizing S/I reduces to maximizing S.
  By L3, S depends on Bloch vectors only through Σₖ fₖ where fₖ = H(xₖ², yₖ², zₖ²).
  By Shannon's maximum entropy principle, each fₖ ≤ log₂(3) with equality
  iff the distribution is uniform, i.e., (xₖ², yₖ², zₖ²) = (1/3, 1/3, 1/3).
-/
import AlethfeldLean.QBF.Rank1.L3Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped Matrix ComplexConjugate BigOperators
open Real Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L2Influence Alethfeld.QBF.Rank1.L3Entropy

variable {n : ℕ}

/-! ## Magic State Definition -/

/-- A Bloch vector is in the magic state if its squared components are all 1/3.
    This corresponds to the state (1/√3, 1/√3, 1/√3) on the Bloch sphere. -/
def isMagicState (v : BlochVector) : Prop :=
  v.q 1 = 1/3 ∧ v.q 2 = 1/3 ∧ v.q 3 = 1/3

/-- The magic Bloch vector with coordinates (1/√3, 1/√3, 1/√3) -/
noncomputable def magicBlochVector : BlochVector where
  x := 1 / Real.sqrt 3
  y := 1 / Real.sqrt 3
  z := 1 / Real.sqrt 3
  norm_sq := by
    simp only [div_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
    ring

/-- The magic state has q components equal to 1/3 -/
theorem magic_q_one : magicBlochVector.q 1 = 1/3 := by
  unfold magicBlochVector BlochVector.q
  simp only [Fin.isValue, Fin.val_one, ↓reduceIte, div_pow,
    Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
  ring

theorem magic_q_two : magicBlochVector.q 2 = 1/3 := by
  unfold magicBlochVector BlochVector.q
  simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceLT, Fin.val_two, ↓reduceIte, div_pow,
    Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
  ring

theorem magic_q_three : magicBlochVector.q 3 = 1/3 := by
  unfold magicBlochVector BlochVector.q
  simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceLT, ↓reduceIte, div_pow,
    Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
  ring

/-- The magic Bloch vector satisfies isMagicState -/
theorem magicBlochVector_isMagicState : isMagicState magicBlochVector :=
  ⟨magic_q_one, magic_q_two, magic_q_three⟩

/-- 1/3 > 0 -/
theorem one_third_pos : (1 : ℝ) / 3 > 0 := by norm_num

/-- Magic state has positive q values for nonzero indices -/
theorem magic_q_pos (ℓ : Fin 4) (hℓ : ℓ ≠ 0) : magicBlochVector.q ℓ > 0 := by
  rcases Fin.eq_zero_or_eq_succ ℓ with h0 | ⟨k, hk⟩
  · exact absurd h0 hℓ
  · rcases Fin.eq_zero_or_eq_succ k with hk0 | ⟨k', hk'⟩
    · simp only [hk, hk0]
      show magicBlochVector.q 1 > 0
      rw [magic_q_one]; exact one_third_pos
    · rcases Fin.eq_zero_or_eq_succ k' with hk'0 | ⟨k'', hk''⟩
      · simp only [hk, hk', hk'0]
        show magicBlochVector.q 2 > 0
        rw [magic_q_two]; exact one_third_pos
      · have : k'' = 0 := Fin.eq_zero k''
        simp only [hk, hk', hk'', this]
        show magicBlochVector.q 3 > 0
        rw [magic_q_three]; exact one_third_pos

/-! ## Shannon Entropy Maximum Principle -/

/-- Maximum entropy for 3 outcomes is log₂(3) -/
noncomputable def maxEntropy3 : ℝ := log2 3

/-- log₂(1/3) = -log₂(3) -/
theorem log2_one_third : log2 (1/3) = -log2 3 := by
  unfold log2
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
  simp [Real.log_one]
  ring

/-- entropyTerm for p > 0 -/
lemma entropyTerm_of_pos {p : ℝ} (hp : p > 0) : entropyTerm p = -p * log2 p := by
  unfold entropyTerm; simp [hp]

/-- Uniform distribution achieves maximum: H(1/3, 1/3, 1/3) = log₂(3) -/
theorem uniform_achieves_max :
    entropyTerm (1/3) + entropyTerm (1/3) + entropyTerm (1/3) = log2 3 := by
  simp only [entropyTerm_of_pos one_third_pos]
  rw [log2_one_third]
  ring

/-- Bloch entropy at magic state equals log₂(3) -/
theorem blochEntropy_magic : blochEntropy magicBlochVector = log2 3 := by
  unfold blochEntropy
  rw [magic_q_one, magic_q_two, magic_q_three]
  exact uniform_achieves_max

/-! ## Shannon Maximum Entropy Theorem

We prove that H(p₁, p₂, p₃) ≤ log₂(3) for any probability distribution,
with equality iff p₁ = p₂ = p₃ = 1/3.

This follows from the strict concavity of x log x.
-/

/-- Key lemma: For p > 0, we have -p log₂(p) ≤ p log₂(3) + (1/3 - p) / log(2)
    This follows from log(x) ≤ x - 1 applied to x = 1/(3p). -/
theorem entropyTerm_le_helper (p : ℝ) (hp : p > 0) :
    -p * log2 p ≤ p * log2 3 + (1/3 - p) / Real.log 2 := by
  have h3p_pos : 3 * p > 0 := by linarith
  have h_inv_pos : 1 / (3 * p) > 0 := by positivity
  have hlog_ineq : Real.log (1 / (3 * p)) ≤ 1 / (3 * p) - 1 :=
    Real.log_le_sub_one_of_pos h_inv_pos
  have h_log_inv : Real.log (1 / (3 * p)) = -Real.log (3 * p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) h3p_pos.ne.symm, Real.log_one, zero_sub]
  have h_log_3p : Real.log (3 * p) = Real.log 3 + Real.log p := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hp)]
  rw [h_log_inv, h_log_3p] at hlog_ineq
  have hmul : p * (-(Real.log 3 + Real.log p)) ≤ p * (1 / (3 * p) - 1) := by
    apply mul_le_mul_of_nonneg_left hlog_ineq (le_of_lt hp)
  have hineq_nat : -p * Real.log p ≤ p * Real.log 3 + (1/3 - p) := by
    rw [neg_add] at hmul
    rw [mul_neg, mul_neg] at hmul
    -- hmul: -p * log 3 + -p * log p ≤ p * (1/(3p) - 1)
    have hrhs : p * (1 / (3 * p) - 1) = 1/3 - p := by
      field_simp; ring
    rw [hrhs] at hmul
    linarith
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold log2
  calc -p * (Real.log p / Real.log 2)
      = (-p * Real.log p) / Real.log 2 := by ring
    _ ≤ (p * Real.log 3 + (1/3 - p)) / Real.log 2 := by
        apply div_le_div_of_nonneg_right hineq_nat (le_of_lt hlog2_pos)
    _ = p * (Real.log 3 / Real.log 2) + (1/3 - p) / Real.log 2 := by ring

/-- Strict version: For p > 0 and p ≠ 1/3, the entropy term is strictly bounded. -/
theorem entropyTerm_lt_helper (p : ℝ) (hp : p > 0) (hp_ne : p ≠ 1/3) :
    -p * log2 p < p * log2 3 + (1/3 - p) / Real.log 2 := by
  have h3p_pos : 3 * p > 0 := by linarith
  have h_inv_pos : 1 / (3 * p) > 0 := by positivity
  have h_x_ne_one : 1 / (3 * p) ≠ 1 := by
    intro h; field_simp [hp.ne.symm] at h; linarith
  have hlog_ineq : Real.log (1 / (3 * p)) < 1 / (3 * p) - 1 :=
    Real.log_lt_sub_one_of_pos h_inv_pos h_x_ne_one
  have h_log_inv : Real.log (1 / (3 * p)) = -Real.log (3 * p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) h3p_pos.ne.symm, Real.log_one, zero_sub]
  have h_log_3p : Real.log (3 * p) = Real.log 3 + Real.log p := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hp)]
  rw [h_log_inv, h_log_3p] at hlog_ineq
  have hmul : p * (-(Real.log 3 + Real.log p)) < p * (1 / (3 * p) - 1) := by
    apply mul_lt_mul_of_pos_left hlog_ineq hp
  have hineq_nat : -p * Real.log p < p * Real.log 3 + (1/3 - p) := by
    rw [neg_add] at hmul
    rw [mul_neg, mul_neg] at hmul
    have hrhs : p * (1 / (3 * p) - 1) = 1/3 - p := by
      field_simp; ring
    rw [hrhs] at hmul
    linarith
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold log2
  calc -p * (Real.log p / Real.log 2)
      = (-p * Real.log p) / Real.log 2 := by ring
    _ < (p * Real.log 3 + (1/3 - p)) / Real.log 2 := by
        rw [div_lt_div_right hlog2_pos]
        exact hineq_nat
    _ = p * (Real.log 3 / Real.log 2) + (1/3 - p) / Real.log 2 := by ring

/-- Helper: entropyTerm bounds sum to log₂(3) -/
theorem entropyTerm_sum_bound (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤
    (p1 + p2 + p3) * log2 3 + ((1/3 - p1) + (1/3 - p2) + (1/3 - p3)) / Real.log 2 := by
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- Handle each term based on whether it's positive
  have h1 : entropyTerm p1 ≤ p1 * log2 3 + (1/3 - p1) / Real.log 2 := by
    by_cases hp1' : p1 > 0
    · rw [entropyTerm_of_pos hp1']; exact entropyTerm_le_helper p1 hp1'
    · push_neg at hp1'; have : p1 = 0 := le_antisymm hp1' hp1
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  have h2 : entropyTerm p2 ≤ p2 * log2 3 + (1/3 - p2) / Real.log 2 := by
    by_cases hp2' : p2 > 0
    · rw [entropyTerm_of_pos hp2']; exact entropyTerm_le_helper p2 hp2'
    · push_neg at hp2'; have : p2 = 0 := le_antisymm hp2' hp2
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  have h3 : entropyTerm p3 ≤ p3 * log2 3 + (1/3 - p3) / Real.log 2 := by
    by_cases hp3' : p3 > 0
    · rw [entropyTerm_of_pos hp3']; exact entropyTerm_le_helper p3 hp3'
    · push_neg at hp3'; have : p3 = 0 := le_antisymm hp3' hp3
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  calc entropyTerm p1 + entropyTerm p2 + entropyTerm p3
      ≤ (p1 * log2 3 + (1/3 - p1) / Real.log 2) +
        (p2 * log2 3 + (1/3 - p2) / Real.log 2) +
        (p3 * log2 3 + (1/3 - p3) / Real.log 2) := by linarith
    _ = (p1 + p2 + p3) * log2 3 + ((1/3 - p1) + (1/3 - p2) + (1/3 - p3)) / Real.log 2 := by ring

/-- Helper: -x log x is concave, so sum is maximized at uniform -/
theorem neg_mul_log_concave_sum (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤ log2 3 := by
  -- Use the helper to get the bound with residual term
  have hbound := entropyTerm_sum_bound p1 p2 p3 hp1 hp2 hp3 hsum
  -- The residual term (1/3 - p1) + (1/3 - p2) + (1/3 - p3) = 1 - (p1 + p2 + p3) = 0
  have hresidual : (1/3 - p1) + (1/3 - p2) + (1/3 - p3) = 0 := by linarith
  -- And (p1 + p2 + p3) * log2 3 = log2 3
  rw [hsum, hresidual] at hbound
  simp at hbound
  exact hbound

/-- Shannon entropy is maximized by uniform distribution -/
theorem shannon_max_uniform (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤ log2 3 :=
  neg_mul_log_concave_sum p1 p2 p3 hp1 hp2 hp3 hsum

/-- Strict inequality for Shannon entropy when not uniform. -/
theorem entropyTerm_sum_lt (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) (hne : p1 ≠ 1/3 ∨ p2 ≠ 1/3 ∨ p3 ≠ 1/3) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 < log2 3 := by
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1le : entropyTerm p1 ≤ p1 * log2 3 + (1/3 - p1) / Real.log 2 := by
    by_cases hp1' : p1 > 0
    · rw [entropyTerm_of_pos hp1']; exact entropyTerm_le_helper p1 hp1'
    · push_neg at hp1'; have : p1 = 0 := le_antisymm hp1' hp1
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  have h2le : entropyTerm p2 ≤ p2 * log2 3 + (1/3 - p2) / Real.log 2 := by
    by_cases hp2' : p2 > 0
    · rw [entropyTerm_of_pos hp2']; exact entropyTerm_le_helper p2 hp2'
    · push_neg at hp2'; have : p2 = 0 := le_antisymm hp2' hp2
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  have h3le : entropyTerm p3 ≤ p3 * log2 3 + (1/3 - p3) / Real.log 2 := by
    by_cases hp3' : p3 > 0
    · rw [entropyTerm_of_pos hp3']; exact entropyTerm_le_helper p3 hp3'
    · push_neg at hp3'; have : p3 = 0 := le_antisymm hp3' hp3
      rw [this]
      unfold entropyTerm; simp
      norm_num; apply div_nonneg; norm_num; exact le_of_lt hlog2_pos
  rcases hne with h1ne | h2ne | h3ne
  · have h1lt : entropyTerm p1 < p1 * log2 3 + (1/3 - p1) / Real.log 2 := by
      by_cases hp1' : p1 > 0
      · rw [entropyTerm_of_pos hp1']; exact entropyTerm_lt_helper p1 hp1' h1ne
      · push_neg at hp1'; have : p1 = 0 := le_antisymm hp1' hp1
        rw [this]
        unfold entropyTerm; simp
        norm_num; apply div_pos; norm_num; exact hlog2_pos
    calc entropyTerm p1 + entropyTerm p2 + entropyTerm p3
        < (p1 * log2 3 + (1/3 - p1) / Real.log 2) +
          (p2 * log2 3 + (1/3 - p2) / Real.log 2) +
          (p3 * log2 3 + (1/3 - p3) / Real.log 2) := by linarith
      _ = log2 3 := by
        simp only [hsum]; field_simp; ring
  · have h2lt : entropyTerm p2 < p2 * log2 3 + (1/3 - p2) / Real.log 2 := by
      by_cases hp2' : p2 > 0
      · rw [entropyTerm_of_pos hp2']; exact entropyTerm_lt_helper p2 hp2' h2ne
      · push_neg at hp2'; have : p2 = 0 := le_antisymm hp2' hp2
        rw [this]
        unfold entropyTerm; simp
        norm_num; apply div_pos; norm_num; exact hlog2_pos
    calc entropyTerm p1 + entropyTerm p2 + entropyTerm p3
        < (p1 * log2 3 + (1/3 - p1) / Real.log 2) +
          (p2 * log2 3 + (1/3 - p2) / Real.log 2) +
          (p3 * log2 3 + (1/3 - p3) / Real.log 2) := by linarith
      _ = log2 3 := by
        simp only [hsum]; field_simp; ring
  · have h3lt : entropyTerm p3 < p3 * log2 3 + (1/3 - p3) / Real.log 2 := by
      by_cases hp3' : p3 > 0
      · rw [entropyTerm_of_pos hp3']; exact entropyTerm_lt_helper p3 hp3' h3ne
      · push_neg at hp3'; have : p3 = 0 := le_antisymm hp3' hp3
        rw [this]
        unfold entropyTerm; simp
        norm_num; apply div_pos; norm_num; exact hlog2_pos
    calc entropyTerm p1 + entropyTerm p2 + entropyTerm p3
        < (p1 * log2 3 + (1/3 - p1) / Real.log 2) +
          (p2 * log2 3 + (1/3 - p2) / Real.log 2) +
          (p3 * log2 3 + (1/3 - p3) / Real.log 2) := by linarith
      _ = log2 3 := by
        simp only [hsum]; field_simp; ring

/-- Shannon entropy maximum characterization. -/
theorem shannon_max_uniform_iff (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 = log2 3 ↔
    p1 = 1/3 ∧ p2 = 1/3 ∧ p3 = 1/3 := by
  constructor
  · intro h
    by_contra hnot
    have hne : p1 ≠ 1/3 ∨ p2 ≠ 1/3 ∨ p3 ≠ 1/3 := by
      by_contra h_all_eq
      push_neg at h_all_eq
      exact hnot h_all_eq
    have hlt := entropyTerm_sum_lt p1 p2 p3 hp1 hp2 hp3 hsum hne
    linarith
  · intro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact uniform_achieves_max

/-! ## Bloch Entropy Bound -/

/-- L4-step4: Bloch entropy is bounded by log₂(3) -/
theorem bloch_entropy_bound (v : BlochVector) : blochEntropy v ≤ log2 3 := by
  unfold blochEntropy
  -- The squared Bloch components form a probability distribution on 3 outcomes
  have hsum : v.q 1 + v.q 2 + v.q 3 = 1 := by
    unfold BlochVector.q
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceFinMk, Fin.reduceLT, Fin.val_one, Fin.val_two]
    have := v.norm_sq
    linarith
  have h1 : v.q 1 ≥ 0 := BlochVector.q_nonneg v 1
  have h2 : v.q 2 ≥ 0 := BlochVector.q_nonneg v 2
  have h3 : v.q 3 ≥ 0 := BlochVector.q_nonneg v 3
  exact shannon_max_uniform (v.q 1) (v.q 2) (v.q 3) h1 h2 h3 hsum

/-! ## Equality Characterization -/

/-- L4-step4: Bloch entropy equals log₂(3) iff magic state -/
theorem bloch_entropy_max_iff (v : BlochVector) :
    blochEntropy v = log2 3 ↔ isMagicState v := by
  constructor
  · -- If blochEntropy = log₂(3), then v is magic state
    intro h
    unfold blochEntropy at h
    have hsum : v.q 1 + v.q 2 + v.q 3 = 1 := by
      unfold BlochVector.q
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceFinMk, Fin.reduceLT, Fin.val_one, Fin.val_two]
      have := v.norm_sq
      linarith
    have h1 : v.q 1 ≥ 0 := BlochVector.q_nonneg v 1
    have h2 : v.q 2 ≥ 0 := BlochVector.q_nonneg v 2
    have h3 : v.q 3 ≥ 0 := BlochVector.q_nonneg v 3
    have h_iff := shannon_max_uniform_iff (v.q 1) (v.q 2) (v.q 3) h1 h2 h3 hsum
    rw [h] at h_iff
    simp only [true_iff] at h_iff
    exact h_iff
  · -- If v is magic state, then blochEntropy = log₂(3)
    intro ⟨h1, h2, h3⟩
    unfold blochEntropy
    rw [h1, h2, h3]
    exact uniform_achieves_max

/-! ## Main Theorem: Maximum at Magic State -/

/-- Total entropy from L3 formula -/
noncomputable def totalEntropyL4 (bloch : Fin n → BlochVector) : ℝ :=
  totalEntropy bloch

/-- Entropy-influence ratio -/
noncomputable def entropyInfluenceRatio (bloch : Fin n → BlochVector) : ℝ :=
  totalEntropyL4 bloch / totalInfluence bloch

/-- Sum of Bloch entropies is maximized when all are at magic state -/
theorem sum_blochEntropy_max (bloch : Fin n → BlochVector) :
    ∑ k, blochEntropy (bloch k) ≤ ∑ k : Fin n, blochEntropy magicBlochVector := by
  apply Finset.sum_le_sum
  intro k _
  calc blochEntropy (bloch k) ≤ log2 3 := bloch_entropy_bound (bloch k)
    _ = blochEntropy magicBlochVector := blochEntropy_magic.symm

/-- L4-root: Maximum at Magic State

    S/I is maximized when all qubits are in the magic state.
    Since I is constant (L2), this reduces to showing S is maximized at magic state.
-/
theorem max_at_magic_state (bloch : Fin n → BlochVector)
    (hn : n ≥ 1)
    (hq_all : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch j).q ℓ > 0)
    (hp : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) → fourierWeight bloch α > 0) :
    totalEntropyL4 bloch ≤ totalEntropyL4 (fun _ : Fin n => magicBlochVector) := by
  -- By L3, totalEntropy = entropyTerm(p₀) + (2n-2)(1-p₀) + 2^{1-n} Σₖ fₖ
  -- The first two terms are independent of Bloch vectors
  -- Only Σₖ fₖ depends on Bloch vectors
  -- By bloch_entropy_bound, each fₖ ≤ log₂(3)
  -- Equality is achieved at magic state
  unfold totalEntropyL4
  -- Apply entropy_formula to both sides
  have hq_magic : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 →
      ((fun _ : Fin n => magicBlochVector) j).q ℓ > 0 := by
    intro _ ℓ hℓ
    simp only
    exact magic_q_pos ℓ hℓ
  have hp_magic : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) →
      fourierWeight (fun _ : Fin n => magicBlochVector) α > 0 := by
    intro α hα
    apply fourierWeight_pos_of_qProduct_pos
    intro k
    obtain ⟨k', hk'⟩ := hα
    by_cases hk : α k = 0
    · rw [hk, L3Entropy.BlochVector.q_zero_eq_one]; norm_num
    · exact magic_q_pos (α k) hk
  rw [entropy_formula bloch hq_all hp]
  rw [entropy_formula (fun _ : Fin n => magicBlochVector) hq_magic hp_magic]
  -- The p_zero and (2n-2)(1-p_zero) terms are the same
  -- So we need: 2^{1-n} * totalBlochEntropy bloch ≤ 2^{1-n} * totalBlochEntropy magic
  have h2pos : (2 : ℝ)^(1 - (n : ℤ)) > 0 := zpow_pos (by norm_num : (0:ℝ) < 2) _
  have hsum : totalBlochEntropy bloch ≤ totalBlochEntropy (fun _ : Fin n => magicBlochVector) := by
    unfold totalBlochEntropy
    exact sum_blochEntropy_max bloch
  have hmul : (2 : ℝ)^(1 - (n : ℤ)) * totalBlochEntropy bloch ≤
              (2 : ℝ)^(1 - (n : ℤ)) * totalBlochEntropy (fun _ : Fin n => magicBlochVector) := by
    apply mul_le_mul_of_nonneg_left hsum (le_of_lt h2pos)
  linarith

/-! ## Corollary: Explicit Maximum Formula -/

/-- L4-cor: Explicit formula for maximum ratio at magic state -/
theorem max_ratio_formula (hn : n ≥ 1) :
    totalEntropyL4 (fun _ : Fin n => magicBlochVector) =
    entropyTerm (p_zero n) + (2*(n : ℤ) - 2) * (1 - p_zero n) +
    (2 : ℝ)^(1 - (n : ℤ)) * (n : ℝ) * log2 3 := by
  unfold totalEntropyL4
  have hq_magic : ∀ j : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 →
      ((fun _ : Fin n => magicBlochVector) j).q ℓ > 0 := by
    intro _ ℓ hℓ
    simp only
    exact magic_q_pos ℓ hℓ
  have hp_magic : ∀ α : MultiIndex n, (∃ k, α k ≠ 0) →
      fourierWeight (fun _ : Fin n => magicBlochVector) α > 0 := by
    intro α hα
    apply fourierWeight_pos_of_qProduct_pos
    intro k
    obtain ⟨k', hk'⟩ := hα
    by_cases hk : α k = 0
    · rw [hk, L3Entropy.BlochVector.q_zero_eq_one]; norm_num
    · exact magic_q_pos (α k) hk
  rw [entropy_formula (fun _ : Fin n => magicBlochVector) hq_magic hp_magic]
  congr 1
  unfold totalBlochEntropy
  simp only [blochEntropy_magic, Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul]
  ring

end Alethfeld.QBF.Rank1.L4Maximum