/-
  AlethfeldLean.QBF.Rank1.L2Influence

  Lemma L2: Influence Independence for Rank-1 Product State QBFs

  Alethfeld Verified Proof
  Status: VERIFIED | Taint: CLEAN

  Key Result: For any rank-1 product state QBF on n qubits,
    I(U) = n * 2^{1-n}
  This is INDEPENDENT of the choice of Bloch vectors.
-/
import AlethfeldLean.QBF.Rank1.L1Fourier

namespace Alethfeld.QBF.Rank1.L2Influence

open scoped Matrix ComplexConjugate BigOperators
open Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch Alethfeld.QBF.Rank1

variable {n : ℕ}

/-! ## Probability Distribution (from L1 Corollary)

For α ≠ 0: p_α = |Û(α)|² = 2^{2-2n} ∏_k q_k^{α_k}
-/

/-- Product of squared Bloch components -/
noncomputable def qProduct (bloch : Fin n → BlochVector) (α : MultiIndex n) : ℝ :=
  ∏ k, (bloch k).q (α k)

/-- Probability (Fourier weight) for multi-index α ≠ 0 -/
noncomputable def probability (bloch : Fin n → BlochVector) (α : MultiIndex n) : ℝ :=
  (2 : ℝ)^(2 - 2*(n : ℤ)) * qProduct bloch α

/-! ## Influence Definitions -/

/-- Influence of qubit j: sum of p_α over all α with α_j ≠ 0 -/
noncomputable def influence_j (bloch : Fin n → BlochVector) (j : Fin n) : ℝ :=
  ∑ α : MultiIndex n, if α j ≠ 0 then probability bloch α else 0

/-- Total influence: sum over all qubits -/
noncomputable def totalInfluence (bloch : Fin n → BlochVector) : ℝ :=
  ∑ j, influence_j bloch j

/-! ## Core Lemmas -/

/-- Sum of q components using Finset.sum -/
theorem BlochVector.q_finset_sum (v : BlochVector) :
    ∑ m : Fin 4, v.q m = 2 := by
  simp only [Fin.sum_univ_four]
  exact v.q_sum_eq_two

/-- Product excluding one index equals product over all divided by that term -/
theorem qProduct_split (bloch : Fin n → BlochVector) (j : Fin n) (α : MultiIndex n) :
    qProduct bloch α = (bloch j).q (α j) * ∏ k : {k : Fin n // k ≠ j}, (bloch k.val).q (α k.val) := by
  unfold qProduct
  rw [← Finset.prod_erase_mul (Finset.univ) (fun k => (bloch k).q (α k)) (Finset.mem_univ j)]
  rw [mul_comm]
  congr 1
  apply Finset.prod_subtype
  intro k
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]

/-- Cardinality of complement: |{k : Fin n // k ≠ j}| = n - 1 (L2-S2a) -/
theorem card_complement_singleton {n : ℕ} (j : Fin n) :
    Fintype.card {k : Fin n // k ≠ j} = n - 1 := by
  have equiv : {k : Fin n // k ≠ j} ≃ {k : Fin n // k ∈ Finset.univ.erase j} :=
    Equiv.subtypeEquivRight (fun k => by simp)
  rw [Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter,
             Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp only [Finset.card_fin]

/-- Product of constant 2 over a type equals 2^|type| (L2-S2b) -/
theorem prod_const_two {α : Type*} [Fintype α] :
    ∏ _ : α, (2 : ℝ) = 2 ^ Fintype.card α := by
  simp only [Finset.prod_const, Finset.card_univ]

/-- Exponent arithmetic: 2^{2-2n} * 2^{n-1} = 2^{1-n} (L2-S2c) -/
theorem exponent_simplify {n : ℕ} :
    (2 : ℝ)^(2 - 2*(n : ℤ)) * (2 : ℝ)^((n : ℤ) - 1) = (2 : ℝ)^(1 - (n : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

/-! ## Track 1 Helper Lemmas (L2-S1a, S1b, S1c) -/

/-- Extension function: extend β with value ℓ at position j -/
def extendAt (j : Fin n) (ℓ : Fin 4) (β : {k : Fin n // k ≠ j} → Fin 4) : MultiIndex n :=
  fun k => if h : k = j then ℓ else β ⟨k, h⟩

/-- Restriction function: restrict α to indices ≠ j -/
def restrictAt (j : Fin n) (α : MultiIndex n) : {k : Fin n // k ≠ j} → Fin 4 :=
  fun ⟨k, _⟩ => α k

/-- extendAt and restrictAt are inverse when α j = ℓ -/
theorem extendAt_restrictAt (j : Fin n) (ℓ : Fin 4) (α : MultiIndex n) (hα : α j = ℓ) :
    extendAt j ℓ (restrictAt j α) = α := by
  ext k
  simp only [extendAt, restrictAt]
  split_ifs with h
  · rw [h, hα]
  · rfl

/-- restrictAt extendAt is identity -/
theorem restrictAt_extendAt (j : Fin n) (ℓ : Fin 4) (β : {k : Fin n // k ≠ j} → Fin 4) :
    restrictAt j (extendAt j ℓ β) = β := by
  ext ⟨k, hk⟩
  simp only [restrictAt, extendAt, dif_neg hk]

/-- S1a: MultiIndex decomposition - reindex sum by fixing α_j = ℓ -/
theorem multiIndex_decompose (j : Fin n) (ℓ : Fin 4) (f : MultiIndex n → ℝ) :
    ∑ α : MultiIndex n, (if α j = ℓ then f α else 0) =
    ∑ β : ({k : Fin n // k ≠ j} → Fin 4), f (extendAt j ℓ β) := by
  -- The equivalence between {α | α j = ℓ} and ({k // k ≠ j} → Fin 4)
  let equiv : {α : MultiIndex n // α j = ℓ} ≃ ({k : Fin n // k ≠ j} → Fin 4) := {
    toFun := fun ⟨α, _⟩ => restrictAt j α
    invFun := fun β => ⟨extendAt j ℓ β, by simp [extendAt]⟩
    left_inv := fun ⟨α, hα⟩ => by
      simp only [Subtype.mk.injEq]
      exact extendAt_restrictAt j ℓ α hα
    right_inv := fun β => restrictAt_extendAt j ℓ β
  }
  -- Split sum by condition: ∑ (if cond then f else 0) = ∑_{cond} f
  have step1 : ∑ α : MultiIndex n, (if α j = ℓ then f α else 0) =
               ∑ α ∈ Finset.filter (fun α => α j = ℓ) Finset.univ, f α := by
    rw [Finset.sum_filter]
  -- Convert filtered sum to subtype sum
  have step2 : ∑ α ∈ Finset.filter (fun α => α j = ℓ) Finset.univ, f α =
               ∑ α : {α : MultiIndex n // α j = ℓ}, f α.val := by
    rw [← Finset.sum_subtype]
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Use equivalence to reindex to β
  have step3 : ∑ α : {α : MultiIndex n // α j = ℓ}, f α.val =
               ∑ β : ({k : Fin n // k ≠ j} → Fin 4), f (extendAt j ℓ β) := by
    rw [Fintype.sum_equiv equiv
      (f := fun (a : {α : MultiIndex n // α j = ℓ}) => f a.val)
      (g := fun β => f (extendAt j ℓ β))]
    intro ⟨α, hα⟩
    simp only [equiv, Equiv.coe_fn_mk, restrictAt, extendAt_restrictAt j ℓ α hα]
  rw [step1, step2, step3]

/-- S1b: Product factorization when α_j is fixed -/
theorem qProduct_factor_fixed_j (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4)
    (β : {k : Fin n // k ≠ j} → Fin 4) :
    qProduct bloch (extendAt j ℓ β) =
    (bloch j).q ℓ * ∏ k : {k : Fin n // k ≠ j}, (bloch k.val).q (β k) := by
  unfold qProduct extendAt
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)]
  rw [mul_comm]
  congr 1
  · -- Show the j-th factor is (bloch j).q ℓ
    simp only [↓reduceDIte]
  · -- Show remaining factors match β
    rw [Finset.prod_subtype (Finset.univ.erase j) (p := fun k => k ≠ j)]
    · apply Finset.prod_congr rfl
      intro ⟨k, hk⟩ _
      simp only [dif_neg hk]
    · intro k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]

/-- S1c: Sum-product interchange (Fubini for finite sums) -/
theorem sum_prod_factor (bloch : Fin n → BlochVector) (j : Fin n) :
    ∑ β : ({k : Fin n // k ≠ j} → Fin 4), ∏ k : {k : Fin n // k ≠ j}, (bloch k.val).q (β k) =
    ∏ k : {k : Fin n // k ≠ j}, ∑ m : Fin 4, (bloch k.val).q m := by
  -- This is the finite Fubini theorem: ∑_f ∏_i f(i) = ∏_i ∑_x x
  rw [Fintype.prod_sum]

/-! ## Factorization Lemma (L2-08)

When α_j = ℓ is fixed and ℓ ≠ 0, the sum over α factors.
-/

/-- Partial sum: sum over all α with α_j = ℓ -/
noncomputable def partialSum (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) : ℝ :=
  ∑ α : MultiIndex n, if α j = ℓ then probability bloch α else 0

/-- Sum over all q values equals 2 -/
theorem sum_q_eq_two (v : BlochVector) : ∑ m : Fin 4, v.q m = 2 :=
  BlochVector.q_finset_sum v

/-- Factorization: ∑_{α : α_j = ℓ} p_α = 2^{2-2n} * q_j^ℓ * ∏_{k≠j} (∑_m q_k^m) -/
theorem factorization_lemma (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) :
    partialSum bloch j ℓ =
    (2 : ℝ)^(2 - 2*(n : ℤ)) * (bloch j).q ℓ *
      ∏ k : {k : Fin n // k ≠ j}, ∑ m : Fin 4, (bloch k.val).q m := by
  unfold partialSum probability
  -- Step 1: Use multiIndex_decompose to reindex the sum
  rw [multiIndex_decompose j ℓ (fun α => (2 : ℝ)^(2 - 2*(n : ℤ)) * qProduct bloch α)]
  -- Step 2: Factor out constant and use qProduct_factor_fixed_j
  simp only [qProduct_factor_fixed_j]
  -- Step 3: Rearrange: ∑ (a * (b * c)) = a * b * ∑ c
  have h1 : ∀ β : ({k : Fin n // k ≠ j} → Fin 4),
      (2 : ℝ)^(2 - 2*(n : ℤ)) * ((bloch j).q ℓ * ∏ k, (bloch k.val).q (β k)) =
      (2 : ℝ)^(2 - 2*(n : ℤ)) * (bloch j).q ℓ * ∏ k, (bloch k.val).q (β k) := by
    intro β
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum]
  congr 1
  -- Step 4: Apply sum_prod_factor (Fubini)
  exact sum_prod_factor bloch j

/-! ## Simplification Using q_sum = 2 (L2-09)

Each factor ∑_m q_k^m = 2, so the product gives 2^{n-1}
-/

theorem partial_sum_simplified (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    partialSum bloch j ℓ = (2 : ℝ)^(1 - (n : ℤ)) * (bloch j).q ℓ := by
  -- Step 1: Apply factorization_lemma
  rw [factorization_lemma]
  -- Step 2: Replace each ∑_m q_k^m with 2
  have h_sum : ∀ k : {k : Fin n // k ≠ j}, ∑ m : Fin 4, (bloch k.val).q m = 2 := by
    intro k
    exact sum_q_eq_two (bloch k.val)
  simp only [h_sum]
  -- Step 3: Product of constant 2 is 2^{n-1}
  rw [prod_const_two, card_complement_singleton]
  -- Step 4: Simplify exponents: 2^{2-2n} * q * 2^{n-1} = 2^{1-n} * q
  -- Goal: 2 ^ (2 - 2 * ↑n) * (bloch j).q ℓ * 2 ^ (n - 1) = 2 ^ (1 - ↑n) * (bloch j).q ℓ
  -- Rearrange: (a * b) * c = (a * c) * b
  rw [mul_assoc, mul_comm ((bloch j).q ℓ) ((2 : ℝ)^(n - 1 : ℕ)), ← mul_assoc]
  congr 1
  -- Now need: 2^{2-2n} * 2^{n-1 : ℕ} = 2^{1-n}
  -- Convert 2^{n-1 : ℕ} to 2^{(n : ℤ) - 1}
  have hn : n ≥ 1 := Fin.pos j
  have hconv : ((2 : ℝ)^(n - 1 : ℕ) : ℝ) = (2 : ℝ)^((n : ℤ) - 1) := by
    rw [← zpow_natCast]
    congr 1
    omega
  rw [hconv]
  exact exponent_simplify

/-! ## Single-Qubit Influence Formula (L2-10)

I_j = ∑_{ℓ ≠ 0} partialSum_ℓ = 2^{1-n} * ∑_{ℓ ≠ 0} q_j^ℓ = 2^{1-n} * 1 = 2^{1-n}
-/

/-- Influence_j equals sum of partialSums over nonzero ℓ (L2-S3a) -/
theorem influence_j_eq_sum_partialSum (bloch : Fin n → BlochVector) (j : Fin n) :
    influence_j bloch j = ∑ ℓ : Fin 4, if ℓ ≠ 0 then partialSum bloch j ℓ else 0 := by
  unfold influence_j partialSum
  simp only [Fin.sum_univ_four, ne_eq, Fin.isValue, Fin.reduceEq, not_true_eq_false, ↓reduceIte,
    not_false_eq_true, zero_add]
  -- Partition the sum over α by value of α j
  have partition : ∀ α : MultiIndex n,
      (if α j ≠ 0 then probability bloch α else 0) =
      (if α j = 1 then probability bloch α else 0) +
      (if α j = 2 then probability bloch α else 0) +
      (if α j = 3 then probability bloch α else 0) := by
    intro α
    rcases Fin.eq_zero_or_eq_succ (α j) with h0 | ⟨k, hk⟩
    · simp [h0]
    · rcases Fin.eq_zero_or_eq_succ k with hk0 | ⟨k', hk'⟩
      · simp [hk, hk0]
      · rcases Fin.eq_zero_or_eq_succ k' with hk'0 | ⟨k'', hk''⟩
        · simp [hk, hk', hk'0]
        · have : k'' = 0 := Fin.eq_zero k''
          simp [hk, hk', hk'', this]
  simp_rw [partition]
  simp only [Finset.sum_add_distrib]

/-- Factor out constant from conditional sum (L2-S3b) -/
theorem factor_out_power (bloch : Fin n → BlochVector) (j : Fin n) :
    ∑ ℓ : Fin 4, (if ℓ ≠ 0 then (2 : ℝ)^(1 - (n : ℤ)) * (bloch j).q ℓ else 0) =
    (2 : ℝ)^(1 - (n : ℤ)) * ∑ ℓ : Fin 4, (if ℓ ≠ 0 then (bloch j).q ℓ else 0) := by
  rw [Finset.mul_sum]
  congr 1
  ext ℓ
  split_ifs <;> ring

/-- Sum over nonzero Fin 4 elements -/
theorem sum_nonzero_fin4 (f : Fin 4 → ℝ) :
    ∑ m : Fin 4, (if m ≠ 0 then f m else 0) = f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_four, Fin.isValue, ne_eq, Fin.reduceEq, not_true_eq_false,
    ↓reduceIte, not_false_eq_true]
  ring

/-- Single-qubit influence is constant: I_j = 2^{1-n} -/
theorem influence_j_formula (bloch : Fin n → BlochVector) (j : Fin n) :
    influence_j bloch j = (2 : ℝ)^(1 - (n : ℤ)) := by
  -- Step 1: Rewrite as sum of partialSums
  rw [influence_j_eq_sum_partialSum]
  -- Step 2: Apply partial_sum_simplified to each nonzero term
  have h_simp : ∀ ℓ : Fin 4, ℓ ≠ 0 →
      partialSum bloch j ℓ = (2 : ℝ)^(1 - (n : ℤ)) * (bloch j).q ℓ :=
    fun ℓ hℓ => partial_sum_simplified bloch j ℓ hℓ
  conv_lhs =>
    arg 2
    ext ℓ
    rw [show (if ℓ ≠ 0 then partialSum bloch j ℓ else 0) =
            (if ℓ ≠ 0 then (2 : ℝ)^(1 - (n : ℤ)) * (bloch j).q ℓ else 0) by
      split_ifs with h
      · exact h_simp ℓ h
      · rfl]
  -- Step 3: Factor out the constant
  rw [factor_out_power]
  -- Step 4: Sum of nonzero q's equals 1
  rw [sum_nonzero_fin4]
  rw [BlochVector.q_nonzero_sum_eq_one]
  ring

/-! ## Main Theorem: Influence Independence (L2-11) -/

/-- Total influence formula: I(U) = n * 2^{1-n}

This is INDEPENDENT of the choice of Bloch vectors.
-/
theorem total_influence_formula (bloch : Fin n → BlochVector) :
    totalInfluence bloch = n * (2 : ℝ)^(1 - (n : ℤ)) := by
  unfold totalInfluence
  simp only [influence_j_formula]
  simp only [Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul]

/-! ## Corollaries -/

/-- Universality: influence is independent of Bloch vectors (L2-12) -/
theorem influence_independent_of_bloch (bloch₁ bloch₂ : Fin n → BlochVector) :
    totalInfluence bloch₁ = totalInfluence bloch₂ := by
  rw [total_influence_formula, total_influence_formula]

/-- Influence is positive for n ≥ 1 -/
theorem influence_pos (bloch : Fin n → BlochVector) (hn : n ≥ 1) :
    totalInfluence bloch > 0 := by
  rw [total_influence_formula]
  apply mul_pos
  · exact Nat.cast_pos.mpr hn
  · exact zpow_pos (by norm_num : (0 : ℝ) < 2) _

/-- Natural number inequality: n ≤ 2^{n-1} for n ≥ 1 (L2-S4a) -/
theorem nat_le_pow_two_sub_one (n : ℕ) (hn : n ≥ 1) : n ≤ 2^(n-1) := by
  match n with
  | 0 => omega
  | 1 => simp
  | k + 2 =>
    have hk : k + 1 ≥ 1 := by omega
    have ih := nat_le_pow_two_sub_one (k + 1) hk
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc k + 2 = (k + 1) + 1 := by ring
      _ ≤ 2^k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2^k + 2^k := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2^(k + 1) := by omega

/-- Real inequality: n * 2^{1-n} ≤ 1 for n ≥ 1 (L2-S4b) -/
theorem influence_bound_real {n : ℕ} (hn : n ≥ 1) :
    (n : ℝ) * (2 : ℝ)^(1 - (n : ℤ)) ≤ 1 := by
  have h := nat_le_pow_two_sub_one n hn
  have key : (1 : ℤ) - (n : ℤ) = -(((n - 1) : ℕ) : ℤ) := by omega
  rw [key, zpow_neg, zpow_natCast]
  have hpow_pos : (0 : ℝ) < (2 : ℝ)^(n - 1) := by positivity
  rw [← div_eq_mul_inv, div_le_one hpow_pos]
  calc (n : ℝ) ≤ ((2^(n-1) : ℕ) : ℝ) := Nat.cast_le.mpr h
    _ = (2 : ℝ)^(n-1) := by norm_cast

/-- Influence decreases exponentially with n (L2-S4c) -/
theorem influence_decreasing (bloch : Fin n → BlochVector) (hn : n ≥ 1) :
    totalInfluence bloch ≤ 1 := by
  rw [total_influence_formula]
  exact influence_bound_real hn

end Alethfeld.QBF.Rank1.L2Influence
