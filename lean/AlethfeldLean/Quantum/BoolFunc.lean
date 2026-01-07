/-
  AlethfeldLean.Quantum.BoolFunc

  Boolean function definitions and Fourier analysis on {±1}^n.

  This module defines:
  - Boolean functions f : {0,1}^n → {±1}
  - Parity/character functions χ_S
  - Fourier coefficients and entropy
  - Character orthogonality relations
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Alethfeld.Quantum.BoolFunc

open scoped BigOperators
open Finset Real

/-! ## Basic Definitions -/

/-- testBit in terms of div/mod -/
lemma testBit_eq_div_mod {x i : ℕ} : x.testBit i = decide (x / 2^i % 2 = 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hmod : x / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by omega)
  cases hv : x / 2 ^ i % 2 with
  | zero => simp
  | succ m =>
    have hm1 : m + 1 < 2 := by rw [← hv]; exact hmod
    have hm0 : m = 0 := Nat.lt_one_iff.mp (by omega : m < 1)
    subst hm0
    simp

/-- Equivalence between (Fin n → Bool) and Fin (2^n) via testBit -/
def boolFuncEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- boolFuncEquiv.symm corresponds to testBit -/
lemma boolFuncEquiv_symm_apply {n : ℕ} (x : Fin (2^n)) (i : Fin n) :
    (boolFuncEquiv n).symm x i = x.val.testBit i.val := by
  simp only [boolFuncEquiv, Equiv.symm_trans_apply, Equiv.piCongrRight_symm_apply]
  have h := finFunctionFinEquiv_symm_apply_val x i
  rw [testBit_eq_div_mod]
  change finTwoEquiv (finFunctionFinEquiv.symm x i) = decide (x.val / 2^i.val % 2 = 1)
  rw [show finTwoEquiv (finFunctionFinEquiv.symm x i) =
      ((finFunctionFinEquiv.symm x i) == 1) from rfl]
  have hmod2 : x.val / 2 ^ i.val % 2 < 2 := Nat.mod_lt _ (by omega)
  cases hv : x.val / 2 ^ i.val % 2 with
  | zero =>
    have : finFunctionFinEquiv.symm x i = ⟨0, by omega⟩ := by ext; rw [h, hv]
    simp [this]
  | succ m =>
    have hm1 : m + 1 < 2 := by rw [← hv]; exact hmod2
    have hm0 : m = 0 := Nat.lt_one_iff.mp (by omega : m < 1)
    subst hm0
    have : finFunctionFinEquiv.symm x i = 1 := by ext; rw [h, hv]; rfl
    simp [this]

/-- Boolean function type: {0,1}^n → {+1,-1} -/
def BoolFunc (n : ℕ) := (Fin n → Bool) → ℤ

/-- The parity function χ_S(x) = (-1)^(Σ_{i∈S} x_i) -/
def parityFunc {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  if (S.filter (fun i => x i)).card % 2 = 0 then 1 else -1

/-- Fourier coefficient of f at S -/
noncomputable def fourierCoeff {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) : ℝ :=
  (1 / 2^n : ℝ) * ∑ x : (Fin n → Bool), (f x : ℝ) * parityFunc S x

/-- Classical Fourier entropy -/
noncomputable def fourierEntropy {n : ℕ} (f : BoolFunc n) : ℝ :=
  - ∑ S : Finset (Fin n),
    let c := (fourierCoeff f S)^2
    if c = 0 then 0 else c * Real.log c / Real.log 2

/-- Classical total influence -/
noncomputable def totalInfluence {n : ℕ} (f : BoolFunc n) : ℝ :=
  ∑ S : Finset (Fin n), S.card * (fourierCoeff f S)^2

/-! ## Character Orthogonality -/

/-- Parity function squared is 1 -/
lemma parityFunc_sq {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    (parityFunc S x : ℂ) * (parityFunc S x : ℂ) = 1 := by
  unfold parityFunc
  split_ifs <;> simp

/-- Product of parity functions equals parity of symmetric difference -/
lemma parityFunc_mul {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    (parityFunc S x : ℤ) * (parityFunc T x : ℤ) = parityFunc (symmDiff S T) x := by
  unfold parityFunc
  -- The key: (-1)^a * (-1)^b = (-1)^(a+b), and parity of symmDiff relates to sum
  let a := (S.filter (fun i => x i)).card
  let b := (T.filter (fun i => x i)).card
  let c := ((symmDiff S T).filter (fun i => x i)).card
  -- The symmDiff formula on filtered sets: symmDiff preserves parity
  have h_eq : (symmDiff S T).filter (fun i => x i) =
      symmDiff (S.filter (fun i => x i)) (T.filter (fun i => x i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  have h_card : c = (symmDiff (S.filter fun i => x i) (T.filter fun i => x i)).card := by
    simp only [c, h_eq]
  -- Key: symmDiff A B = (A ∪ B) \ (A ∩ B), so |symmDiff A B| ≡ |A| + |B| (mod 2)
  have h_parity : c % 2 = (a + b) % 2 := by
    rw [h_card]
    let A := S.filter fun i => x i
    let B := T.filter fun i => x i
    -- Use card_sdiff and card_union lemmas
    have h_sd_eq : symmDiff A B = (A ∪ B) \ (A ∩ B) := by
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      tauto
    rw [h_sd_eq]
    -- card_sdiff: #(t \ s) = #t - #(s ∩ t)
    -- Here t = A ∪ B, s = A ∩ B, so #(t \ s) = #(A ∪ B) - #((A ∩ B) ∩ (A ∪ B))
    -- And (A ∩ B) ∩ (A ∪ B) = A ∩ B, so #(t \ s) = #(A ∪ B) - #(A ∩ B)
    have h_inter_eq : (A ∩ B) ∩ (A ∪ B) = A ∩ B := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [Finset.card_sdiff, h_inter_eq]
    have h_incl_excl : (A ∪ B).card + (A ∩ B).card = A.card + B.card := by
      have := Finset.card_union_add_card_inter A B
      omega
    have h_a_eq : A.card = a := rfl
    have h_b_eq : B.card = b := rfl
    rw [h_a_eq, h_b_eq] at h_incl_excl
    -- #(A∪B) - #(A∩B) ≡ #(A∪B) + #(A∩B) ≡ a + b (mod 2)
    -- because subtracting is the same as adding mod 2
    have h_mod2 : ((A ∪ B).card - (A ∩ B).card) % 2 = ((A ∪ B).card + (A ∩ B).card) % 2 := by
      have h_diff : (A ∪ B).card ≥ (A ∩ B).card := Finset.card_le_card Finset.inter_subset_union
      omega
    rw [h_mod2, h_incl_excl]
  -- Now case split on parities
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all <;> omega

/-- Character completeness: Σ_S χ_S(x) * χ_S(y) = 2^n if x = y, else 0

This is the orthogonality relation for characters of (ℤ/2)^n.
For x = y: each term is χ_S(x)² = 1, so sum = 2^n (number of subsets).
For x ≠ y: pair S with S∆{i} where i is a differing position; terms cancel.
-/
lemma character_completeness {n : ℕ} (x y : Fin n → Bool) :
    (∑ S : Finset (Fin n), (parityFunc S x : ℂ) * (parityFunc S y : ℂ)) =
      if x = y then (2 : ℂ)^n else 0 := by
  split_ifs with hxy
  · -- x = y case: each term is χ_S(x)² = 1
    subst hxy
    conv_lhs => arg 2; ext S; rw [parityFunc_sq]
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul, mul_one]
    have hcard : Fintype.card (Finset (Fin n)) = 2^n := by
      rw [Fintype.card_finset, Fintype.card_fin]
    simp only [hcard]
    norm_cast
  · -- x ≠ y case: use involution pairing
    -- Find a position i where x and y differ
    have hdiff : ∃ i : Fin n, x i ≠ y i := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hdiff
    -- Define the involution φ(S) = S ∆ {i}
    let φ : Finset (Fin n) → Finset (Fin n) := fun S => symmDiff S {i}
    -- Use parityFunc_mul to show χ_{S∆{i}}(z) = χ_S(z) * χ_{{i}}(z)
    have parity_symmDiff : ∀ (S : Finset (Fin n)) (z : Fin n → Bool),
        (parityFunc (symmDiff S {i}) z : ℂ) =
          (parityFunc S z : ℂ) * (parityFunc {i} z : ℂ) := by
      intro S z
      -- Use the multiplication property: χ_S(z) * χ_T(z) = χ_{S∆T}(z)
      have h := parityFunc_mul S {i} z
      -- h : parityFunc S z * parityFunc {i} z = parityFunc (symmDiff S {i}) z
      exact_mod_cast h.symm
    -- Apply sum_involution
    apply Finset.sum_involution (g := fun S _ => φ S)
    · -- f(S) + f(φ S) = 0: opposite signs due to x i ≠ y i
      intro S _
      simp only [φ]
      rw [parity_symmDiff S x, parity_symmDiff S y]
      -- Since x i ≠ y i, exactly one has χ_{{i}}(z) = -1
      unfold parityFunc
      simp only [Finset.filter_singleton]
      -- x i ≠ y i, so exactly one of them is true
      cases hxi : x i <;> cases hyi : y i
      · -- x i = false, y i = false: contradicts hi
        exfalso; exact hi (hxi.trans hyi.symm)
      · -- x i = false, y i = true
        -- parityFunc {i} x = 1 (since x i = false, filter is ∅)
        -- parityFunc {i} y = -1 (since y i = true, filter is {i})
        -- Goal: a * b + a * χ(x i) * (b * χ(y i)) = 0 where χ(false)=1, χ(true)=-1
        -- Reduce `if false = true then ... else ...` and `if 1 = 0 then ... else ...`
        have hf : (false : Bool) = true ↔ False := by decide
        have ho : (1 : ℕ) = 0 ↔ False := by decide
        simp only [hf, ↓reduceIte, Finset.card_empty, Nat.zero_mod, ho, Finset.card_singleton]
        -- Now: a * b + a * 1 * (b * -1) = 0
        ring
      · -- x i = true, y i = false
        have hf : (false : Bool) = true ↔ False := by decide
        have ho : (1 : ℕ) = 0 ↔ False := by decide
        simp only [hf, ↓reduceIte, Finset.card_empty, Nat.zero_mod, ho, Finset.card_singleton]
        ring
      · -- x i = true, y i = true: contradicts hi
        exfalso; exact hi (hxi.trans hyi.symm)
    · -- hg₃: f a ≠ 0 → g a ≠ a (no fixed points for nonzero terms)
      intro S _ _
      simp only [φ, ne_eq]
      intro h
      have hmem : i ∈ symmDiff S ({i} : Finset (Fin n)) ↔ i ∈ S := by rw [h]
      simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hmem
      tauto
    · -- g_mem: φ S ∈ univ
      intro S _
      exact Finset.mem_univ _
    · -- hg₄: φ (φ S) = S (involution)
      intro S _
      simp only [φ, symmDiff_symmDiff_cancel_right]

/-- Fourier inversion formula: f(x) = Σ_S f̂(S) χ_S(x)

This is the standard Fourier inversion on {±1}^n. The proof uses character orthogonality:
Σ_S χ_S(x) χ_S(y) = 2^n δ_{x,y}. -/
lemma fourier_inversion {n : ℕ} (f : BoolFunc n) (x : Fin n → Bool) :
    (f x : ℂ) = ∑ S : Finset (Fin n), (fourierCoeff f S : ℂ) * (parityFunc S x : ℂ) := by
  -- Expand fourierCoeff definition
  simp only [fourierCoeff]
  -- Convert to complex and reorganize
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_intCast]
  -- Reorganize the sum for applying sum_comm
  -- Transform: Σ_S (1/2^n * Σ_y f(y)χ_S(y)) * χ_S(x)
  -- = 1/2^n * Σ_S (Σ_y f(y)χ_S(y)) * χ_S(x)
  -- = 1/2^n * Σ_S Σ_y f(y)χ_S(y)χ_S(x)
  -- = 1/2^n * Σ_y f(y) * Σ_S χ_S(y)χ_S(x)
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  -- The inner sum is now Σ_S χ_S(y) χ_S(x) = 2^n δ_{y,x}
  -- Factor out f(y): Σ_i f(y) * (χ_i(y) * χ_i(x)) = f(y) * Σ_i χ_i(y) * χ_i(x)
  conv_rhs =>
    arg 2
    ext y
    rw [← Finset.mul_sum]
    arg 2
    rw [← Finset.mul_sum]
    arg 2
    rw [show ∑ S : Finset (Fin n), (parityFunc S y : ℂ) * (parityFunc S x : ℂ) =
        if y = x then (2 : ℂ)^n else 0 from character_completeness y x]
  -- Only y = x term survives
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  -- f(x) * 2^n / 2^n = f(x)
  have h2n_ne : (2 : ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)
  field_simp
  norm_cast
  ring

end Alethfeld.Quantum.BoolFunc
