/-
  AlethfeldLean.Quantum.ZIndexEquiv

  Z-index equivalence and entropy/influence theorems for diagonal observables.

  This module defines:
  - toZIndex/fromZIndex: bijection between Finset (Fin n) and Z-type indices
  - zIndexEquiv: the formal equivalence
  - Theorems relating spectral entropy/influence to Fourier entropy/influence
-/
import AlethfeldLean.Quantum.SpectralDist

namespace Alethfeld.Quantum.ZIndexEquiv

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.PauliDiag
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.SpectralDist
open Alethfeld.Quantum.TExpansion

/-! ## Z-Index Conversion Functions -/

/-- Helper: Function to convert Finset to Z_S index -/
def toZIndex {n : ℕ} (S : Finset (Fin n)) : Fin n → Fin 4 :=
  fun i => if i ∈ S then 3 else 0

/-- The inverse of toZIndex: extract the set of positions where α i = 3 -/
def fromZIndex {n : ℕ} (α : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.filter (fun i => α i = 3) Finset.univ

/-! ## Z-Index Properties -/

/-- Helper: Z_S index is not in the "has X or Y" set -/
lemma toZIndex_not_XY {n : ℕ} (S : Finset (Fin n)) :
    ¬∃ i, (toZIndex S) i ∈ ({1, 2} : Finset (Fin 4)) := by
  push_neg
  intro i
  unfold toZIndex
  split_ifs <;> simp

/-- toZIndex and fromZIndex are inverses (on the Z-type domain) -/
lemma fromZIndex_toZIndex {n : ℕ} (S : Finset (Fin n)) :
    fromZIndex (toZIndex S) = S := by
  ext i
  simp only [fromZIndex, Finset.mem_filter, Finset.mem_univ, true_and, toZIndex]
  split_ifs with h <;> simp [h]

/-- toZIndex and fromZIndex are inverses (on the Z-type domain) -/
lemma toZIndex_fromZIndex {n : ℕ} (α : Fin n → Fin 4)
    (hα : ¬∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) :
    toZIndex (fromZIndex α) = α := by
  push_neg at hα
  ext i
  simp only [toZIndex, fromZIndex, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : α i = 3
  · simp [h]
  · have hi := hα i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    push_neg at hi
    have hbound : (α i).val < 4 := (α i).isLt
    interval_cases hv : (α i).val
    · simp [h, Fin.ext_iff, hv]  -- case 0
    · exfalso; apply hi.1; exact Fin.ext hv  -- case 1
    · exfalso; apply hi.2; exact Fin.ext hv  -- case 2
    · exfalso; apply h; exact Fin.ext hv  -- case 3

/-- Z-type indices are equivalent to Finset (Fin n) -/
def zIndexEquiv (n : ℕ) : {α : Fin n → Fin 4 // ¬∃ i, α i ∈ ({1, 2} : Finset (Fin 4))} ≃ Finset (Fin n) where
  toFun := fun ⟨α, _⟩ => fromZIndex α
  invFun := fun S => ⟨toZIndex S, toZIndex_not_XY S⟩
  left_inv := fun ⟨α, hα⟩ => by simp only [Subtype.mk.injEq]; exact toZIndex_fromZIndex α hα
  right_inv := fun S => fromZIndex_toZIndex S

/-! ## Spectral Distribution for Z-type Indices -/

/-- Helper: spectralDist of diagonalObs at Z_S index equals Fourier coefficient squared -/
lemma spectralDist_diagonalObs_Z_S {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) :
    spectralDist (diagonalObs f) (toZIndex S) = (fourierCoeff f S)^2 := by
  unfold spectralDist toZIndex
  rw [pauliCoeff_diagonalObs_Z_S]
  -- |fourierCoeff f S|² = (fourierCoeff f S)² since it's real
  rw [Complex.normSq_ofReal]
  ring

/-- Helper: spectralDist of diagonalObs is zero for non-Z_S indices -/
lemma spectralDist_diagonalObs_nonZ {n : ℕ} (f : BoolFunc n) (α : Fin n → Fin 4)
    (hα : ∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) :
    spectralDist (diagonalObs f) α = 0 := by
  unfold spectralDist
  rw [pauliCoeff_diagonalObs_nonZ f α hα]
  simp only [map_zero]

/-! ## Pauli Weight of Z-type Indices -/

/-- Helper: pauliWeight of Z_S index equals |S| -/
lemma pauliWeight_toZIndex {n : ℕ} (S : Finset (Fin n)) :
    pauliWeight (toZIndex S) = S.card := by
  unfold pauliWeight toZIndex
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp [h]

/-! ## Main Theorems -/

/-- Diagonal observable's spectral entropy equals Fourier entropy -/
theorem diagonalObs_spectralEntropy_eq {n : ℕ} (f : BoolFunc n) :
    spectralEntropy (diagonalObs f) = fourierEntropy f := by
  -- The spectral distribution of diagonalObs f is supported only on Z_S terms
  -- We need to show the sum over (Fin n → Fin 4) equals the sum over Finset (Fin n)
  unfold spectralEntropy fourierEntropy
  congr 1
  -- Split the sum: terms with X/Y components are zero
  -- First, partition (Fin n → Fin 4) into "Z-type" (only 0,3) and "XY-type" (has 1 or 2)
  have h_partition : ∀ α : Fin n → Fin 4,
      (∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) ∨ (∀ i, α i = 0 ∨ α i = 3) := by
    intro α
    by_cases h : ∃ i, α i ∈ ({1, 2} : Finset (Fin 4))
    · left; exact h
    · right
      push_neg at h
      intro i
      have hi := h i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      push_neg at hi
      have hbound : (α i).val < 4 := (α i).isLt
      interval_cases hv : (α i).val
      · left; exact Fin.ext hv  -- case 0
      · exfalso; apply hi.1; exact Fin.ext hv  -- case 1
      · exfalso; apply hi.2; exact Fin.ext hv  -- case 2
      · right; exact Fin.ext hv  -- case 3
  -- The sum over XY-type is zero
  have h_XY_zero : ∀ α : Fin n → Fin 4, (∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) →
      (let prob := spectralDist (diagonalObs f) α
       if prob = 0 then (0 : ℝ) else prob * Real.log prob / Real.log 2) = 0 := by
    intro α hα
    simp only
    rw [spectralDist_diagonalObs_nonZ f α hα]
    simp
  -- For Z-type, spectralDist matches Fourier coefficient squared
  -- Define the bijection between Z-type indices and Finset (Fin n)
  let Z_indices := {α : Fin n → Fin 4 | ∀ i, α i = 0 ∨ α i = 3}
  -- Use Finset.sum_bij to relate the sums
  -- First, rewrite LHS to only sum over Z-type indices
  conv_lhs =>
    arg 2
    ext α
    rw [show (let prob := spectralDist (diagonalObs f) α
             if prob = 0 then (0 : ℝ) else prob * Real.log prob / Real.log 2) =
            if ∃ i, α i ∈ ({1, 2} : Finset (Fin 4)) then 0
            else (let prob := spectralDist (diagonalObs f) α
                  if prob = 0 then 0 else prob * Real.log prob / Real.log 2) by
          split_ifs with h
          · exact h_XY_zero α h
          · rfl]
  simp only
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  -- Now the sum is only over {α | ¬∃ i, α i ∈ {1,2}} = {α | ∀ i, α i ∈ {0,3}}
  -- This is in bijection with Finset (Fin n) via toZIndex
  -- Convert filtered sum to sum over subtype using Finset.sum_subtype
  -- The notation ∑ x with p, f x is definitionally ∑ x ∈ Finset.univ.filter p, f x
  have h_mem : ∀ x : Fin n → Fin 4, x ∈ Finset.univ.filter (fun x => ¬∃ i, x i ∈ ({1,2} : Finset (Fin 4))) ↔
      ¬∃ i, x i ∈ ({1,2} : Finset (Fin 4)) := by simp
  rw [Finset.sum_subtype _ h_mem]
  -- Convert RHS to sum over subtype {α // ¬∃ i, α i ∈ {1,2}}
  rw [← Fintype.sum_equiv (zIndexEquiv n) _ _ (fun S => rfl)]
  -- Now both sides sum over {α // ¬∃ i, α i ∈ {1,2}}
  apply Finset.sum_congr rfl
  intro α
  simp only [Finset.mem_univ, true_implies]
  -- α is a Z-type index (no X or Y components)
  -- spectralDist at α.val equals fourierCoeff squared at zIndexEquiv α
  have h_spec : spectralDist (diagonalObs f) α.val = (fourierCoeff f (zIndexEquiv n α))^2 := by
    have := spectralDist_diagonalObs_Z_S f (zIndexEquiv n α)
    simp only [zIndexEquiv, Equiv.coe_fn_mk, fromZIndex] at this ⊢
    -- Need to show toZIndex {i | α.val i = 3} = α.val
    have h_eq : toZIndex {i | α.val i = 3} = α.val := toZIndex_fromZIndex α.val α.prop
    rw [h_eq] at this
    exact this
  rw [h_spec]

/-- Diagonal observable's quantum influence equals classical influence -/
theorem diagonalObs_quantumInfluence_eq {n : ℕ} (f : BoolFunc n) :
    quantumInfluence (diagonalObs f) = totalInfluence f := by
  -- Influence = Σ_S |S| * f̂(S)² since only Z_S terms contribute
  -- and wt(Z_S) = |S|
  unfold quantumInfluence totalInfluence
  -- Non-Z terms have spectralDist = 0
  have h_XY_zero : ∀ α : Fin n → Fin 4, (∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) →
      (pauliWeight α : ℝ) * spectralDist (diagonalObs f) α = 0 := by
    intro α hα
    rw [spectralDist_diagonalObs_nonZ f α hα, mul_zero]
  -- Rewrite to sum over non-XY terms only
  conv_lhs =>
    arg 2
    ext α
    rw [show (pauliWeight α : ℝ) * spectralDist (diagonalObs f) α =
            if ∃ i, α i ∈ ({1, 2} : Finset (Fin 4)) then 0
            else (pauliWeight α : ℝ) * spectralDist (diagonalObs f) α by
          split_ifs with h
          · exact h_XY_zero α h
          · rfl]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  -- Now bijection between non-XY terms and Finset (Fin n)
  -- Convert filtered sum to sum over subtype using Finset.sum_subtype
  have h_mem : ∀ x : Fin n → Fin 4, x ∈ Finset.univ.filter (fun x => ¬∃ i, x i ∈ ({1,2} : Finset (Fin 4))) ↔
      ¬∃ i, x i ∈ ({1,2} : Finset (Fin 4)) := by simp
  rw [Finset.sum_subtype _ h_mem]
  -- Convert RHS to sum over subtype {α // ¬∃ i, α i ∈ {1,2}}
  rw [← Fintype.sum_equiv (zIndexEquiv n) _ _ (fun S => rfl)]
  -- Now both sides sum over {α // ¬∃ i, α i ∈ {1,2}}
  apply Finset.sum_congr rfl
  intro α
  simp only [Finset.mem_univ, true_implies]
  -- α is a Z-type index (no X or Y components)
  -- pauliWeight at α.val equals |fromZIndex α.val| and spectralDist equals fourierCoeff squared
  have h_spec : spectralDist (diagonalObs f) α.val = (fourierCoeff f (zIndexEquiv n α))^2 := by
    have := spectralDist_diagonalObs_Z_S f (zIndexEquiv n α)
    simp only [zIndexEquiv, Equiv.coe_fn_mk, fromZIndex] at this ⊢
    have h_eq : toZIndex {i | α.val i = 3} = α.val := toZIndex_fromZIndex α.val α.prop
    rw [h_eq] at this
    exact this
  have h_wt : pauliWeight α.val = (zIndexEquiv n α).card := by
    simp only [zIndexEquiv, Equiv.coe_fn_mk, fromZIndex]
    rw [← pauliWeight_toZIndex]
    congr 1
    exact (toZIndex_fromZIndex α.val α.prop).symm
  rw [h_spec, h_wt]

end Alethfeld.Quantum.ZIndexEquiv
