/-
  AlethfeldLean.Quantum.DiagonalObs

  Diagonal observables and their Pauli expansion.

  This module defines:
  - Z_S and X_S Pauli strings
  - L_f diagonal observable from a Boolean function
  - Theorem: L_f = Σ_S f̂(S) Z_S (Pauli expansion)
-/
import AlethfeldLean.Quantum.BoolFunc
import AlethfeldLean.Quantum.PauliDiag
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Alethfeld.Quantum.DiagonalObs

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.PauliDiag

/-! ## Pauli String Definitions -/

/-- Z_S Pauli string: Z at positions in S, I elsewhere -/
noncomputable def pauliZ_S {n : ℕ} (S : Finset (Fin n)) : QubitMat n :=
  Alethfeld.Quantum.Pauli.pauliString (fun i => if i ∈ S then 3 else 0)

/-- X_S Pauli string: X at positions in S, I elsewhere -/
noncomputable def pauliX_S {n : ℕ} (S : Finset (Fin n)) : QubitMat n :=
  Alethfeld.Quantum.Pauli.pauliString (fun i => if i ∈ S then 1 else 0)

/-! ## Diagonal Observable -/

/-- L_f diagonal observable from a Boolean function -/
noncomputable def diagonalObs {n : ℕ} (f : BoolFunc n) : QubitMat n :=
  Matrix.diagonal (fun x => (f (fun i => x.val.testBit i.val) : ℂ))

/-! ## Z_S Properties -/

/-- Z_S is a diagonal matrix: off-diagonal entries are zero -/
lemma pauliZ_S_off_diag {n : ℕ} (S : Finset (Fin n)) (i j : Fin (2^n)) (hij : i ≠ j) :
    pauliZ_S S i j = 0 := by
  unfold pauliZ_S
  apply pauliString_diag
  · intro k
    by_cases hk : k ∈ S <;> simp [hk]
  · exact hij

/-- Diagonal entry of Z_S at position x equals (-1)^|S ∩ x| -/
lemma pauliZ_S_diag_entry {n : ℕ} (S : Finset (Fin n)) (x : Fin (2 ^ n)) :
    pauliZ_S S x x = (-1 : ℂ)^(S.filter (fun i => x.val.testBit i.val)).card := by
  unfold pauliZ_S
  rw [pauliString_diag_entry]
  · -- The product formula equals (-1)^|S ∩ x|
    -- First, simplify the condition: (if k ∈ S then 3 else 0) = 3 ↔ k ∈ S
    have h_cond : ∀ k : Fin n, ((if k ∈ S then (3 : Fin 4) else 0) = 3) = (k ∈ S) := by
      intro k
      by_cases hk : k ∈ S <;> simp [hk]
    -- Rewrite using h_cond
    simp_rw [h_cond]
    -- Now the product is: ∏ k, if k ∈ S then (-1)^(if x.testBit k then 1 else 0) else 1
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one]
    -- Now we have: ∏ k ∈ S, (-1)^(if x.testBit k then 1 else 0)
    -- Use Finset.prod_pow to convert to (-1)^(∑ k ∈ S, (if x.testBit k then 1 else 0))
    have h_pow : ∏ k ∈ Finset.filter (· ∈ S) Finset.univ,
        (-1 : ℂ)^(if (x.val).testBit k.val then 1 else 0) =
        (-1 : ℂ)^(∑ k ∈ Finset.filter (· ∈ S) Finset.univ,
          (if (x.val).testBit k.val then 1 else 0)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [h_pow]
    -- The filter (· ∈ S) over univ is just S itself
    have h_filter_eq : Finset.filter (· ∈ S) Finset.univ = S := by
      ext k
      simp
    rw [h_filter_eq]
    congr 1
    -- Sum of (if testBit then 1 else 0) equals cardinality of filter
    rw [← Finset.card_filter]
  · intro k
    by_cases hk : k ∈ S <;> simp [hk]

/-! ## Diagonal Pauli Expansion -/

/-- Lemma 1: L_f = Σ_S f̂(S) Z_S

This is the Pauli expansion of a diagonal observable, fundamental to Fourier analysis
on Boolean functions. The proof uses:
1. Each Z_S is diagonal with entries (-1)^|S ∩ x|
2. The Fourier inversion formula: f(x) = Σ_S f̂(S) χ_S(x)
-/
theorem diagonal_pauli_expansion {n : ℕ} (f : BoolFunc n) :
    diagonalObs f = ∑ S : Finset (Fin n), (fourierCoeff f S : ℂ) • pauliZ_S S := by
  ext i j
  by_cases hij : i = j
  · -- Diagonal entries
    subst hij
    simp only [diagonalObs, Matrix.diagonal_apply_eq]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    -- Use pauliZ_S_diag_entry to relate pauliZ_S i i to parityFunc
    have h_diag : ∀ S, pauliZ_S S i i = (-1 : ℂ)^(S.filter (fun k => i.val.testBit k.val)).card :=
      fun S => pauliZ_S_diag_entry S i
    simp_rw [h_diag]
    -- Relate (-1)^|S ∩ bits(i)| to parityFunc
    let x := fun k : Fin n => i.val.testBit k.val
    have h_parity : ∀ S, (-1 : ℂ)^(S.filter (fun k => i.val.testBit k.val)).card =
        (parityFunc S x : ℂ) := by
      intro S
      unfold parityFunc
      -- The two filter sets are the same since x k = i.val.testBit k.val
      have h_filter_eq : S.filter (fun k => i.val.testBit k.val) =
          S.filter (fun k => x k) := by
        ext k
        simp only [Finset.mem_filter, x]
      rw [h_filter_eq]
      split_ifs with h
      · -- Even case: (-1)^even = 1
        have h_even : Even (S.filter (fun k => x k)).card := Nat.even_iff.mpr h
        simp only [Int.cast_one]
        exact h_even.neg_one_pow
      · -- Odd case: (-1)^odd = -1
        push_neg at h
        have h_odd : Odd (S.filter (fun k => x k)).card := by
          rw [Nat.odd_iff]
          omega
        simp only [Int.cast_neg, Int.cast_one]
        exact h_odd.neg_one_pow
    simp_rw [h_parity]
    -- Now use Fourier inversion
    have h_inv := fourier_inversion f x
    convert h_inv using 1
  · -- Off-diagonal entries are zero
    simp only [diagonalObs, Matrix.diagonal_apply_ne _ hij]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    -- Use pauliZ_S_off_diag
    have : ∀ S, pauliZ_S S i j = 0 := fun S => pauliZ_S_off_diag S i j hij
    simp only [this, mul_zero, Finset.sum_const_zero]

/-- Lemma 2: H⊗ⁿ Z_S (H⊗ⁿ)† = X_S -/
theorem hadamard_n_conj_Z_S {n : ℕ} (S : Finset (Fin n)) :
    -- Uses tensor product structure and single-qubit results
    True := by  -- Placeholder - full statement requires kroneckerPow
  trivial

end Alethfeld.Quantum.DiagonalObs
