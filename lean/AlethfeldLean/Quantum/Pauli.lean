/-
  AlethfeldLean.Quantum.Pauli

  Pauli matrices and their fundamental properties.
  Includes trace properties essential for Fourier analysis.
-/
import AlethfeldLean.Quantum.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Finprod

namespace Alethfeld.Quantum.Pauli

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset

/-- Pauli I (identity) -/
def σI : Mat2 := !![1, 0; 0, 1]

/-- Pauli X -/
def σX : Mat2 := !![0, 1; 1, 0]

/-- Pauli Y -/
def σY : Mat2 := !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z -/
def σZ : Mat2 := !![1, 0; 0, -1]

/-- Single-qubit Pauli matrix indexed by Fin 4 -/
def σ : Fin 4 → Mat2
  | 0 => σI
  | 1 => σX
  | 2 => σY
  | 3 => σZ

/-! ## Trace Properties -/

theorem trace_σI : Matrix.trace σI = 2 := by
  simp only [σI, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one, head_cons]
  norm_num

theorem trace_σX : Matrix.trace σX = 0 := by
  simp only [σX, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one, head_cons]
  norm_num

theorem trace_σY : Matrix.trace σY = 0 := by
  simp only [σY, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one, head_cons]
  norm_num

theorem trace_σZ : Matrix.trace σZ = 0 := by
  simp only [σZ, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one, head_cons]
  norm_num

/-- Trace of σ^j is 2 if j=0, else 0 -/
theorem trace_σ (j : Fin 4) : Matrix.trace (σ j) = if j = 0 then 2 else 0 := by
  fin_cases j <;> simp [σ, trace_σI, trace_σX, trace_σY, trace_σZ]

/-- Corollary: trace of non-identity Pauli is zero -/
theorem trace_σ_ne_zero {j : Fin 4} (hj : j ≠ 0) : Matrix.trace (σ j) = 0 := by
  simp [trace_σ, hj]

/-! ## Pauli Strings (Tensor Products) -/

/-- Equivalence between Fin (2^(n+1)) and Fin (2^n) × Fin 2 -/
def finPow2SuccEquiv (n : ℕ) : Fin (2^(n+1)) ≃ Fin (2^n) × Fin 2 :=
  (finCongr (Nat.pow_succ 2 n)).trans finProdFinEquiv.symm

/-- n-fold tensor product of single-qubit Pauli matrices
    σ^α = σ^{α₁} ⊗ σ^{α₂} ⊗ ⋯ ⊗ σ^{αₙ} -/
noncomputable def pauliString : {n : ℕ} → MultiIndex n → QubitMat n
  | 0, _ => !![1]
  | n+1, α =>
    let rest := pauliString (fun k => α k.succ)  -- QubitMat n
    let first := σ (α 0)                           -- Mat2
    let kron := rest ⊗ₖ first
    kron.submatrix (finPow2SuccEquiv n) (finPow2SuccEquiv n)

/-- Trace of tensor product factors -/
theorem trace_kronecker (A B : Mat2) :
    Matrix.trace (A ⊗ₖ B) = Matrix.trace A * Matrix.trace B :=
  Matrix.trace_kronecker A B

/-- Trace is preserved under reindexing by an equivalence -/
lemma trace_submatrix_equiv {m n R : Type*} [Fintype m] [Fintype n] [AddCommMonoid R]
    (A : Matrix m m R) (e : n ≃ m) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.submatrix, Matrix.diag, Matrix.of_apply]
  conv_rhs => rw [← Equiv.sum_comp e]

/-- isZeroIndex for n+1 decomposes into first element and rest -/
lemma isZeroIndex_succ_iff {n : ℕ} (α : MultiIndex (n+1)) :
    isZeroIndex α ↔ α 0 = 0 ∧ isZeroIndex (fun k => α k.succ) := by
  constructor
  · intro h
    exact ⟨h 0, fun k => h k.succ⟩
  · intro ⟨h0, hrest⟩ k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact h0
    · exact hrest j

/-- Main theorem: Trace of Pauli string
    Tr(σ^α) = 2^n if α = 0, else 0 -/
theorem trace_pauliString {n : ℕ} (α : MultiIndex n) :
    Matrix.trace (pauliString α) = if isZeroIndex α then (2 : ℂ)^n else 0 := by
  induction n with
  | zero =>
    have hz : isZeroIndex α := fun k => Fin.elim0 k
    simp only [pauliString, Matrix.trace, Matrix.diag, hz, ↓reduceIte, pow_zero]
    simp only [Matrix.of_apply, cons_val_fin_one]
    simp
  | succ n ih =>
    simp only [pauliString]
    rw [trace_submatrix_equiv]
    rw [Matrix.trace_kronecker]
    rw [ih (fun k => α k.succ)]
    rw [trace_σ (α 0)]
    have h_iff := isZeroIndex_succ_iff α
    by_cases h0 : α 0 = 0 <;> by_cases hrest : isZeroIndex (fun k => α k.succ)
    · have hz : isZeroIndex α := h_iff.mpr ⟨h0, hrest⟩
      simp only [h0, ↓reduceIte, hrest, hz, pow_succ, mul_comm]
    · have hnz : ¬isZeroIndex α := fun h => hrest (h_iff.mp h).2
      simp [h0, hrest, hnz]
    · have hnz : ¬isZeroIndex α := fun h => h0 (h_iff.mp h).1
      simp [h0, hrest, hnz]
    · have hnz : ¬isZeroIndex α := fun h => h0 (h_iff.mp h).1
      simp [h0, hrest, hnz]

/-- Simplified form using multiIndexDelta -/
theorem trace_pauliString' {n : ℕ} (α : MultiIndex n) :
    Matrix.trace (pauliString α) = (2 : ℂ)^n * multiIndexDelta α := by
  rw [trace_pauliString]
  simp only [multiIndexDelta]
  split_ifs <;> ring

end Alethfeld.Quantum.Pauli
