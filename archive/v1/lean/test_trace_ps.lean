import AlethfeldLean.Quantum.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Finprod

namespace Test

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum

-- Pauli matrices
def σI : Mat2 := !![1, 0; 0, 1]
def σX : Mat2 := !![0, 1; 1, 0]
def σY : Mat2 := !![0, -Complex.I; Complex.I, 0]
def σZ : Mat2 := !![1, 0; 0, -1]

def σ : Fin 4 → Mat2
  | 0 => σI
  | 1 => σX
  | 2 => σY
  | 3 => σZ

theorem trace_σI : Matrix.trace σI = 2 := by
  simp only [σI, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one]; norm_num

theorem trace_σX : Matrix.trace σX = 0 := by
  simp only [σX, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one]; norm_num

theorem trace_σY : Matrix.trace σY = 0 := by
  simp only [σY, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one]; norm_num

theorem trace_σZ : Matrix.trace σZ = 0 := by
  simp only [σZ, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.of_apply,
    cons_val_zero, cons_val_one]; norm_num

theorem trace_σ (j : Fin 4) : Matrix.trace (σ j) = if j = 0 then 2 else 0 := by
  fin_cases j <;> simp [σ, trace_σI, trace_σX, trace_σY, trace_σZ]

def finPow2SuccEquiv (n : ℕ) : Fin (2^(n+1)) ≃ Fin (2^n) × Fin 2 :=
  (finCongr (Nat.pow_succ 2 n)).trans finProdFinEquiv.symm

noncomputable def pauliString : {n : ℕ} → MultiIndex n → QubitMat n
  | 0, _ => !![1]
  | n+1, α =>
    let rest := pauliString (fun k => α k.succ)
    let first := σ (α 0)
    let kron := rest ⊗ₖ first
    kron.submatrix (finPow2SuccEquiv n) (finPow2SuccEquiv n)

lemma trace_submatrix_equiv {m n R : Type*} [Fintype m] [Fintype n] [AddCommMonoid R] 
    (A : Matrix m m R) (e : n ≃ m) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.submatrix, Matrix.diag, Matrix.of_apply]
  conv_rhs => rw [← Equiv.sum_comp e]

-- Helper: isZeroIndex for n+1 iff first is zero and rest is zero
lemma isZeroIndex_succ_iff {n : ℕ} (α : MultiIndex (n+1)) :
    isZeroIndex α ↔ α 0 = 0 ∧ isZeroIndex (fun k => α k.succ) := by
  constructor
  · intro h
    exact ⟨h 0, fun k => h k.succ⟩
  · intro ⟨h0, hrest⟩ k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact h0
    · exact hrest j

-- Main theorem  
theorem trace_pauliString {n : ℕ} (α : MultiIndex n) :
    Matrix.trace (pauliString α) = if isZeroIndex α then (2 : ℂ)^n else 0 := by
  induction n with
  | zero => 
    have hz : isZeroIndex α := fun k => Fin.elim0 k
    simp only [pauliString, Matrix.trace, Matrix.diag, hz, ↓reduceIte, pow_zero]
    simp only [Matrix.of_apply, cons_val_fin_one]
    simp  -- handles ∑ _ : Fin 1, 1 = 1
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

#check trace_pauliString

end Test
