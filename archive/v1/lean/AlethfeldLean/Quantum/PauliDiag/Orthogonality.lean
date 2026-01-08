/-
  AlethfeldLean.Quantum.PauliDiag.Orthogonality

  Pauli product traces and orthogonality relations.
-/
import AlethfeldLean.Quantum.Pauli

namespace Alethfeld.Quantum.PauliDiag.Orthogonality

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli

/-! ## Pauli Product Traces (Orthogonality) -/

/-- Product of σI with itself -/
lemma σI_mul_σI : σI * σI = σI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σI, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- Product of σX with itself -/
lemma σX_mul_σX : σX * σX = σI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σX, σI, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- Product of σY with itself -/
lemma σY_mul_σY : σY * σY = σI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σY, σI, Matrix.mul_apply, Fin.sum_univ_two, of_apply, Complex.I_sq]

/-- Product of σZ with itself -/
lemma σZ_mul_σZ : σZ * σZ = σI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σZ, σI, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- σX * σZ product is off-diagonal -/
lemma σX_mul_σZ_diag (i : Fin 2) : (σX * σZ) i i = 0 := by
  fin_cases i <;>
    simp [σX, σZ, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- σZ * σX product is off-diagonal -/
lemma σZ_mul_σX_diag (i : Fin 2) : (σZ * σX) i i = 0 := by
  fin_cases i <;>
    simp [σZ, σX, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- σY * σZ product is off-diagonal -/
lemma σY_mul_σZ_diag (i : Fin 2) : (σY * σZ) i i = 0 := by
  fin_cases i <;>
    simp [σY, σZ, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- σZ * σY product is off-diagonal -/
lemma σZ_mul_σY_diag (i : Fin 2) : (σZ * σY) i i = 0 := by
  fin_cases i <;>
    simp [σZ, σY, Matrix.mul_apply, Fin.sum_univ_two, of_apply]

/-- Trace of σZ * σX is zero -/
lemma trace_σZ_mul_σX : Matrix.trace (σZ * σX) = 0 := by
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, σZ_mul_σX_diag]
  ring

/-- Trace of σZ * σY is zero -/
lemma trace_σZ_mul_σY : Matrix.trace (σZ * σY) = 0 := by
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, σZ_mul_σY_diag]
  ring

/-- Trace of σZ * σI is zero (since trace σZ = 0) -/
lemma trace_σZ_mul_σI : Matrix.trace (σZ * σI) = 0 := by
  have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
  rw [h, Matrix.mul_one]
  exact trace_σZ

/-- Trace of σI * σZ is zero -/
lemma trace_σI_mul_σZ : Matrix.trace (σI * σZ) = 0 := by
  have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
  rw [h, Matrix.one_mul]
  exact trace_σZ

/-- Trace of σX * σZ is zero -/
lemma trace_σX_mul_σZ : Matrix.trace (σX * σZ) = 0 := by
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, σX_mul_σZ_diag]
  ring

/-- Trace of σY * σZ is zero -/
lemma trace_σY_mul_σZ : Matrix.trace (σY * σZ) = 0 := by
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, σY_mul_σZ_diag]
  ring

/-- Trace of product of distinct Paulis is zero -/
lemma trace_σ_mul_σ_ne (a b : Fin 4) (hab : a ≠ b) : Matrix.trace (σ a * σ b) = 0 := by
  -- Exhaustive case analysis
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals simp only [σ]
  -- σI * σX
  · have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
    rw [h, Matrix.one_mul]; exact trace_σX
  -- σI * σY
  · have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
    rw [h, Matrix.one_mul]; exact trace_σY
  -- σI * σZ
  · exact trace_σI_mul_σZ
  -- σX * σI
  · have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
    rw [h, Matrix.mul_one]; exact trace_σX
  -- σX * σY: σX * σY = iσZ which has trace 0
  · simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag]
    simp only [σX, σY, Matrix.mul_apply, Fin.sum_univ_two, of_apply]
    simp only [cons_val_zero, cons_val_one]
    ring
  -- σX * σZ
  · exact trace_σX_mul_σZ
  -- σY * σI
  · have h : σI = (1 : Mat2) := by ext i j; fin_cases i <;> fin_cases j <;> simp [σI, of_apply]
    rw [h, Matrix.mul_one]; exact trace_σY
  -- σY * σX: σY * σX = -iσZ which has trace 0
  · simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag]
    simp only [σY, σX, Matrix.mul_apply, Fin.sum_univ_two, of_apply]
    simp only [cons_val_zero, cons_val_one]
    ring
  -- σY * σZ
  · exact trace_σY_mul_σZ
  -- σZ * σI
  · exact trace_σZ_mul_σI
  -- σZ * σX
  · exact trace_σZ_mul_σX
  -- σZ * σY
  · exact trace_σZ_mul_σY

/-- Trace of product σ_a * σ_b equals 2 δ_{a,b} -/
lemma trace_σ_mul_σ (a b : Fin 4) : Matrix.trace (σ a * σ b) = if a = b then 2 else 0 := by
  by_cases hab : a = b
  · subst hab
    fin_cases a <;> simp only [σ, ↓reduceIte]
    · rw [σI_mul_σI]; exact trace_σI
    · rw [σX_mul_σX]; exact trace_σI
    · rw [σY_mul_σY]; exact trace_σI
    · rw [σZ_mul_σZ]; exact trace_σI
  · simp only [hab, ↓reduceIte]
    exact trace_σ_mul_σ_ne a b hab

end Alethfeld.Quantum.PauliDiag.Orthogonality
