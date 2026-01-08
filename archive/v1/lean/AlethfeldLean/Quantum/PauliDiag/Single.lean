/-
  AlethfeldLean.Quantum.PauliDiag.Single

  Single-qubit Pauli diagonal properties: σI and σZ are diagonal,
  σX and σY have zero diagonal, diagonal entry formulas.
-/
import AlethfeldLean.Quantum.Pauli

namespace Alethfeld.Quantum.PauliDiag.Single

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli

/-! ## Single-Qubit Diagonal Properties -/

/-- σI is diagonal: off-diagonal entries are zero -/
lemma σI_off_diag (i j : Fin 2) (hij : i ≠ j) : σI i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [σI, of_apply, cons_val_zero, cons_val_one]

/-- σZ is diagonal: off-diagonal entries are zero -/
lemma σZ_off_diag (i j : Fin 2) (hij : i ≠ j) : σZ i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [σZ, of_apply, cons_val_zero, cons_val_one]

/-- σX has zero diagonal -/
lemma σX_diag_zero (i : Fin 2) : σX i i = 0 := by
  fin_cases i <;> simp [σX, of_apply, cons_val_zero, cons_val_one]

/-- σY has zero diagonal -/
lemma σY_diag_zero (i : Fin 2) : σY i i = 0 := by
  fin_cases i <;> simp [σY, of_apply, cons_val_zero, cons_val_one]

/-- σ at index 1 or 2 has zero diagonal -/
lemma σ_XY_diag_zero (k : Fin 4) (hk : k = 1 ∨ k = 2) (i : Fin 2) :
    σ k i i = 0 := by
  rcases hk with rfl | rfl
  · exact σX_diag_zero i
  · exact σY_diag_zero i

/-- σI diagonal entry -/
lemma σI_diag (i : Fin 2) : σI i i = 1 := by
  fin_cases i <;> simp [σI, of_apply, cons_val_zero, cons_val_one]

/-- σZ diagonal entries: σZ 0 0 = 1, σZ 1 1 = -1 -/
lemma σZ_diag_0 : σZ 0 0 = 1 := by simp [σZ, of_apply, cons_val_zero]
lemma σZ_diag_1 : σZ 1 1 = -1 := by simp [σZ, of_apply, cons_val_one]

/-- σZ diagonal entry equals (-1)^bit -/
lemma σZ_diag_entry (i : Fin 2) : σZ i i = (-1 : ℂ)^i.val := by
  fin_cases i
  · simp [σZ_diag_0]
  · simp [σZ_diag_1]

/-- σI diagonal entry always 1 -/
lemma σI_diag_entry (i : Fin 2) : σI i i = 1 := σI_diag i

/-- Diagonal entry of σ at index 0 or 3 -/
lemma σ_IZ_diag_entry (k : Fin 4) (hk : k = 0 ∨ k = 3) (i : Fin 2) :
    σ k i i = if k = 3 then (-1 : ℂ)^i.val else 1 := by
  rcases hk with rfl | rfl
  · simp [σ, σI_diag_entry]
  · simp [σ, σZ_diag_entry]

/-- Helper: σ at index 0 or 3 is diagonal -/
lemma σ_diag_off_diag (k : Fin 4) (hk : k = 0 ∨ k = 3) (i j : Fin 2) (hij : i ≠ j) :
    σ k i j = 0 := by
  rcases hk with rfl | rfl
  · exact σI_off_diag i j hij
  · exact σZ_off_diag i j hij

end Alethfeld.Quantum.PauliDiag.Single
