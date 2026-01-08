/-
  AlethfeldLean.Quantum.Basic

  Basic definitions for quantum computing formalization.
  Uses Mathlib's matrix and complex number infrastructure.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Alethfeld.Quantum

open scoped Matrix ComplexConjugate Kronecker

/-- A 2x2 complex matrix representing a single-qubit operator -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- An n-qubit operator is a 2^n × 2^n matrix -/
abbrev QubitMat (n : ℕ) := Matrix (Fin (2^n)) (Fin (2^n)) ℂ

/-- Multi-index for Pauli strings: α ∈ {0,1,2,3}^n -/
abbrev MultiIndex (n : ℕ) := Fin n → Fin 4

/-- The zero multi-index (all zeros) -/
def zeroIndex (n : ℕ) : MultiIndex n := fun _ => 0

/-- Check if a multi-index is the zero index -/
def isZeroIndex {n : ℕ} (α : MultiIndex n) : Prop := ∀ k, α k = 0

/-- Decidable instance for isZeroIndex -/
instance {n : ℕ} (α : MultiIndex n) : Decidable (isZeroIndex α) :=
  inferInstanceAs (Decidable (∀ k, α k = 0))

/-- Kronecker delta for multi-indices -/
noncomputable def multiIndexDelta {n : ℕ} (α : MultiIndex n) : ℂ :=
  if isZeroIndex α then 1 else 0

theorem multiIndexDelta_zero (n : ℕ) : multiIndexDelta (zeroIndex n) = 1 := by
  simp [multiIndexDelta, isZeroIndex, zeroIndex]

theorem multiIndexDelta_nonzero {n : ℕ} {α : MultiIndex n}
    (h : ∃ k, α k ≠ 0) : multiIndexDelta α = 0 := by
  simp only [multiIndexDelta]
  split_ifs with hz
  · exfalso
    obtain ⟨k, hk⟩ := h
    exact hk (hz k)
  · rfl

end Alethfeld.Quantum
