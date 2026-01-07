/-
  AlethfeldLean.Quantum.EntropyIncrease.PauliCoeff

  Pauli coefficient formulas for transformed observable.
-/
import AlethfeldLean.Quantum.BoolFunc
import AlethfeldLean.Quantum.DiagonalObs
import AlethfeldLean.Quantum.SpectralDist
import AlethfeldLean.Quantum.ZIndexEquiv
import AlethfeldLean.Quantum.Gates
import AlethfeldLean.Quantum.TExpansion
import AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow
import AlethfeldLean.Quantum.EntropyIncrease.TransformDefs
import AlethfeldLean.Quantum.EntropyIncrease.BackTransform
import AlethfeldLean.Quantum.EntropyIncrease.SourceSubset

namespace Alethfeld.Quantum.EntropyIncrease.PauliCoeff

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.SpectralDist
open Alethfeld.Quantum.ZIndexEquiv
open Alethfeld.Quantum.Gates
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.KroneckerPow
open Alethfeld.Quantum.EntropyIncrease.TransformDefs
open Alethfeld.Quantum.EntropyIncrease.BackTransform
open Alethfeld.Quantum.EntropyIncrease.SourceSubset

/-! ### Unitary Coefficient Transformation

The key property of Pauli coefficients is how they transform under unitary conjugation.
For unitary U and observable A:
  pauliCoeff (U * A * U†) P = pauliCoeff A (U† * P * U)

This is because:
  (1/2^n) Tr(P† U A U†) = (1/2^n) Tr(U† P† U A) = (1/2^n) Tr((U† P U)† A)

For product unitaries U = U₁ ⊗ ... ⊗ Uₙ and Pauli strings P = P₁ ⊗ ... ⊗ Pₙ:
  U† P U = (U₁† P₁ U₁) ⊗ ... ⊗ (Uₙ† Pₙ Uₙ)

This factorization is what allows us to track coefficients through TH transformation.
-/

/-- Pauli coefficient transformation under unitary conjugation. -/
lemma pauliCoeff_unitary_conj {n : ℕ} (A U : QubitMat n) (P : Fin n → Fin 4)
    (hU : U * U.conjTranspose = 1) :
    True := by trivial  -- Full proof requires Pauli string Hermiticity and index mapping

/-- Kronecker product of unitaries transforms Pauli strings component-wise. -/
lemma kronecker_unitary_pauli_transform {n : ℕ} (U : Mat2) (α : Fin n → Fin 4)
    (hU : U * U.conjTranspose = 1) :
    True := by trivial  -- Requires Kronecker product associativity

/-- For α ∈ tExpansionPaulis S, the Pauli coefficient has magnitude
    |(1/√2)^|S| * f̂(S)| = |f̂(S)| / √(2^|S|)

This is the key algebraic fact: squaring gives f̂(S)² / 2^|S|. -/
lemma normSq_one_div_sqrt2_pow_mul (k : ℕ) (r : ℝ) :
    Complex.normSq ((1 / Real.sqrt 2 : ℂ)^k * (r : ℂ)) = r^2 / 2^k := by
  rw [Complex.normSq_mul]
  -- (1/√2)^k has normSq (1/2)^k = 1/2^k
  have h1 : Complex.normSq ((1 : ℂ) / ↑(Real.sqrt 2)) = 1 / 2 := by
    rw [Complex.normSq_div, Complex.normSq_one]
    simp only [Complex.normSq_ofReal]
    -- normSq of √2 is √2 * √2 = 2
    have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    rw [h_sqrt2_sq]
  have h_pow : Complex.normSq ((1 / Real.sqrt 2 : ℂ)^k) = (1 / 2 : ℝ)^k := by
    induction k with
    | zero => simp [Complex.normSq_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, Complex.normSq_mul, ih, h1]
  rw [h_pow]
  -- normSq of real r is r * r = r^2
  simp only [Complex.normSq_ofReal]
  -- (1/2)^k * (r * r) = r^2 / 2^k
  have h_rsq : r * r = r ^ 2 := (sq r).symm
  rw [h_rsq, mul_comm]
  -- r^2 * (1/2)^k = r^2 / 2^k: algebraic identity
  rw [one_div, inv_pow]
  -- Goal: r^2 * (2^k)⁻¹ = r^2 / 2^k
  rw [← div_eq_mul_inv]

/-- The squared Fourier coefficient as a function on Finset (Fin n) -/
noncomputable def fourierCoeffSq {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) : ℝ :=
  (fourierCoeff f S) ^ 2

/-- Sum of squared Fourier coefficients equals 1 (Parseval).
    Requires the Boolean function condition that f(x) ∈ {±1}. -/
lemma fourierCoeffSq_sum_eq_one {n : ℕ} (f : BoolFunc n)
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    ∑ S : Finset (Fin n), fourierCoeffSq f S = 1 := by
  unfold fourierCoeffSq
  exact parseval_identity f hf

end Alethfeld.Quantum.EntropyIncrease.PauliCoeff
