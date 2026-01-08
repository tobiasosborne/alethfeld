/-
  AlethfeldLean.Quantum.SpectralDist

  Spectral distribution and Pauli coefficient extraction.

  This module defines:
  - pauliCoeff: Pauli coefficient extraction â(P) = (1/2^n) Tr(P† A)
  - spectralDist: The spectral distribution π_A(P) = |â(P)|²
  - spectralEntropy: Quantum spectral entropy H(A)
  - quantumInfluence: Quantum influence Inf(A)
  - Key lemmas relating diagonal observable coefficients to Fourier coefficients
-/
import AlethfeldLean.Quantum.DiagonalObs
import AlethfeldLean.Quantum.TExpansion

namespace Alethfeld.Quantum.SpectralDist

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.PauliDiag
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.TExpansion

/-! ## Pauli Coefficient Extraction -/

/-- Pauli coefficient extraction: â(P) = (1/2^n) Tr(P† A)
    This is the standard definition from quantum information theory. -/
noncomputable def pauliCoeff {n : ℕ} (A : QubitMat n) (P : Fin n → Fin 4) : ℂ :=
  (1 / (2 : ℂ)^n) * Matrix.trace ((pauliString P).conjTranspose * A)

/-- The spectral distribution: π_A(P) = |â(P)|² -/
noncomputable def spectralDist {n : ℕ} (A : QubitMat n) (P : Fin n → Fin 4) : ℝ :=
  Complex.normSq (pauliCoeff A P)

/-- Quantum spectral entropy of an operator: H(A) = -Σ_P π_A(P) log₂ π_A(P) -/
noncomputable def spectralEntropy {n : ℕ} (A : QubitMat n) : ℝ :=
  - ∑ P : (Fin n → Fin 4),
    let prob := spectralDist A P
    if prob = 0 then 0 else prob * Real.log prob / Real.log 2

/-- Quantum influence of an operator: Inf(A) = Σ_P wt(P) · π_A(P) -/
noncomputable def quantumInfluence {n : ℕ} (A : QubitMat n) : ℝ :=
  ∑ P : (Fin n → Fin 4), pauliWeight P * spectralDist A P

/-! ## Diagonal Observable Coefficients -/

/-- Helper: Pauli coefficient of diagonal obs at Z_S equals Fourier coefficient -/
lemma pauliCoeff_diagonalObs_Z_S {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) :
    pauliCoeff (diagonalObs f) (fun i => if i ∈ S then 3 else 0) = (fourierCoeff f S : ℂ) := by
  unfold pauliCoeff fourierCoeff diagonalObs
  -- The key is that Z_S is Hermitian and both Z_S and diagonalObs are diagonal
  -- So trace(Z_S† * diagonalObs f) = Σ_x (Z_S)_xx * (diagonalObs f)_xx
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  -- trace(P† * A) where both are diagonal
  simp only [Matrix.trace, Matrix.diag]
  -- The LHS sums over Fin (2^n), RHS over Fin n → Bool
  -- Use the equivalence boolFuncEquiv to transform the RHS sum
  rw [Complex.ofReal_sum]
  -- Transform RHS sum from (Fin n → Bool) to Fin (2^n) using the equivalence
  rw [Fintype.sum_equiv (boolFuncEquiv n).symm]
  -- Now prove term-by-term equality
  intro x
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
  simp only [Matrix.mul_apply]
  -- Since both matrices are diagonal, only the x = x term contributes
  rw [Finset.sum_eq_single x]
  · -- Main term: (Z_S)_xx† * f(x)
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    -- (pauliString α)_xx = (pauliZ_S S)_xx for our α
    have h_eq : pauliString (fun i => if i ∈ S then (3 : Fin 4) else 0) x x =
        pauliZ_S S x x := rfl
    rw [h_eq, pauliZ_S_diag_entry]
    -- Z_S diagonal entry is real, so conjugate is itself
    -- (-1)^k is real, so its conjugate is itself
    have h_real_pow : ∀ k : ℕ, ((-1 : ℂ)^k).re = (-1 : ℝ)^k ∧ ((-1 : ℂ)^k).im = 0 := by
      intro k
      induction k with
      | zero => simp [Complex.one_re, Complex.one_im]
      | succ k ih =>
        constructor
        · rw [pow_succ, pow_succ, Complex.mul_re]
          simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im]
          rw [ih.1, ih.2]
          ring
        · rw [pow_succ, Complex.mul_im]
          simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im]
          rw [ih.1, ih.2]
          ring
    -- star ((-1)^k) = (-1)^k since (-1)^k is real
    have h_conj : ∀ k : ℕ, star ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
      intro k
      rw [Complex.star_def, Complex.conj_eq_iff_re]
      rw [(h_real_pow k).1]
      simp only [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    rw [h_conj]
    -- Now relate to parityFunc
    -- The key: (boolFuncEquiv n).symm x i = x.val.testBit i.val
    have h_equiv : ∀ i, (boolFuncEquiv n).symm x i = x.val.testBit i.val :=
      fun i => boolFuncEquiv_symm_apply x i
    unfold parityFunc
    -- Both sides should be (-1)^|S ∩ bits(x)|
    -- The filter on (boolFuncEquiv n).symm x is the same as filter on testBit
    have h_filter_eq : (S.filter (fun k => (boolFuncEquiv n).symm x k)).card =
        (S.filter (fun k => x.val.testBit k.val)).card := by
      congr 1
      ext k
      simp only [mem_filter, h_equiv]
    simp_rw [h_filter_eq]
    -- First show that f (...testBit...) = f ((boolFuncEquiv n).symm x)
    have h_f_eq : f (fun i => x.val.testBit i.val) = f ((boolFuncEquiv n).symm x) := by
      congr 1
      ext i
      exact (h_equiv i).symm
    rw [h_f_eq]
    split_ifs with h
    · -- Even case: (-1)^(even) = 1
      have h_even : Even (S.filter (fun k => x.val.testBit k.val)).card :=
        Nat.even_iff.mpr h
      simp only [Int.cast_one, mul_one]
      rw [Even.neg_one_pow h_even]
      simp
    · -- Odd case: (-1)^(odd) = -1
      have h_odd : Odd (S.filter (fun k => x.val.testBit k.val)).card := by
        rw [Nat.odd_iff]
        omega
      simp only [Int.cast_neg, Int.cast_one]
      rw [Odd.neg_one_pow h_odd]
      ring
  · -- Other terms: y ≠ x, show (diagonalObs f)_yx = 0
    intro y _ hyx
    rw [Matrix.diagonal_apply_ne _ hyx, mul_zero]
  · -- Show x ∈ Finset.univ (trivial)
    intro h
    exact absurd (Finset.mem_univ x) h

/-- Helper: Pauli coefficient of diagonal obs is zero for non-Z_S indices -/
lemma pauliCoeff_diagonalObs_nonZ {n : ℕ} (f : BoolFunc n) (α : Fin n → Fin 4)
    (hα : ∃ i, α i ∈ ({1, 2} : Finset (Fin 4))) :
    pauliCoeff (diagonalObs f) α = 0 := by
  -- Convert the hypothesis to the form needed by pauliString_diag_zero_of_XY
  have hα' : ∃ k, α k = 1 ∨ α k = 2 := by
    obtain ⟨i, hi⟩ := hα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    exact ⟨i, hi⟩
  -- Unfold pauliCoeff
  unfold pauliCoeff
  simp only [mul_eq_zero]
  right
  -- trace(P† * A) = ∑_i (P† * A)_ii = ∑_i ∑_j P†_ij * A_ji
  -- For diagonal A: only j = i contributes, so = ∑_i P†_ii * A_ii = ∑_i (P_ii)^* * A_ii
  -- But P_ii = 0 when α has X/Y component
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_eq_zero
  intro x _
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hxy : y = x
  · -- y = x: show (pauliString α)†_xx = 0
    subst hxy
    simp only [Matrix.conjTranspose_apply]
    rw [pauliString_diag_zero_of_XY α hα' y]
    simp
  · -- y ≠ x: show (diagonalObs f)_yx = 0
    have hdiag : diagonalObs f y x = 0 := Matrix.diagonal_apply_ne _ hxy
    rw [hdiag, mul_zero]

end Alethfeld.Quantum.SpectralDist
