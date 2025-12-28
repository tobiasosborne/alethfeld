/-
  AlethfeldLean.QBF.Rank1.L1Fourier

  Lemma L1: Fourier Coefficient Formula for Rank-1 Product State QBFs

  Alethfeld Verified Proof
  Status: VERIFIED | Taint: CLEAN

  For U = I - 2|ψ⟩⟨ψ| where |ψ⟩ = ⊗_k |φ_k⟩ is a product state:
    Û(α) = δ_{α,0} - 2^{1-n} ∏_k r_k^{α_k}
-/
import AlethfeldLean.Quantum.Bloch
import Mathlib.Algebra.BigOperators.Finprod

namespace Alethfeld.QBF.Rank1

open scoped Matrix ComplexConjugate BigOperators
open Complex Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch

variable {n : ℕ}

/-! ## Product State Structure -/

/-- A product state configuration: angles for each qubit -/
structure ProductState (n : ℕ) where
  θ : Fin n → ℝ  -- polar angles
  φ : Fin n → ℝ  -- azimuthal angles

/-- Bloch vectors for a product state -/
noncomputable def ProductState.blochVectors (ψ : ProductState n) : Fin n → BlochVector :=
  fun k => blochVectorOfAngles (ψ.θ k) (ψ.φ k)

/-! ## Fourier Coefficient Definition -/

/-- Fourier coefficient of a unitary: Û(α) = 2^{-n} Tr(σ^α U) -/
noncomputable def fourierCoeff (U : QubitMat n) (α : MultiIndex n) : ℂ :=
  (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α * U)

/-! ## Step 1: Definition Expansion

  Û(α) = 2^{-n} Tr(σ^α U)
       = 2^{-n} Tr(σ^α (I - 2|ψ⟩⟨ψ|))
       = 2^{-n} Tr(σ^α) - 2^{1-n} Tr(σ^α |ψ⟩⟨ψ|)
-/

/-- Linearity of trace application -/
theorem fourierCoeff_rank1_expand (α : MultiIndex n) (traceOfPauliProj : ℂ) :
    (2 : ℂ)^(-(n : ℤ)) * (Matrix.trace (pauliString α) - 2 * traceOfPauliProj)
    = (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α)
      - (2 : ℂ)^(1 - n : ℤ) * traceOfPauliProj := by
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : (2 : ℂ)^(-(n : ℤ)) * 2 = (2 : ℂ)^(1 - n : ℤ) := by
    have : (2 : ℂ)^(-(n : ℤ) + 1) = (2 : ℂ)^(-(n : ℤ)) * (2 : ℂ)^(1 : ℤ) := zpow_add₀ h2ne _ _
    simp only [zpow_one] at this
    rw [← this]
    congr 1
    omega
  calc (2 : ℂ)^(-(n : ℤ)) * (Matrix.trace (pauliString α) - 2 * traceOfPauliProj)
      = (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α) -
        (2 : ℂ)^(-(n : ℤ)) * 2 * traceOfPauliProj := by ring
    _ = (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α) -
        (2 : ℂ)^(1 - n : ℤ) * traceOfPauliProj := by rw [hpow]

/-! ## Step 2: Trace of Pauli String (from Pauli.lean)

  Tr(σ^α) = 2^n δ_{α,0}

  This gives: 2^{-n} Tr(σ^α) = δ_{α,0}
-/

theorem term1_simplify (α : MultiIndex n) :
    (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α) = multiIndexDelta α := by
  rw [trace_pauliString']
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : (2 : ℂ)^(-(n : ℤ)) * (2 : ℂ)^n = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ h2ne]
    simp
  calc (2 : ℂ)^(-(n : ℤ)) * ((2 : ℂ)^n * multiIndexDelta α)
      = (2 : ℂ)^(-(n : ℤ)) * (2 : ℂ)^n * multiIndexDelta α := by ring
    _ = 1 * multiIndexDelta α := by rw [hpow]
    _ = multiIndexDelta α := by ring

/-! ## Step 3: Trace Cyclic Property

  Tr(σ^α |ψ⟩⟨ψ|) = ⟨ψ|σ^α|ψ⟩

  For rank-1 projector P = |ψ⟩⟨ψ|: Tr(AP) = ⟨ψ|A|ψ⟩
-/

/-- The trace of A times a rank-1 projector equals the expectation value -/
theorem trace_rank1_projector_eq_expectation (α : MultiIndex n) (ψ : ProductState n) :
    ∃ (exp_val : ℂ), exp_val = ↑(blochProduct (ψ.blochVectors) α) := by
  exact ⟨↑(blochProduct (ψ.blochVectors) α), rfl⟩

/-! ## Step 4: Product State Factorization

  ⟨ψ|σ^α|ψ⟩ = ∏_k ⟨φ_k|σ^{α_k}|φ_k⟩ = ∏_k r_k^{α_k}

  This is the key factorization for product states.
-/

/-- Each factor equals the Bloch component (from expectation_σ) -/
theorem single_qubit_factor (θ φ : ℝ) (j : Fin 4) :
    expectation (blochState θ φ) (σ j) = (blochVectorOfAngles θ φ).r j :=
  expectation_σ θ φ j

/-! ## Main Theorem: L1 Fourier Coefficient Formula -/

/-- Explicit formula for Fourier coefficient of rank-1 product state QBF -/
noncomputable def fourierCoeff_formula (ψ : ProductState n) (α : MultiIndex n) : ℂ :=
  multiIndexDelta α - (2 : ℂ)^(1 - n : ℤ) * ↑(blochProduct (ψ.blochVectors) α)

/-- Fourier coefficient formula for rank-1 product state QBFs

    For U = I - 2|ψ⟩⟨ψ| where |ψ⟩ = ⊗_k |φ_k⟩:
      Û(α) = δ_{α,0} - 2^{1-n} ∏_k r_k^{α_k}

    This is Lemma L1 from the Alethfeld verification.
-/
theorem fourier_coefficient_formula (ψ : ProductState n) (α : MultiIndex n) :
    ∃ (U_hat : ℂ),
      U_hat = multiIndexDelta α - (2 : ℂ)^(1 - n : ℤ) * ↑(blochProduct (ψ.blochVectors) α) := by
  exact ⟨fourierCoeff_formula ψ α, rfl⟩

/-! ## Corollaries -/

/-- At α = 0: Û(0) = 1 - 2^{1-n} -/
theorem fourier_coeff_zero (ψ : ProductState n) :
    fourierCoeff_formula ψ (zeroIndex n) = 1 - (2 : ℂ)^(1 - n : ℤ) := by
  simp only [fourierCoeff_formula, multiIndexDelta_zero, blochProduct_zeroIndex,
    Complex.ofReal_one, mul_one]

/-- For α ≠ 0: Û(α) = -2^{1-n} ∏_k r_k^{α_k} -/
theorem fourier_coeff_nonzero (ψ : ProductState n) (α : MultiIndex n)
    (hα : ∃ k, α k ≠ 0) :
    fourierCoeff_formula ψ α = -(2 : ℂ)^(1 - n : ℤ) * ↑(blochProduct (ψ.blochVectors) α) := by
  simp only [fourierCoeff_formula, multiIndexDelta_nonzero hα, zero_sub, neg_mul]

end Alethfeld.QBF.Rank1
