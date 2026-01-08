import AlethfeldLean.Quantum.Pauli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Test

open scoped Matrix ComplexConjugate BigOperators
open Complex Real Alethfeld.Quantum Alethfeld.Quantum.Pauli
open Matrix (cons_val_zero cons_val_one head_cons)

abbrev QubitState := Fin 2 → ℂ

noncomputable def blochState (θ φ : ℝ) : QubitState :=
  ![Real.cos (θ/2), Complex.exp (Complex.I * φ) * Real.sin (θ/2)]

noncomputable def innerProduct (ψ φ : QubitState) : ℂ :=
  ∑ i, conj (ψ i) * φ i

noncomputable def matVecMul (A : Mat2) (ψ : QubitState) : QubitState :=
  fun i => ∑ j, A i j * ψ j

noncomputable def expectation (ψ : QubitState) (A : Mat2) : ℂ :=
  innerProduct ψ (matVecMul A ψ)

-- Helper: exp(iφ) * conj(exp(iφ)) = 1 for real φ
lemma exp_mul_conj_exp_eq_one (φ : ℝ) : 
    cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ)) = 1 := by
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  have h : I * ↑φ = ↑φ * I := by ring
  rw [h, normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
  norm_num

theorem expectation_σI (θ φ : ℝ) :
    expectation (blochState θ φ) σI = 1 := by
  simp only [expectation, innerProduct, matVecMul, blochState, σI]
  simp only [Fin.sum_univ_two, Matrix.of_apply, cons_val_zero, cons_val_one]
  ring_nf
  have hcr : (starRingEnd ℂ) ↑(Real.cos (θ * (1/2))) = ↑(Real.cos (θ * (1/2))) := Complex.conj_ofReal _
  have hsr : (starRingEnd ℂ) ↑(Real.sin (θ * (1/2))) = ↑(Real.sin (θ * (1/2))) := Complex.conj_ofReal _
  simp only [map_mul, hcr, hsr]
  calc ↑(Real.cos (θ * (1/2))) * ↑(Real.cos (θ * (1/2))) + 
       cexp (I * ↑φ) * ↑(Real.sin (θ * (1/2))) * ((starRingEnd ℂ) (cexp (I * ↑φ)) * ↑(Real.sin (θ * (1/2))))
      = ↑(Real.cos (θ * (1/2)))^2 + 
        (cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ))) * ↑(Real.sin (θ * (1/2)))^2 := by ring
    _ = ↑(Real.cos (θ * (1/2)))^2 + 1 * ↑(Real.sin (θ * (1/2)))^2 := by rw [exp_mul_conj_exp_eq_one]
    _ = ↑((Real.cos (θ * (1/2)))^2 + (Real.sin (θ * (1/2)))^2) := by push_cast; ring
    _ = ↑(1 : ℝ) := by rw [Real.cos_sq_add_sin_sq]
    _ = 1 := by norm_cast

#check expectation_σI

end Test
