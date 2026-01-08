/-
  AlethfeldLean.Quantum.Bloch

  Bloch sphere representation of single-qubit pure states.
  Key result: expectation values of Pauli matrices equal Bloch components.
-/
import AlethfeldLean.Quantum.Pauli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Alethfeld.Quantum.Bloch

open scoped Matrix ComplexConjugate BigOperators
open Complex Real Alethfeld.Quantum Alethfeld.Quantum.Pauli

/-! ## Bloch Vector Definition -/

/-- A Bloch vector (x, y, z) with unit norm -/
structure BlochVector where
  x : ℝ
  y : ℝ
  z : ℝ
  norm_sq : x^2 + y^2 + z^2 = 1

/-- Extended Bloch components: r^(0) = 1, r^(1) = x, r^(2) = y, r^(3) = z -/
def BlochVector.r (v : BlochVector) : Fin 4 → ℝ
  | 0 => 1
  | 1 => v.x
  | 2 => v.y
  | 3 => v.z

/-- Squared Bloch components: q^(0) = 1, q^(1) = x², q^(2) = y², q^(3) = z² -/
def BlochVector.q (v : BlochVector) : Fin 4 → ℝ
  | 0 => 1
  | 1 => v.x^2
  | 2 => v.y^2
  | 3 => v.z^2

/-- Sum of all q components equals 2: q^(0) + q^(1) + q^(2) + q^(3) = 1 + x² + y² + z² = 2 -/
theorem BlochVector.q_sum_eq_two (v : BlochVector) :
    v.q 0 + v.q 1 + v.q 2 + v.q 3 = 2 := by
  simp only [BlochVector.q]
  linarith [v.norm_sq]

/-- Sum of nonzero q components equals 1: q^(1) + q^(2) + q^(3) = x² + y² + z² = 1 -/
theorem BlochVector.q_nonzero_sum_eq_one (v : BlochVector) :
    v.q 1 + v.q 2 + v.q 3 = 1 := by
  simp only [BlochVector.q]
  exact v.norm_sq

/-- q components are non-negative (squares) -/
theorem BlochVector.q_nonneg (v : BlochVector) (m : Fin 4) : 0 ≤ v.q m := by
  fin_cases m <;> simp only [BlochVector.q] <;> nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]

/-- q^(0) = 1 always -/
theorem BlochVector.q_zero_eq_one (v : BlochVector) : v.q 0 = 1 := rfl

/-- Each q component is at most 1 -/
theorem BlochVector.q_le_one (v : BlochVector) (m : Fin 4) : v.q m ≤ 1 := by
  fin_cases m
  · simp only [BlochVector.q]; norm_num
  · have h := v.norm_sq
    simp only [BlochVector.q]
    nlinarith [sq_nonneg v.y, sq_nonneg v.z]
  · have h := v.norm_sq
    simp only [BlochVector.q]
    nlinarith [sq_nonneg v.x, sq_nonneg v.z]
  · have h := v.norm_sq
    simp only [BlochVector.q]
    nlinarith [sq_nonneg v.x, sq_nonneg v.y]

/-- Product of Bloch components over all qubits for a multi-index -/
noncomputable def blochProduct {n : ℕ} (bloch : Fin n → BlochVector) (α : MultiIndex n) : ℝ :=
  ∏ k, (bloch k).r (α k)

theorem blochProduct_zeroIndex {n : ℕ} (bloch : Fin n → BlochVector) :
    blochProduct bloch (zeroIndex n) = 1 := by
  simp only [blochProduct, zeroIndex, BlochVector.r, Finset.prod_const_one]

/-! ## Single-Qubit State Representation -/

/-- A single-qubit pure state as a 2-vector -/
abbrev QubitState := Fin 2 → ℂ

/-- Standard basis states -/
def ket0 : QubitState := ![1, 0]
def ket1 : QubitState := ![0, 1]

/-- Bloch parametrization: |φ⟩ = cos(θ/2)|0⟩ + e^{iφ}sin(θ/2)|1⟩ -/
noncomputable def blochState (θ φ : ℝ) : QubitState :=
  ![Real.cos (θ/2), Complex.exp (Complex.I * φ) * Real.sin (θ/2)]

/-- The Bloch vector corresponding to angles (θ, φ) -/
noncomputable def blochVectorOfAngles (θ φ : ℝ) : BlochVector where
  x := Real.sin θ * Real.cos φ
  y := Real.sin θ * Real.sin φ
  z := Real.cos θ
  norm_sq := by
    have h1 : (Real.sin θ * Real.cos φ)^2 + (Real.sin θ * Real.sin φ)^2 =
              Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
    have h2 : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
    rw [h1, h2, mul_one, Real.sin_sq_add_cos_sq]

/-! ## Expectation Values -/

/-- Inner product ⟨ψ|φ⟩ for qubit states -/
noncomputable def innerProduct (ψ φ : QubitState) : ℂ :=
  ∑ i, conj (ψ i) * φ i

/-- Matrix-vector product for 2x2 matrix acting on qubit state -/
noncomputable def matVecMul (A : Mat2) (ψ : QubitState) : QubitState :=
  fun i => ∑ j, A i j * ψ j

/-- Expectation value ⟨ψ|A|ψ⟩ -/
noncomputable def expectation (ψ : QubitState) (A : Mat2) : ℂ :=
  innerProduct ψ (matVecMul A ψ)

/-! ## Helper Lemmas for Expectation Computations -/

/-- exp(iφ) * conj(exp(iφ)) = 1 -/
lemma exp_mul_conj_exp_eq_one (φ : ℝ) :
    cexp (↑φ * I) * (starRingEnd ℂ) (cexp (↑φ * I)) = 1 := by
  rw [mul_comm, ← normSq_eq_conj_mul_self]
  simp only [normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
  norm_num

/-- exp(iφ) + conj(exp(iφ)) = 2cos(φ) -/
lemma exp_add_exp_conj (φ : ℝ) :
    cexp (↑φ * I) + (starRingEnd ℂ) (cexp (↑φ * I)) = 2 * ↑(Real.cos φ) := by
  rw [exp_mul_I]
  simp only [map_add, map_mul, conj_I, mul_neg]
  have hc : (starRingEnd ℂ) (Complex.cos ↑φ) = Complex.cos ↑φ := by
    rw [← ofReal_cos]; exact conj_ofReal _
  have hs : (starRingEnd ℂ) (Complex.sin ↑φ) = Complex.sin ↑φ := by
    rw [← ofReal_sin]; exact conj_ofReal _
  rw [hc, hs, ← ofReal_cos]
  ring

/-- conj(exp(iφ)) - exp(iφ) = -2i*sin(φ) -/
lemma exp_conj_sub_exp (φ : ℝ) :
    (starRingEnd ℂ) (cexp (↑φ * I)) - cexp (↑φ * I) = -2 * I * ↑(Real.sin φ) := by
  rw [exp_mul_I]
  simp only [map_add, map_mul, conj_I, mul_neg]
  have hc : (starRingEnd ℂ) (Complex.cos ↑φ) = Complex.cos ↑φ := by
    rw [← ofReal_cos]; exact conj_ofReal _
  have hs : (starRingEnd ℂ) (Complex.sin ↑φ) = Complex.sin ↑φ := by
    rw [← ofReal_sin]; exact conj_ofReal _
  rw [hc, hs, ← ofReal_sin]
  ring

/-! ## Main Bloch Expectation Theorems -/

/-- ⟨φ|I|φ⟩ = 1 for normalized state -/
theorem expectation_σI (θ φ : ℝ) :
    expectation (blochState θ φ) σI = 1 := by
  simp only [expectation, innerProduct, matVecMul, blochState, σI]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  simp only [map_mul, conj_ofReal]
  have hexp : cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ)) = 1 := by
    rw [mul_comm I]
    exact exp_mul_conj_exp_eq_one φ
  calc ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) +
       cexp (I * ↑φ) * ↑(Real.sin (θ * (1 / 2))) * ((starRingEnd ℂ) (cexp (I * ↑φ)) * ↑(Real.sin (θ * (1 / 2))))
      = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) +
        cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ)) * (↑(Real.sin (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2)))) := by ring
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) +
        1 * (↑(Real.sin (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2)))) := by rw [hexp]
    _ = ↑(Real.cos (θ * (1 / 2)))^2 + ↑(Real.sin (θ * (1 / 2)))^2 := by ring
    _ = ↑(Real.cos (θ * (1 / 2))^2 + Real.sin (θ * (1 / 2))^2) := by push_cast; ring
    _ = ↑(1 : ℝ) := by rw [Real.cos_sq_add_sin_sq]
    _ = 1 := ofReal_one

/-- ⟨φ|σ_x|φ⟩ = sin θ cos φ = x -/
theorem expectation_σX (θ φ : ℝ) :
    expectation (blochState θ φ) σX = (blochVectorOfAngles θ φ).x := by
  simp only [expectation, innerProduct, matVecMul, blochState, σX, blochVectorOfAngles]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  simp only [map_mul, conj_ofReal]
  have hexp_sum : cexp (I * ↑φ) + (starRingEnd ℂ) (cexp (I * ↑φ)) = 2 * ↑(Real.cos φ) := by
    rw [mul_comm I]
    exact exp_add_exp_conj φ
  calc ↑(Real.cos (θ * (1 / 2))) * cexp (I * ↑φ) * ↑(Real.sin (θ * (1 / 2))) +
       ↑(Real.cos (θ * (1 / 2))) * ((starRingEnd ℂ) (cexp (I * ↑φ)) * ↑(Real.sin (θ * (1 / 2))))
      = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) *
        (cexp (I * ↑φ) + (starRingEnd ℂ) (cexp (I * ↑φ))) := by ring
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) * (2 * ↑(Real.cos φ)) := by
        rw [hexp_sum]
    _ = ↑(2 * Real.sin (θ * (1 / 2)) * Real.cos (θ * (1 / 2))) * ↑(Real.cos φ) := by
        push_cast; ring
    _ = ↑(Real.sin (2 * (θ * (1 / 2)))) * ↑(Real.cos φ) := by rw [Real.sin_two_mul]
    _ = ↑(Real.sin θ) * ↑(Real.cos φ) := by ring_nf
    _ = ↑(Real.sin θ * Real.cos φ) := by push_cast; ring

/-- ⟨φ|σ_y|φ⟩ = sin θ sin φ = y -/
theorem expectation_σY (θ φ : ℝ) :
    expectation (blochState θ φ) σY = (blochVectorOfAngles θ φ).y := by
  simp only [expectation, innerProduct, matVecMul, blochState, σY, blochVectorOfAngles]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  simp only [map_mul, conj_ofReal]
  have hexp_diff : (starRingEnd ℂ) (cexp (I * ↑φ)) - cexp (I * ↑φ) = -2 * I * ↑(Real.sin φ) := by
    rw [mul_comm I]
    exact exp_conj_sub_exp φ
  calc -(↑(Real.cos (θ * (1 / 2))) * I * cexp (I * ↑φ) * ↑(Real.sin (θ * (1 / 2)))) +
       ↑(Real.cos (θ * (1 / 2))) * I * ((starRingEnd ℂ) (cexp (I * ↑φ)) * ↑(Real.sin (θ * (1 / 2))))
      = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) * I *
        ((starRingEnd ℂ) (cexp (I * ↑φ)) - cexp (I * ↑φ)) := by ring
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) * I *
        (-2 * I * ↑(Real.sin φ)) := by rw [hexp_diff]
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) * (I * I) * (-2) * ↑(Real.sin φ) := by
        ring
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2))) * (-1) * (-2) * ↑(Real.sin φ) := by
        rw [I_mul_I]
    _ = ↑(2 * Real.sin (θ * (1 / 2)) * Real.cos (θ * (1 / 2))) * ↑(Real.sin φ) := by
        push_cast; ring
    _ = ↑(Real.sin (2 * (θ * (1 / 2)))) * ↑(Real.sin φ) := by rw [Real.sin_two_mul]
    _ = ↑(Real.sin θ) * ↑(Real.sin φ) := by ring_nf
    _ = ↑(Real.sin θ * Real.sin φ) := by push_cast; ring

/-- ⟨φ|σ_z|φ⟩ = cos θ = z -/
theorem expectation_σZ (θ φ : ℝ) :
    expectation (blochState θ φ) σZ = (blochVectorOfAngles θ φ).z := by
  simp only [expectation, innerProduct, matVecMul, blochState, σZ, blochVectorOfAngles]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  simp only [map_mul, conj_ofReal]
  have hexp : cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ)) = 1 := by
    rw [mul_comm I]
    exact exp_mul_conj_exp_eq_one φ
  calc ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) -
       cexp (I * ↑φ) * ↑(Real.sin (θ * (1 / 2))) *
         ((starRingEnd ℂ) (cexp (I * ↑φ)) * ↑(Real.sin (θ * (1 / 2))))
      = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) -
        cexp (I * ↑φ) * (starRingEnd ℂ) (cexp (I * ↑φ)) *
          (↑(Real.sin (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2)))) := by ring
    _ = ↑(Real.cos (θ * (1 / 2))) * ↑(Real.cos (θ * (1 / 2))) -
        1 * (↑(Real.sin (θ * (1 / 2))) * ↑(Real.sin (θ * (1 / 2)))) := by rw [hexp]
    _ = ↑(Real.cos (θ * (1 / 2)))^2 - ↑(Real.sin (θ * (1 / 2)))^2 := by ring
    _ = ↑(Real.cos (θ * (1 / 2))^2 - Real.sin (θ * (1 / 2))^2) := by push_cast; ring
    _ = ↑(Real.cos (2 * (θ * (1 / 2)))) := by rw [Real.cos_two_mul']
    _ = ↑(Real.cos θ) := by ring_nf

/-- Unified theorem: ⟨φ|σ^j|φ⟩ = r^(j) for Bloch component r -/
theorem expectation_σ (θ φ : ℝ) (j : Fin 4) :
    expectation (blochState θ φ) (σ j) = (blochVectorOfAngles θ φ).r j := by
  fin_cases j
  · exact expectation_σI θ φ
  · exact expectation_σX θ φ
  · exact expectation_σY θ φ
  · exact expectation_σZ θ φ

end Alethfeld.Quantum.Bloch
