/-
  AlethfeldLean.Quantum.Gates

  Quantum gate definitions and conjugation lemmas.

  This module defines:
  - Hadamard gate H
  - T gate
  - Conjugation actions: H P H†, T P T† for Pauli matrices P
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

namespace Alethfeld.Quantum.Gates

open scoped Matrix ComplexConjugate
open Complex Matrix Real Alethfeld.Quantum.Pauli

/-! ## Gate Definitions -/

/-- The Hadamard gate -/
noncomputable def hadamard : Mat2 :=
  (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- The T gate -/
noncomputable def tGate : Mat2 :=
  !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

/-! ## Hadamard Conjugation -/

/-- Hadamard is self-adjoint (H† = H) -/
lemma hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  unfold hadamard
  simp only [conjTranspose_smul]
  congr 1
  · rw [star_div₀, star_one]
    congr 1
    exact Complex.conj_ofReal _
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTranspose, of_apply, cons_val_zero, cons_val_one]

/-- Helper for Hadamard: √2 * √2 = 2 -/
private lemma sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)

/-- Helper: (1/√2)² = 1/2 -/
private lemma hadamard_coeff_sq :
    ((1 : ℂ) / ↑(Real.sqrt 2)) * ((1 : ℂ) / ↑(Real.sqrt 2)) = (1 / 2 : ℂ) := by
  rw [div_mul_div_comm, one_mul]
  congr 1
  rw [← ofReal_mul, sqrt2_sq, ofReal_ofNat]

/-- H X H† = Z -/
theorem hadamard_conj_X : hadamard * σX * hadamard.conjTranspose = σZ := by
  rw [hadamard_conjTranspose]
  unfold hadamard σX σZ
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_assoc, smul_eq_mul, hadamard_coeff_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [of_apply, cons_val_zero, cons_val_one, smul_apply, smul_eq_mul] <;> ring

/-- H Y H† = -Y -/
theorem hadamard_conj_Y : hadamard * σY * hadamard.conjTranspose = -σY := by
  rw [hadamard_conjTranspose]
  unfold hadamard σY
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_assoc, smul_eq_mul, hadamard_coeff_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [of_apply, cons_val_zero, cons_val_one, smul_apply, smul_eq_mul, neg_apply] <;> ring

/-- H Z H† = X -/
theorem hadamard_conj_Z : hadamard * σZ * hadamard.conjTranspose = σX := by
  rw [hadamard_conjTranspose]
  unfold hadamard σZ σX
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_assoc, smul_eq_mul, hadamard_coeff_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [of_apply, cons_val_zero, cons_val_one, smul_apply, smul_eq_mul] <;> ring

/-! ## T Gate Conjugation -/

/-- Helper: conj(I*π/4) = -I*π/4 -/
private lemma conj_I_pi_div_4 :
    (starRingEnd ℂ) (Complex.I * Real.pi / 4) = -Complex.I * Real.pi / 4 := by
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h : (starRingEnd ℂ) (4 : ℂ) = 4 := by
    have : (4 : ℂ) = ((4 : ℕ) : ℂ) := by norm_cast
    rw [this, Complex.conj_natCast]
  simp only [h]

/-- Helper: conj(exp(I*π/4)) = exp(-I*π/4) -/
private lemma conj_exp_I_pi_4 :
    starRingEnd ℂ (Complex.exp (Complex.I * Real.pi / 4)) =
    Complex.exp (-Complex.I * Real.pi / 4) := by
  rw [← Complex.exp_conj, conj_I_pi_div_4]

/-- T gate conjugate transpose -/
lemma tGate_conjTranspose :
    tGate.conjTranspose = !![1, 0; 0, Complex.exp (-Complex.I * Real.pi / 4)] := by
  unfold tGate conjTranspose
  ext i j
  fin_cases i <;> fin_cases j
  · simp [of_apply, Matrix.map_apply]
  · simp [of_apply, Matrix.map_apply]
  · simp [of_apply, Matrix.map_apply]
  · simp only [of_apply, Matrix.map_apply]
    exact conj_exp_I_pi_4

/-- exp(iπ/4) * exp(-iπ/4) = 1 -/
private lemma exp_pi4_mul_exp_neg_pi4 :
    Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (-Complex.I * Real.pi / 4) = 1 := by
  rw [← Complex.exp_add]
  have : Complex.I * Real.pi / 4 + -Complex.I * Real.pi / 4 = 0 := by ring
  rw [this, Complex.exp_zero]

/-- exp(-iπ/4) * exp(iπ/4) = 1 (commuted form) -/
lemma exp_neg_pi4_mul_exp_pi4 :
    Complex.exp (-Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = 1 := by
  rw [mul_comm]; exact exp_pi4_mul_exp_neg_pi4

/-- T gate is unitary: T† T = 1 -/
lemma tGate_conjTranspose_mul_tGate : tGate.conjTranspose * tGate = 1 := by
  rw [tGate_conjTranspose]
  unfold tGate
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one,
      Matrix.cons_val', Matrix.cons_val_zero', Matrix.cons_val_succ', one_apply]
  -- (0,0) case: 1*1 + 0*0 = if 0=0 then 1 else 0
  · simp
  -- (0,1) case: 1*0 + 0*exp = if 0=1 then 1 else 0
  · simp
  -- (1,0) case: 0*1 + exp*0 = if 1=0 then 1 else 0
  · simp
  -- (1,1) case: 0*0 + exp(-iπ/4)*exp(iπ/4) = if 1=1 then 1 else 0
  · simp only [mul_zero, zero_mul, add_zero, zero_add, ite_true]
    exact exp_neg_pi4_mul_exp_pi4

/-- Variant with grouped negation -/
@[simp] private lemma exp_pi4_mul_exp_neg_pi4' :
    Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (-(Complex.I * Real.pi) / 4) = 1 := by
  have h : -(Complex.I * Real.pi) / 4 = -Complex.I * Real.pi / 4 := by ring
  rw [h]
  exact exp_pi4_mul_exp_neg_pi4

/-- Helper: √2 ^ 2 = 2 in ℂ -/
private lemma sqrt2_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [sq, ← ofReal_mul, Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  simp

/-- exp(iπ/4) = (1+i)/√2 -/
lemma exp_I_pi_div_4_eq :
    Complex.exp (Complex.I * Real.pi / 4) = (1 + Complex.I) / Real.sqrt 2 := by
  rw [show Complex.I * Real.pi / 4 = (Real.pi / 4 : ℝ) * Complex.I by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]; ring]
  rw [← Complex.cos_add_sin_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp only [Complex.ofReal_div]
  field_simp
  rw [sqrt2_sq_complex]
  simp only [ofReal_ofNat]

/-- T I T† = I -/
theorem tgate_conj_I : tGate * σI * tGate.conjTranspose = σI := by
  rw [tGate_conjTranspose]
  unfold tGate σI
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, of_apply]

/-- T Z T† = Z -/
theorem tgate_conj_Z : tGate * σZ * tGate.conjTranspose = σZ := by
  rw [tGate_conjTranspose]
  unfold tGate σZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, of_apply]

/-- Helper: exp(-iπ/4) * exp(iπ/4) = 1 (alternative form) -/
private lemma exp_neg_pi4_mul_exp_pi4_alt :
    Complex.exp (Complex.I * Real.pi * (-1/4)) * Complex.exp (Complex.I * Real.pi * (1/4)) = 1 := by
  rw [← Complex.exp_add]
  have heq : Complex.I * Real.pi * (-1/4) + Complex.I * Real.pi * (1/4) = 0 := by ring
  rw [heq, Complex.exp_zero]

/-- T† Z T = Z (inverse conjugation) -/
theorem tgate_inv_conj_Z : tGate.conjTranspose * σZ * tGate = σZ := by
  rw [tGate_conjTranspose]
  unfold tGate σZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one,
      Matrix.cons_val', Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals ring_nf
  -- The (1,1) case: need -(exp * exp) = -1
  rw [exp_neg_pi4_mul_exp_pi4_alt]

/-- H† Z H = X (inverse Hadamard conjugation, using H† = H) -/
theorem hadamard_inv_conj_Z : hadamard.conjTranspose * σZ * hadamard = σX := by
  conv_lhs => rw [hadamard_conjTranspose]
  conv_rhs => rw [← hadamard_conj_Z]
  rw [hadamard_conjTranspose]

/-- exp(-iπ/4) = (1-i)/√2 -/
lemma exp_neg_I_pi_div_4_eq :
    Complex.exp (-Complex.I * Real.pi / 4) = (1 - Complex.I) / Real.sqrt 2 := by
  rw [show -Complex.I * Real.pi / 4 = (-(Real.pi / 4) : ℝ) * Complex.I by
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]; ring]
  rw [← Complex.cos_add_sin_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp only [Complex.ofReal_div, Complex.ofReal_neg]
  field_simp
  rw [sqrt2_sq_complex]
  simp only [ofReal_ofNat]
  ring

/-- Helper: (1+I)/√2 * (1-I)/√2 = 1 -/
private lemma omega_mul_omega_conj :
    (1 + Complex.I) / Real.sqrt 2 * ((1 - Complex.I) / Real.sqrt 2) = 1 := by
  field_simp
  rw [sqrt2_sq_complex]
  have h : (1 + Complex.I) * (1 - Complex.I) = 1 - Complex.I^2 := by ring
  rw [h, Complex.I_sq]
  ring

/-- T X T† = (X + Y)/√2 -/
theorem tgate_conj_X :
    tGate * σX * tGate.conjTranspose =
    (1 / Real.sqrt 2 : ℂ) • (σX + σY) := by
  rw [tGate_conjTranspose]
  unfold tGate σX σY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, smul_apply, smul_eq_mul,
      add_apply, cons_val_zero, cons_val_one, Matrix.cons_val', Matrix.cons_val_zero',
      Matrix.cons_val_succ', exp_I_pi_div_4_eq, exp_neg_I_pi_div_4_eq] <;>
    ring

/-- T Y T† = (Y - X)/√2 -/
theorem tgate_conj_Y :
    tGate * σY * tGate.conjTranspose =
    (1 / Real.sqrt 2 : ℂ) • (σY - σX) := by
  rw [tGate_conjTranspose]
  unfold tGate σX σY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, smul_apply, smul_eq_mul,
      sub_apply, cons_val_zero, cons_val_one, Matrix.cons_val', Matrix.cons_val_zero',
      Matrix.cons_val_succ', exp_I_pi_div_4_eq, exp_neg_I_pi_div_4_eq] <;>
    ring_nf <;>
    simp only [Complex.I_sq] <;>
    ring

/-! ## Inverse T Gate Conjugation (T† P T)

These lemmas show how Paulis transform under T† · T (needed for coefficient tracking). -/

/-- T† X T = (X - Y)/√2 -/
theorem tgate_inv_conj_X :
    tGate.conjTranspose * σX * tGate =
    (1 / Real.sqrt 2 : ℂ) • (σX - σY) := by
  rw [tGate_conjTranspose]
  unfold tGate σX σY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, smul_apply, smul_eq_mul,
      sub_apply, cons_val_zero, cons_val_one, Matrix.cons_val', Matrix.cons_val_zero',
      Matrix.cons_val_succ', exp_I_pi_div_4_eq, exp_neg_I_pi_div_4_eq] <;>
    ring

/-- T† Y T = (X + Y)/√2 -/
theorem tgate_inv_conj_Y :
    tGate.conjTranspose * σY * tGate =
    (1 / Real.sqrt 2 : ℂ) • (σX + σY) := by
  rw [tGate_conjTranspose]
  unfold tGate σX σY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, smul_apply, smul_eq_mul,
      add_apply, cons_val_zero, cons_val_one, Matrix.cons_val', Matrix.cons_val_zero',
      Matrix.cons_val_succ', exp_I_pi_div_4_eq, exp_neg_I_pi_div_4_eq] <;>
    ring_nf <;>
    simp only [Complex.I_sq] <;>
    ring

/-! ## Combined H T† P T H Conjugation

These lemmas show the full conjugation H† T† P T H = H T† P T H (using H† = H).
Key for coefficient tracking: the diagonal is (1/√2) times the diagonal of Z. -/

/-- H σX H = σZ (from H being self-adjoint and hadamard_conj_X) -/
lemma hadamard_σX_hadamard : hadamard * σX * hadamard = σZ := by
  rw [show hadamard * σX * hadamard = hadamard * σX * hadamard.conjTranspose by
    rw [hadamard_conjTranspose]]
  exact hadamard_conj_X

/-- H σY H = -σY (from H being self-adjoint and hadamard_conj_Y) -/
lemma hadamard_σY_hadamard : hadamard * σY * hadamard = -σY := by
  rw [show hadamard * σY * hadamard = hadamard * σY * hadamard.conjTranspose by
    rw [hadamard_conjTranspose]]
  exact hadamard_conj_Y

/-- H T† X T H = (Z + Y)/√2 -/
theorem hadamard_tgate_inv_conj_X :
    hadamard * (tGate.conjTranspose * σX * tGate) * hadamard = (1 / Real.sqrt 2 : ℂ) • (σZ + σY) := by
  rw [tgate_inv_conj_X]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  -- H (σX - σY) H = H σX H - H σY H = σZ - (-σY) = σZ + σY
  rw [Matrix.mul_sub, Matrix.sub_mul]
  -- Need to reassociate: hadamard * (σX - σY) = hadamard * σX - hadamard * σY
  -- Then: (hadamard * σX - hadamard * σY) * hadamard = hadamard * σX * hadamard - hadamard * σY * hadamard
  have hX : hadamard * σX * hadamard = σZ := hadamard_σX_hadamard
  have hY : hadamard * σY * hadamard = -σY := hadamard_σY_hadamard
  calc hadamard * σX * hadamard - hadamard * σY * hadamard
      = σZ - (-σY) := by rw [hX, hY]
    _ = σZ + σY := by ext i j; fin_cases i <;> fin_cases j <;>
        simp [σZ, σY, of_apply, sub_apply, add_apply, neg_apply, cons_val_zero, cons_val_one]

/-- H T† Y T H = (Z - Y)/√2 -/
theorem hadamard_tgate_inv_conj_Y :
    hadamard * (tGate.conjTranspose * σY * tGate) * hadamard = (1 / Real.sqrt 2 : ℂ) • (σZ - σY) := by
  rw [tgate_inv_conj_Y]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  -- H (σX + σY) H = H σX H + H σY H = σZ + (-σY) = σZ - σY
  rw [Matrix.mul_add, Matrix.add_mul]
  have hX : hadamard * σX * hadamard = σZ := hadamard_σX_hadamard
  have hY : hadamard * σY * hadamard = -σY := hadamard_σY_hadamard
  calc hadamard * σX * hadamard + hadamard * σY * hadamard
      = σZ + (-σY) := by rw [hX, hY]
    _ = σZ - σY := by ext i j; fin_cases i <;> fin_cases j <;>
        simp [σZ, σY, of_apply, add_apply, sub_apply, neg_apply, cons_val_zero, cons_val_one]

/-- Diagonal of (Z + Y) is the same as diagonal of Z (since Y has zero diagonal) -/
lemma diag_Z_plus_Y : ∀ i : Fin 2, (σZ + σY) i i = σZ i i := by
  intro i
  fin_cases i <;> simp [σZ, σY, of_apply, add_apply, cons_val_zero, cons_val_one]

/-- Diagonal of (Z - Y) is the same as diagonal of Z (since Y has zero diagonal) -/
lemma diag_Z_minus_Y : ∀ i : Fin 2, (σZ - σY) i i = σZ i i := by
  intro i
  fin_cases i <;> simp [σZ, σY, of_apply, sub_apply, cons_val_zero, cons_val_one]

/-- Diagonal entry of H T† X T H is (1/√2) times diagonal of Z -/
lemma hadamard_tgate_inv_conj_X_diag (i : Fin 2) :
    (hadamard * (tGate.conjTranspose * σX * tGate) * hadamard) i i =
    (1 / Real.sqrt 2 : ℂ) * σZ i i := by
  rw [hadamard_tgate_inv_conj_X]
  simp only [smul_apply, smul_eq_mul]
  rw [diag_Z_plus_Y]

/-- Diagonal entry of H T† Y T H is (1/√2) times diagonal of Z -/
lemma hadamard_tgate_inv_conj_Y_diag (i : Fin 2) :
    (hadamard * (tGate.conjTranspose * σY * tGate) * hadamard) i i =
    (1 / Real.sqrt 2 : ℂ) * σZ i i := by
  rw [hadamard_tgate_inv_conj_Y]
  simp only [smul_apply, smul_eq_mul]
  rw [diag_Z_minus_Y]

end Alethfeld.Quantum.Gates
