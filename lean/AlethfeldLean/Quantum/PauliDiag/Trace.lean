/-
  AlethfeldLean.Quantum.PauliDiag.Trace

  Trace lemmas for products with diagonal matrices.
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli

namespace Alethfeld.Quantum.PauliDiag.Trace

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli

/-! ## Trace with Diagonal Matrices -/

/-- Trace of product with diagonal matrix equals sum of products of diagonal entries -/
lemma trace_mul_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (d : n → ℂ) :
    Matrix.trace (M * Matrix.diagonal d) = ∑ i, M i i * d i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Trace of diagonal times matrix equals sum of products of diagonal entries -/
lemma trace_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (M : Matrix n n ℂ) :
    Matrix.trace (Matrix.diagonal d * M) = ∑ i, d i * M i i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Trace of diagonal times zero-diagonal matrix is zero -/
lemma trace_diagonal_mul_zero_diag {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (M : Matrix n n ℂ) (hM : ∀ i, M i i = 0) :
    Matrix.trace (Matrix.diagonal d * M) = 0 := by
  rw [trace_diagonal_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [hM i, mul_zero]

/-- Trace of M† * diagonal when M has zero diagonal -/
lemma trace_conjTranspose_mul_diagonal_zero_diag {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (d : n → ℂ) (hM : ∀ i, M i i = 0) :
    Matrix.trace (M.conjTranspose * Matrix.diagonal d) = 0 := by
  rw [trace_mul_diagonal]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Matrix.conjTranspose_apply, hM i, star_zero, zero_mul]

/-- Trace of matrix * diagonal when matrix has zero diagonal -/
lemma trace_mul_diagonal_zero_diag {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (d : n → ℂ) (hM : ∀ i, M i i = 0) :
    Matrix.trace (M * Matrix.diagonal d) = 0 := by
  rw [trace_mul_diagonal]
  apply Finset.sum_eq_zero
  intro i _
  rw [hM i, zero_mul]

/-- Key structural lemma: Trace of product where one factor has zero diagonal -/
lemma trace_product_zero_of_zero_diag_and_diag {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (D : Matrix n n ℂ)
    (hM : ∀ i, M i i = 0) (hD : ∀ i j, i ≠ j → D i j = 0) :
    (M * D).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [hM i, zero_mul]
  · intro j _ hji
    rw [hD j i hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## Trace of Submatrix by Equivalence -/

/-- Trace of submatrix by equivalence equals trace -/
lemma trace_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix m m ℂ) (e : n ≃ m) :
    (A.submatrix e e).trace = A.trace := by
  unfold Matrix.trace Matrix.diag
  rw [Fintype.sum_equiv e.symm]
  intro x
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]

/-! ## Trace of Kronecker Products -/

/-- Trace of Kronecker product -/
lemma trace_kronecker_prod {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (A ⊗ₖ B).trace = A.trace * B.trace := Matrix.trace_kronecker A B

/-- If a Kronecker factor has zero trace, the product has zero trace -/
lemma trace_kronecker_zero_of_first {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A.trace = 0) :
    (A ⊗ₖ B).trace = 0 := by
  rw [Matrix.trace_kronecker, hA, zero_mul]

lemma trace_kronecker_zero_of_second {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hB : B.trace = 0) :
    (A ⊗ₖ B).trace = 0 := by
  rw [Matrix.trace_kronecker, hB, mul_zero]

/-- Trace of σX is zero -/
lemma trace_σX_zero : σX.trace = 0 := trace_σX

/-- Trace of σY is zero -/
lemma trace_σY_zero : σY.trace = 0 := trace_σY

end Alethfeld.Quantum.PauliDiag.Trace
