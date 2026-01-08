import Mathlib

open scoped Matrix BigOperators

lemma trace_submatrix_equiv {m n R : Type*} [Fintype m] [Fintype n] [AddCommMonoid R] 
    (A : Matrix m m R) (e : n ≃ m) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.submatrix, Matrix.diag, Matrix.of_apply]
  conv_rhs => rw [← Equiv.sum_comp e]

#check trace_submatrix_equiv
