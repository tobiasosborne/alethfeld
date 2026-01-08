/-
  AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow

  Kronecker power definitions and structure lemmas.
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli
import AlethfeldLean.Quantum.Gates

namespace Alethfeld.Quantum.EntropyIncrease.KroneckerPow

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli

/-! ## Kronecker Powers -/

/-- n-fold Kronecker power of a 2×2 matrix -/
noncomputable def kroneckerPow : (n : ℕ) → Mat2 → QubitMat n
  | 0, _ => !![1]  -- 1×1 identity
  | n+1, M =>
    let rest := kroneckerPow n M  -- 2^n × 2^n
    let kron := rest ⊗ₖ M         -- 2^(n+1) × 2^(n+1)
    kron.submatrix (finPow2SuccEquiv n) (finPow2SuccEquiv n)

/-! ## Trace Cycling Lemmas -/

/-- Trace cycling: Tr(A B) = Tr(B A) -/
lemma trace_mul_comm' {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) :
    (A * B).trace = (B * A).trace := Matrix.trace_mul_comm A B

/-! ## Kronecker Power Structure Lemmas -/

/-- kroneckerPow (n+1) has the Kronecker-submatrix structure -/
lemma kroneckerPow_succ (n : ℕ) (M : Mat2) :
    kroneckerPow (n+1) M = (kroneckerPow n M ⊗ₖ M).submatrix (finPow2SuccEquiv n) (finPow2SuccEquiv n) :=
  rfl

/-- Conjugate transpose of submatrix (for equivalence with same domain/codomain) -/
lemma conjTranspose_submatrix_equiv {α : Type*} [Fintype α] {β : Type*} [Star β]
    (A : Matrix α α β) (e : α' ≃ α) :
    (A.submatrix e e).conjTranspose = A.conjTranspose.submatrix e e := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply]

/-- Product of two submatrix expressions with same equivalence -/
lemma submatrix_mul_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m m ℂ) (e : n ≃ m) :
    (A.submatrix e e) * (B.submatrix e e) = (A * B).submatrix e e :=
  Matrix.submatrix_mul_equiv A B e e e

/-- Conjugate transpose of Kronecker product (using commutativity of ℂ) -/
lemma conjTranspose_kronecker_ℂ {m n p q : Type*}
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (A ⊗ₖ B).conjTranspose = A.conjTranspose ⊗ₖ B.conjTranspose :=
  Matrix.conjTranspose_kronecker A B

/-- Mixed product property for Kronecker products (same types) -/
lemma mul_kronecker_mul_ℂ {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m m ℂ) (C D : Matrix n n ℂ) :
    (A * B) ⊗ₖ (C * D) = (A ⊗ₖ C) * (B ⊗ₖ D) :=
  Matrix.mul_kronecker_mul A B C D

/-! ## Conjugation Factorization -/

/-- Key factorization: conjugation of product unitary Kronecker powers factors.
    H† T† P T H = ((H_rest † T_rest † P_rest † T_rest H_rest) ⊗ₖ (h† t† p t h)).submatrix e e
    when H, T, P are built from Kronecker-submatrix structure. -/
lemma conjugation_factors_through_kronecker {n : ℕ}
    (H_rest T_rest P_rest : QubitMat n) (h t p : Mat2) :
    let e := finPow2SuccEquiv n
    let H := (H_rest ⊗ₖ h).submatrix e e
    let T := (T_rest ⊗ₖ t).submatrix e e
    let P := (P_rest ⊗ₖ p).submatrix e e
    H.conjTranspose * T.conjTranspose * P.conjTranspose * T * H =
      ((H_rest.conjTranspose * T_rest.conjTranspose * P_rest.conjTranspose * T_rest * H_rest) ⊗ₖ
       (h.conjTranspose * t.conjTranspose * p.conjTranspose * t * h)).submatrix e e := by
  intro e H T P
  -- Step 1: Move conjTranspose inside submatrix
  have hH_conj : H.conjTranspose = (H_rest.conjTranspose ⊗ₖ h.conjTranspose).submatrix e e := by
    simp only [H, conjTranspose_submatrix_equiv, conjTranspose_kronecker_ℂ]
  have hT_conj : T.conjTranspose = (T_rest.conjTranspose ⊗ₖ t.conjTranspose).submatrix e e := by
    simp only [T, conjTranspose_submatrix_equiv, conjTranspose_kronecker_ℂ]
  have hP_conj : P.conjTranspose = (P_rest.conjTranspose ⊗ₖ p.conjTranspose).submatrix e e := by
    simp only [P, conjTranspose_submatrix_equiv, conjTranspose_kronecker_ℂ]
  -- Step 2: Combine products using submatrix_mul_submatrix_equiv
  rw [hH_conj, hT_conj, hP_conj]
  rw [submatrix_mul_submatrix_equiv, submatrix_mul_submatrix_equiv,
      submatrix_mul_submatrix_equiv, submatrix_mul_submatrix_equiv]
  -- Step 3: Use mul_kronecker_mul to factor the Kronecker products
  congr 1
  rw [mul_kronecker_mul_ℂ, mul_kronecker_mul_ℂ, mul_kronecker_mul_ℂ, mul_kronecker_mul_ℂ]

end Alethfeld.Quantum.EntropyIncrease.KroneckerPow
