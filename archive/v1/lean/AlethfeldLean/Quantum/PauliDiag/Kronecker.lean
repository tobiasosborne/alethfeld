/-
  AlethfeldLean.Quantum.PauliDiag.Kronecker

  Kronecker product diagonal properties and Pauli string diagonal lemmas.
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli
import AlethfeldLean.Quantum.PauliDiag.Single

namespace Alethfeld.Quantum.PauliDiag.Kronecker

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.PauliDiag.Single

/-! ## Kronecker Product Diagonal Properties -/

/-- Diagonal entry of Kronecker product is product of diagonal entries -/
lemma kronecker_diag_entry {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (i : m × n) :
    Matrix.kroneckerMap (· * ·) A B i i = A i.1 i.1 * B i.2 i.2 := by
  simp only [Matrix.kroneckerMap_apply]

/-- Kronecker product of diagonal matrices is diagonal -/
lemma kronecker_diag_off_diag {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : ∀ i j, i ≠ j → A i j = 0) (hB : ∀ i j, i ≠ j → B i j = 0)
    (i j : m × n) (hij : i ≠ j) :
    Matrix.kroneckerMap (· * ·) A B i j = 0 := by
  simp only [Matrix.kroneckerMap_apply]
  by_cases h1 : i.1 = j.1
  · have h2 : i.2 ≠ j.2 := by
      intro h
      apply hij
      ext <;> assumption
    rw [hB i.2 j.2 h2, mul_zero]
  · rw [hA i.1 j.1 h1, zero_mul]

/-! ## Pauli String Diagonal Properties -/

/-- pauliString is diagonal when all indices are 0 or 3 -/
lemma pauliString_diag {n : ℕ} (α : MultiIndex n) (hα : ∀ k, α k = 0 ∨ α k = 3)
    (i j : Fin (2 ^ n)) (hij : i ≠ j) : pauliString α i j = 0 := by
  induction n with
  | zero =>
    have heq : i = j := Fin.ext (by omega)
    exact absurd heq hij
  | succ n ih =>
    simp only [pauliString]
    simp only [Matrix.submatrix_apply]
    have h_rest : ∀ i j, i ≠ j → pauliString (fun k => α k.succ) i j = 0 := fun i j hij =>
      ih (fun k => α k.succ) (fun k => hα k.succ) i j hij
    have h_first : ∀ i j, i ≠ j → σ (α 0) i j = 0 := fun i j hij =>
      σ_diag_off_diag (α 0) (hα 0) i j hij
    let e := finPow2SuccEquiv n
    have h_ne : e i ≠ e j := by
      intro heq
      apply hij
      exact e.injective heq
    simp only [Matrix.kroneckerMap_apply]
    by_cases h1 : (e i).1 = (e j).1
    · have h2 : (e i).2 ≠ (e j).2 := by
        intro h
        apply h_ne
        exact Prod.ext h1 h
      have hzero := h_first (e i).2 (e j).2 h2
      simp only [e] at hzero
      rw [hzero, mul_zero]
    · have hzero := h_rest (e i).1 (e j).1 h1
      simp only [e] at hzero
      rw [hzero, zero_mul]

/-- Diagonal entry of submatrix equals original diagonal entry at reindexed position -/
lemma submatrix_diag_entry {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (e : n ≃ m) (x : n) :
    (A.submatrix e e) x x = A (e x) (e x) := by
  simp only [Matrix.submatrix_apply]

/-- Diagonal entry of pauliString when all indices are 0 or 3 -/
lemma pauliString_diag_entry {n : ℕ} (α : MultiIndex n) (hα : ∀ k, α k = 0 ∨ α k = 3)
    (x : Fin (2 ^ n)) :
    pauliString α x x = ∏ k : Fin n,
      (if α k = 3 then (-1 : ℂ) ^ (if x.val.testBit k.val then 1 else 0) else 1) := by
  induction n with
  | zero =>
    simp [pauliString, Finset.univ_eq_empty]
  | succ n ih =>
    simp only [pauliString]
    rw [submatrix_diag_entry]
    simp only [Matrix.kroneckerMap_apply]
    rw [Fin.prod_univ_succ]
    have h_rest := ih (fun k => α k.succ) (fun k => hα k.succ)
    let fst := (finPow2SuccEquiv n x).1
    have h_fst_val : fst.val = x.val / 2 := finPow2SuccEquiv_fst n x
    let snd := (finPow2SuccEquiv n x).2
    have h_snd_val : snd.val = x.val % 2 := finPow2SuccEquiv_snd n x
    specialize h_rest fst
    rw [mul_comm]
    congr 1
    · rw [σ_IZ_diag_entry (α 0) (hα 0) snd]
      simp only [snd, h_snd_val]
      have h_tb0 : x.val.testBit 0 = (x.val % 2 = 1) := testBit_zero_eq_mod2 x.val
      by_cases h0 : α 0 = 3
      · simp only [h0, ↓reduceIte]
        congr 1
        by_cases hbit : x.val % 2 = 1
        · have htb : x.val.testBit 0 = true := by rw [h_tb0]; exact hbit
          simp [htb, hbit]
        · have hbit0 : x.val % 2 = 0 := by omega
          have htb : x.val.testBit 0 = false := by
            by_contra htb'
            push_neg at htb'
            have h1 : x.val.testBit 0 = true := Bool.eq_true_of_not_eq_false htb'
            have : x.val % 2 = 1 := by rwa [← h_tb0]
            omega
          simp [htb, hbit0]
      · have hα0 : α 0 = 0 := by
          rcases hα 0 with h | h <;> simp_all
        simp only [hα0]
        rfl
    · rw [h_rest]
      apply Finset.prod_congr rfl
      intro i _
      have h_tb : x.val.testBit i.val.succ = (x.val / 2).testBit i.val :=
        Nat.testBit_succ x.val i.val
      simp only [Fin.val_succ, h_fst_val, h_tb]

/-- pauliString has zero diagonal if any component is X or Y -/
lemma pauliString_diag_zero_of_XY {n : ℕ} (α : MultiIndex n)
    (hα : ∃ k, α k = 1 ∨ α k = 2) (x : Fin (2 ^ n)) :
    pauliString α x x = 0 := by
  obtain ⟨k, hk⟩ := hα
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [pauliString]
    simp only [Matrix.submatrix_apply]
    simp only [Matrix.kroneckerMap_apply]
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · have hdiag : σ (α 0) ((finPow2SuccEquiv n x).2) ((finPow2SuccEquiv n x).2) = 0 :=
        σ_XY_diag_zero (α 0) hk _
      rw [hdiag, mul_zero]
    · have hzero := ih (fun (i : Fin n) => α i.succ) (finPow2SuccEquiv n x).1 j hk
      rw [hzero, zero_mul]

end Alethfeld.Quantum.PauliDiag.Kronecker
