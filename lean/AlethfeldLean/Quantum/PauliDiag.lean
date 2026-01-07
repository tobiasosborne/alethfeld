/-
  AlethfeldLean.Quantum.PauliDiag

  Pauli diagonal lemmas: properties of diagonal Pauli matrices and strings.

  This module establishes:
  - σI and σZ are diagonal (off-diagonal entries are zero)
  - σX and σY have zero diagonal
  - Diagonal entries of σI, σZ in terms of (-1)^bit
  - Kronecker products of diagonal matrices are diagonal
  - pauliString is diagonal when all indices are 0 or 3
  - pauliString diagonal entry formula
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli

namespace Alethfeld.Quantum.PauliDiag

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli

/-! ## Single-Qubit Diagonal Properties -/

/-- σI is diagonal: off-diagonal entries are zero -/
lemma σI_off_diag (i j : Fin 2) (hij : i ≠ j) : σI i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [σI, of_apply, cons_val_zero, cons_val_one]

/-- σZ is diagonal: off-diagonal entries are zero -/
lemma σZ_off_diag (i j : Fin 2) (hij : i ≠ j) : σZ i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [σZ, of_apply, cons_val_zero, cons_val_one]

/-- σX has zero diagonal -/
lemma σX_diag_zero (i : Fin 2) : σX i i = 0 := by
  fin_cases i <;> simp [σX, of_apply, cons_val_zero, cons_val_one]

/-- σY has zero diagonal -/
lemma σY_diag_zero (i : Fin 2) : σY i i = 0 := by
  fin_cases i <;> simp [σY, of_apply, cons_val_zero, cons_val_one]

/-- σ at index 1 or 2 has zero diagonal -/
lemma σ_XY_diag_zero (k : Fin 4) (hk : k = 1 ∨ k = 2) (i : Fin 2) :
    σ k i i = 0 := by
  rcases hk with rfl | rfl
  · exact σX_diag_zero i
  · exact σY_diag_zero i

/-- σI diagonal entry -/
lemma σI_diag (i : Fin 2) : σI i i = 1 := by
  fin_cases i <;> simp [σI, of_apply, cons_val_zero, cons_val_one]

/-- σZ diagonal entries: σZ 0 0 = 1, σZ 1 1 = -1 -/
lemma σZ_diag_0 : σZ 0 0 = 1 := by simp [σZ, of_apply, cons_val_zero]
lemma σZ_diag_1 : σZ 1 1 = -1 := by simp [σZ, of_apply, cons_val_one]

/-- σZ diagonal entry equals (-1)^bit -/
lemma σZ_diag_entry (i : Fin 2) : σZ i i = (-1 : ℂ)^i.val := by
  fin_cases i
  · simp [σZ_diag_0]
  · simp [σZ_diag_1]

/-- σI diagonal entry always 1 -/
lemma σI_diag_entry (i : Fin 2) : σI i i = 1 := σI_diag i

/-- Diagonal entry of σ at index 0 or 3 -/
lemma σ_IZ_diag_entry (k : Fin 4) (hk : k = 0 ∨ k = 3) (i : Fin 2) :
    σ k i i = if k = 3 then (-1 : ℂ)^i.val else 1 := by
  rcases hk with rfl | rfl
  · simp [σ, σI_diag_entry]
  · simp [σ, σZ_diag_entry]

/-! ## Kronecker Product Diagonal Properties -/

/-- Diagonal entry of Kronecker product is product of diagonal entries -/
lemma kronecker_diag_entry {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (i : m × n) :
    (A ⊗ₖ B) i i = A i.1 i.1 * B i.2 i.2 := by
  simp only [Matrix.kroneckerMap_apply]

/-- Kronecker product of diagonal matrices is diagonal -/
lemma kronecker_diag_off_diag {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : ∀ i j, i ≠ j → A i j = 0) (hB : ∀ i j, i ≠ j → B i j = 0)
    (i j : m × n) (hij : i ≠ j) :
    (A ⊗ₖ B) i j = 0 := by
  simp only [Matrix.kroneckerMap_apply]
  by_cases h1 : i.1 = j.1
  · have h2 : i.2 ≠ j.2 := by
      intro h
      apply hij
      ext <;> assumption
    rw [hB i.2 j.2 h2, mul_zero]
  · rw [hA i.1 j.1 h1, zero_mul]

/-- Helper: σ at index 0 or 3 is diagonal -/
lemma σ_diag_off_diag (k : Fin 4) (hk : k = 0 ∨ k = 3) (i j : Fin 2) (hij : i ≠ j) :
    σ k i j = 0 := by
  rcases hk with rfl | rfl
  · exact σI_off_diag i j hij
  · exact σZ_off_diag i j hij

/-! ## Pauli String Diagonal Properties -/

/-- pauliString is diagonal when all indices are 0 or 3 -/
lemma pauliString_diag {n : ℕ} (α : MultiIndex n) (hα : ∀ k, α k = 0 ∨ α k = 3)
    (i j : Fin (2^n)) (hij : i ≠ j) : pauliString α i j = 0 := by
  induction n with
  | zero =>
    -- Fin 1 is a subsingleton, so i = j, contradicting hij
    have heq : i = j := Fin.ext (by omega)
    exact absurd heq hij
  | succ n ih =>
    simp only [pauliString]
    -- The result is (pauliString (α ∘ succ)) ⊗ₖ (σ (α 0)) composed with finPow2SuccEquiv
    simp only [Matrix.submatrix_apply]
    -- Set up helper hypotheses
    have h_rest : ∀ i j, i ≠ j → pauliString (fun k => α k.succ) i j = 0 := fun i j hij =>
      ih (fun k => α k.succ) (fun k => hα k.succ) i j hij
    have h_first : ∀ i j, i ≠ j → σ (α 0) i j = 0 := fun i j hij =>
      σ_diag_off_diag (α 0) (hα 0) i j hij
    -- finPow2SuccEquiv is an equivalence, so i ≠ j implies distinct images
    let e := finPow2SuccEquiv n
    have h_ne : e i ≠ e j := by
      intro heq
      apply hij
      exact e.injective heq
    -- Apply the Kronecker diagonality lemma
    simp only [Matrix.kroneckerMap_apply]
    by_cases h1 : (e i).1 = (e j).1
    · -- First components equal, so second components must differ
      have h2 : (e i).2 ≠ (e j).2 := by
        intro h
        apply h_ne
        exact Prod.ext h1 h
      have hzero := h_first (e i).2 (e j).2 h2
      simp only [e] at hzero
      rw [hzero, mul_zero]
    · -- First components differ
      have hzero := h_rest (e i).1 (e j).1 h1
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
      (if α k = 3 then (-1 : ℂ)^(if x.val.testBit k.val then 1 else 0) else 1) := by
  induction n with
  | zero =>
    simp [pauliString, Finset.univ_eq_empty]
  | succ n ih =>
    simp only [pauliString]
    rw [submatrix_diag_entry]
    rw [kronecker_diag_entry]
    -- Split the product
    rw [Fin.prod_univ_succ]
    -- The IH for the rest of the pauliString
    have h_rest := ih (fun k => α k.succ) (fun k => hα k.succ)
    -- The first component relates to higher bits via testBit_succ
    let fst := (finPow2SuccEquiv n x).1
    have h_fst_val : fst.val = x.val / 2 := finPow2SuccEquiv_fst n x
    -- The second component relates to bit 0
    let snd := (finPow2SuccEquiv n x).2
    have h_snd_val : snd.val = x.val % 2 := finPow2SuccEquiv_snd n x
    -- Apply the induction hypothesis
    specialize h_rest fst
    -- Rewrite LHS using h_rest and σ_IZ_diag_entry
    rw [mul_comm]
    congr 1
    · -- The σ(α 0) diagonal entry
      rw [σ_IZ_diag_entry (α 0) (hα 0) snd]
      simp only [snd, h_snd_val]
      -- Need to relate x.val % 2 to testBit 0
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
    · -- The product over i.succ
      rw [h_rest]
      apply Finset.prod_congr rfl
      intro i _
      -- testBit at position i.succ = testBit at i on x / 2
      have h_tb : x.val.testBit i.val.succ = (x.val / 2).testBit i.val :=
        Nat.testBit_succ x.val i.val
      simp only [Fin.val_succ, h_fst_val, h_tb]

/-- pauliString has zero diagonal if any component is X or Y -/
lemma pauliString_diag_zero_of_XY {n : ℕ} (α : MultiIndex n)
    (hα : ∃ k, α k = 1 ∨ α k = 2) (x : Fin (2^n)) :
    pauliString α x x = 0 := by
  obtain ⟨k, hk⟩ := hα
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [pauliString]
    simp only [Matrix.submatrix_apply]
    simp only [Matrix.kroneckerMap_apply]
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · -- k = 0: the first factor σ(α 0) has zero diagonal
      have hdiag : σ (α 0) ((finPow2SuccEquiv n x).2) ((finPow2SuccEquiv n x).2) = 0 :=
        σ_XY_diag_zero (α 0) hk _
      rw [hdiag, mul_zero]
    · -- k = j.succ: use IH on the rest
      have hzero := ih (fun (i : Fin n) => α i.succ) (finPow2SuccEquiv n x).1 j hk
      rw [hzero, zero_mul]

end Alethfeld.Quantum.PauliDiag
