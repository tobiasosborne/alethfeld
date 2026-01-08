/-
  AlethfeldLean.Quantum.EntropyIncrease.BackTransform

  Back-transformed Pauli index and diagonal lemmas.
-/
import AlethfeldLean.Quantum.PauliDiag
import AlethfeldLean.Quantum.Gates
import AlethfeldLean.Quantum.TExpansion
import AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow

namespace Alethfeld.Quantum.EntropyIncrease.BackTransform

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.PauliDiag
open Alethfeld.Quantum.Gates
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.KroneckerPow

/-! ### Back-Transformation Maps Z to X

The key technical lemma: when a Pauli string with a Z component is back-transformed
through the TH gates, the Z position becomes X:
- T† σZ T = σZ (Z is preserved by T conjugation)
- H† σZ H = σX (Hadamard maps Z to X)

Therefore the back-transformed Pauli has an X component, giving zero diagonal. -/

/-- The "back-transformed" Pauli index for TH conjugation.
    At each position: I→I, X→(complex), Y→(complex), Z→X -/
def backTransformedIndex {n : ℕ} (α : Fin n → Fin 4) : Fin n → Fin 4 :=
  fun i =>
    match α i with
    | 0 => 0  -- I → I (H† T† I T H = I)
    | 1 => 1  -- X → X (approximately, for T† X T gives combo, then H)
    | 2 => 2  -- Y → Y (approximately)
    | 3 => 1  -- Z → X (H† T† Z T H = H† Z H = X) ← KEY FACT

/-- If α has a Z component, backTransformedIndex has an X component at that position -/
lemma backTransformedIndex_Z_to_X {n : ℕ} (α : Fin n → Fin 4) (i : Fin n) (hi : α i = 3) :
    backTransformedIndex α i = 1 := by
  simp only [backTransformedIndex, hi]

/-- If α has a Z component, backTransformedIndex has an X or Y component somewhere -/
lemma backTransformedIndex_has_XY_of_Z {n : ℕ} (α : Fin n → Fin 4) (hZ : ∃ i, α i = 3) :
    ∃ i, backTransformedIndex α i = 1 ∨ backTransformedIndex α i = 2 := by
  obtain ⟨i, hi⟩ := hZ
  use i
  left
  exact backTransformedIndex_Z_to_X α i hi

/-! ### Back-Transformation Diagonal Structure

The key mathematical fact: when a Pauli string with a Z component is back-transformed
through TH gates, the resulting matrix has zero diagonal.

This follows from:
1. At position i with σZ: H† T† σZ T H = H† σZ H = σX (off-diagonal)
2. Kronecker product with an off-diagonal factor has zero diagonal
3. The submatrix reindexing preserves the zero-diagonal property

The proof uses the recursive structure of pauliString and kroneckerPow. -/

/-- Key lemma: Back-transformed Pauli string has zero diagonal when original has Z.

This captures the central mathematical fact for the spectral distribution theorem:
when pauliString α has a Z component (α i = 3), the matrix
  (kroneckerPow n hadamard)† (kroneckerPow n tGate)† (pauliString α) (kroneckerPow n tGate) (kroneckerPow n hadamard)
has zero diagonal.

Proof idea:
- At position i: H†ᵢ T†ᵢ σZ Tᵢ Hᵢ = H†ᵢ σZ Hᵢ = σX (zero diagonal)
- Kronecker product structure: if one factor has zero diagonal, the product has zero diagonal
- The submatrix reindexing (via finPow2SuccEquiv) preserves diagonal structure -/
lemma backTransformed_pauli_diag_zero_of_Z {n : ℕ} (α : Fin n → Fin 4) (hZ : ∃ i, α i = 3) :
    ∀ x, ((kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose *
          (pauliString α).conjTranspose * (kroneckerPow n tGate) *
          (kroneckerPow n hadamard)) x x = 0 := by
  -- The proof proceeds by induction on n.
  -- Key insight: the conjugation acts componentwise on Kronecker products, and
  -- at position i where α_i = 3, we get H† T† σZ T H = H† σZ H = σX (zero diagonal).
  induction n with
  | zero =>
    -- For n = 0, no position i can exist, so hZ is vacuous
    intro x_goal
    obtain ⟨i, _⟩ := hZ
    exact Fin.elim0 i
  | succ n ih =>
    -- For n + 1, the Kronecker structure gives:
    -- H† T† P† T H = (H_rest† T_rest† P_rest† T_rest H_rest ⊗ h† t† p† t h).submatrix e e
    -- where p = σ(α 0), and rest refers to indices 1..n
    intro x_goal
    obtain ⟨i, hi⟩ := hZ
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · -- Case 1: Z at position 0 (i = 0)
      have h0 : α 0 = 3 := hi
      -- Key fact: h† t† σZ t h = σX, and σX has zero diagonal
      have h_σZ_transform : hadamard.conjTranspose * tGate.conjTranspose * σZ * tGate * hadamard = σX := by
        have step1 : tGate.conjTranspose * σZ * tGate = σZ :=
          Alethfeld.Quantum.Gates.tgate_inv_conj_Z
        have step2 : hadamard.conjTranspose * σZ * hadamard = σX :=
          Alethfeld.Quantum.Gates.hadamard_inv_conj_Z
        calc hadamard.conjTranspose * tGate.conjTranspose * σZ * tGate * hadamard
            = hadamard.conjTranspose * (tGate.conjTranspose * σZ * tGate) * hadamard := by
              simp only [Matrix.mul_assoc]
          _ = hadamard.conjTranspose * σZ * hadamard := by rw [step1]
          _ = σX := step2
      have h_σX_diag : ∀ k : Fin 2, σX k k = 0 := σX_diag_zero
      -- σZ.conjTranspose = σZ (σZ is Hermitian)
      have hσZ_herm : σZ.conjTranspose = σZ := σZ_hermitian
      -- α 0 = 3, so σ (α 0) = σZ
      have hp_eq : σ (α 0) = σZ := by simp only [h0, σ]
      have hp_conj : (σ (α 0)).conjTranspose = σZ := by rw [hp_eq, hσZ_herm]
      -- The single-qubit factor is h† t† σZ t h = σX
      have h_single : hadamard.conjTranspose * tGate.conjTranspose * (σ (α 0)).conjTranspose *
          tGate * hadamard = σX := by
        rw [hp_conj]
        exact h_σZ_transform
      -- Use conjugation_factors_through_kronecker
      have h_factor := conjugation_factors_through_kronecker
        (kroneckerPow n hadamard) (kroneckerPow n tGate)
        (pauliString (fun m => α m.succ)) hadamard tGate (σ (α 0))
      -- The full matrix equals (rest_factor ⊗ₖ σX).submatrix e e
      -- Rewrite the goal to use the factorization
      simp only [kroneckerPow_succ, pauliString]
      rw [h_factor]
      -- Now goal is: ((rest ⊗ₖ σX).submatrix e e) x x = 0
      simp only [Matrix.submatrix_apply]
      rw [kronecker_diag_entry]
      rw [h_single]
      rw [h_σX_diag ((finPow2SuccEquiv n x_goal).2)]
      ring
    · -- Case 2: Z at position > 0 (i = j.succ for some j)
      have hZ' : ∃ k, (fun (m : Fin n) => α m.succ) k = 3 := ⟨j, hi⟩
      -- By IH, the rest factor has zero diagonal
      have h_ih := ih (fun (m : Fin n) => α m.succ) hZ'
      -- Use conjugation_factors_through_kronecker
      have h_factor := conjugation_factors_through_kronecker
        (kroneckerPow n hadamard) (kroneckerPow n tGate)
        (pauliString (fun m => α m.succ)) hadamard tGate (σ (α 0))
      -- Rewrite the goal to use the factorization
      simp only [kroneckerPow_succ, pauliString]
      rw [h_factor]
      -- Now goal is: ((rest ⊗ₖ single).submatrix e e) x x = 0
      simp only [Matrix.submatrix_apply]
      rw [kronecker_diag_entry]
      rw [h_ih (finPow2SuccEquiv n x_goal).1]
      ring

end Alethfeld.Quantum.EntropyIncrease.BackTransform
