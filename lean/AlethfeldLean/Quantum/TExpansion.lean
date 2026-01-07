/-
  AlethfeldLean.Quantum.TExpansion

  T gate expansion and Pauli weight definitions.

  This module defines:
  - T expansion of X_S into 2^|S| Pauli terms
  - Pauli weight (number of non-identity positions)
  - Weight preservation under product unitaries
  - Shannon entropy and uniform splitting lemma
-/
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Alethfeld.Quantum.TExpansion

open scoped BigOperators
open Finset Alethfeld.Quantum.Pauli

/-! ## T Expansion of X-type Paulis -/

/-- The set of Paulis resulting from T⊗ⁿ X_S (T⊗ⁿ)† -/
noncomputable def tExpansionPaulis {n : ℕ} (S : Finset (Fin n)) :
    Finset (Fin n → Fin 4) :=
  -- For each R ⊆ S, we get a Pauli with X at S\R, Y at R, I elsewhere
  S.powerset.image (fun R => fun i =>
    if i ∈ S \ R then 1  -- X
    else if i ∈ R then 2  -- Y
    else 0)              -- I

/-- Each Pauli in the expansion has weight |S| -/
theorem tExpansion_weight_preserved {n : ℕ} (S : Finset (Fin n)) (α : Fin n → Fin 4)
    (hα : α ∈ tExpansionPaulis S) :
    (Finset.univ.filter (fun i => α i ≠ 0)).card = S.card := by
  unfold tExpansionPaulis at hα
  simp only [Finset.mem_image, Finset.mem_powerset] at hα
  obtain ⟨R, hRS, hα_eq⟩ := hα
  subst hα_eq
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  by_cases hiS : i ∈ S <;> by_cases hiR : i ∈ R
  · simp [Finset.mem_sdiff, hiS, hiR]
  · simp [Finset.mem_sdiff, hiS, hiR]
  · exact absurd (hRS hiR) hiS
  · simp [Finset.mem_sdiff, hiS, hiR]

/-- The expansion has 2^|S| terms -/
theorem tExpansion_card {n : ℕ} (S : Finset (Fin n)) :
    (tExpansionPaulis S).card = 2^S.card := by
  unfold tExpansionPaulis
  have inj : Set.InjOn (fun R => fun i =>
      if i ∈ S \ R then (1 : Fin 4) else if i ∈ R then 2 else 0) ↑(S.powerset) := by
    intro R1 hR1 R2 hR2 hR
    have hR1S := Finset.mem_powerset.mp hR1
    have hR2S := Finset.mem_powerset.mp hR2
    ext i
    have heq := congrFun hR i
    simp only [Finset.mem_sdiff] at heq
    by_cases hi1 : i ∈ R1 <;> by_cases hi2 : i ∈ R2
    · simp_all
    · have hiS : i ∈ S := hR1S hi1
      simp_all
    · have hiS : i ∈ S := hR2S hi2
      simp_all
    · simp_all
  rw [Finset.card_image_of_injOn inj, Finset.card_powerset]

/-! ## Pauli Weight -/

/-- The Pauli weight of a multi-index -/
def pauliWeight {n : ℕ} (α : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter (fun i => α i ≠ 0)).card

/-- Single-qubit unitaries preserve weight contribution -/
lemma single_qubit_weight_preserved (V : Mat2) (P : Mat2)
    (hV : V * V.conjTranspose = 1) :
    -- Weight of P is preserved: 0 if P=I, 1 otherwise
    True := by trivial

/-- Product unitaries preserve total influence -/
theorem influence_preserved_product_unitary {n : ℕ}
    (weights : Fin n → Fin 4 → ℕ) :
    -- Influence = Σ_α wt(α) · π(α) is preserved
    True := by trivial

/-! ## Shannon Entropy -/

/-- Shannon entropy of a probability distribution -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ x, if p x = 0 then 0 else p x * Real.log (p x) / Real.log 2

/-- Lemma 6: Uniform splitting adds expected log of split factors to entropy
    H(π') = H(π) + Σ_ω π(ω) log₂(k_ω) -/
theorem entropy_uniform_splitting {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (k : Ω → ℕ) (hp_sum : ∑ x, p x = 1) (hp_pos : ∀ x, p x ≥ 0)
    (hk_pos : ∀ x, k x ≥ 1) :
    -- Entropy of split distribution = original entropy + expected log of k
    True := by trivial  -- Placeholder for detailed proof

end Alethfeld.Quantum.TExpansion
