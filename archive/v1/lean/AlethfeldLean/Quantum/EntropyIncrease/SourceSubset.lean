/-
  AlethfeldLean.Quantum.EntropyIncrease.SourceSubset

  Source subset definition and T-expansion disjointness lemmas.
-/
import AlethfeldLean.Quantum.TExpansion

namespace Alethfeld.Quantum.EntropyIncrease.SourceSubset

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.TExpansion

/-! ### Finding the source subset for a T-expansion Pauli

Each Pauli α in the T-expansion comes from exactly one subset S.
The subset S is determined by the positions where α has non-identity Pauli (X or Y).
-/

/-- The set of all T-expansion Paulis over all subsets S.
    This is the support of the spectral distribution of transformedObs f. -/
noncomputable def allTExpansionPaulis {n : ℕ} : Finset (Fin n → Fin 4) :=
  Finset.univ.biUnion tExpansionPaulis

/-- Given a Pauli index α in allTExpansionPaulis, find the unique S such that α ∈ tExpansionPaulis S.
    The subset S is exactly the positions where α i ∈ {1, 2} (X or Y). -/
noncomputable def sourceSubset {n : ℕ} (α : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.filter (fun i => α i = 1 ∨ α i = 2) Finset.univ

/-- For α ∈ tExpansionPaulis S, the sourceSubset equals S. -/
lemma sourceSubset_of_tExpansion {n : ℕ} (S : Finset (Fin n)) (α : Fin n → Fin 4)
    (hα : α ∈ tExpansionPaulis S) :
    sourceSubset α = S := by
  unfold tExpansionPaulis at hα
  simp only [Finset.mem_image, Finset.mem_powerset] at hα
  obtain ⟨R, hRS, hα_eq⟩ := hα
  subst hα_eq
  unfold sourceSubset
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with h1 | h2
    · -- α i = 1 (X case): if i ∈ S \ R then i ∈ S
      simp only [Finset.mem_sdiff] at h1
      by_cases hiS : i ∈ S
      · exact hiS
      · by_cases hiR : i ∈ R
        · simp [hiR] at h1
        · simp [hiS, hiR] at h1
    · -- α i = 2 (Y case): i ∈ R implies i ∈ S (since R ⊆ S)
      simp only [Finset.mem_sdiff] at h2
      by_cases hiR : i ∈ R
      · exact hRS hiR
      · -- When i ∉ R, the value is either 1 (if i ∈ S) or 0 (if i ∉ S), never 2
        simp only [hiR, ↓reduceIte] at h2
        by_cases hiS : i ∈ S <;> simp_all
  · intro hiS
    by_cases hiR : i ∈ R
    · right  -- α i = 2 (Y)
      simp [Finset.mem_sdiff, hiR]
    · left  -- α i = 1 (X)
      simp [Finset.mem_sdiff, hiS, hiR]

/-- T-expansion Paulis for different subsets are disjoint.
    If α ∈ tExpansionPaulis S₁ and α ∈ tExpansionPaulis S₂, then S₁ = S₂.
    This follows from sourceSubset_of_tExpansion: sourceSubset α = S for α ∈ tExpansionPaulis S. -/
lemma tExpansionPaulis_pairwiseDisjoint {n : ℕ} (S₁ S₂ : Finset (Fin n)) (hne : S₁ ≠ S₂) :
    Disjoint (tExpansionPaulis S₁) (tExpansionPaulis S₂) := by
  rw [Finset.disjoint_left]
  intro α hα₁ hα₂
  have h1 := sourceSubset_of_tExpansion S₁ α hα₁
  have h2 := sourceSubset_of_tExpansion S₂ α hα₂
  rw [h1] at h2
  exact hne h2

/-- PairwiseDisjoint version for use with sum_biUnion. -/
lemma tExpansionPaulis_pairwise {n : ℕ} :
    (Set.univ : Set (Finset (Fin n))).PairwiseDisjoint tExpansionPaulis := by
  intro S₁ _ S₂ _ hne
  exact tExpansionPaulis_pairwiseDisjoint S₁ S₂ hne

end Alethfeld.Quantum.EntropyIncrease.SourceSubset
