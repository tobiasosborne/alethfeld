/-
  AlethfeldLean.Quantum.EntropyIncrease.Entropy

  Entropy and influence computation from expansion structure.
-/
import AlethfeldLean.Quantum.BoolFunc
import AlethfeldLean.Quantum.SpectralDist
import AlethfeldLean.Quantum.ZIndexEquiv
import AlethfeldLean.Quantum.TExpansion
import AlethfeldLean.Quantum.EntropyIncrease.TransformDefs
import AlethfeldLean.Quantum.EntropyIncrease.SourceSubset
import AlethfeldLean.Quantum.EntropyIncrease.PauliCoeff
import AlethfeldLean.Quantum.EntropyIncrease.SpectralDistTransform

namespace Alethfeld.Quantum.EntropyIncrease.Entropy

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.SpectralDist
open Alethfeld.Quantum.ZIndexEquiv
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.TransformDefs
open Alethfeld.Quantum.EntropyIncrease.SourceSubset
open Alethfeld.Quantum.EntropyIncrease.PauliCoeff
open Alethfeld.Quantum.EntropyIncrease.SpectralDistTransform

/-! ### Computing Entropy and Influence from Spectral Distribution Structure

Given the spectral distribution characterization, we can compute entropy and influence
by summing over the T-expansion structure. -/

/-- Entropy of transformed observable computed from spectral distribution structure. -/
lemma spectralEntropy_from_expansion {n : ℕ} (f : BoolFunc n)
    (h_at : ∀ S α, α ∈ tExpansionPaulis S →
      spectralDist (transformedObs f) α = fourierCoeffSq f S / 2^S.card)
    (h_outside : ∀ α, α ∉ allTExpansionPaulis →
      spectralDist (transformedObs f) α = 0) :
    spectralEntropy (transformedObs f) = fourierEntropy f + totalInfluence f := by
  unfold spectralEntropy fourierEntropy totalInfluence
  have hsplit : ∑ P : Fin n → Fin 4,
      (let prob := spectralDist (transformedObs f) P
       if prob = 0 then 0 else prob * Real.log prob / Real.log 2) =
      ∑ P ∈ allTExpansionPaulis,
        (let prob := spectralDist (transformedObs f) P
         if prob = 0 then 0 else prob * Real.log prob / Real.log 2) +
      ∑ P ∈ (Finset.univ \ allTExpansionPaulis),
        (let prob := spectralDist (transformedObs f) P
         if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    simp only [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hsplit]
  have h_outside_zero : ∑ P ∈ (Finset.univ \ allTExpansionPaulis),
      (let prob := spectralDist (transformedObs f) P
       if prob = 0 then 0 else prob * Real.log prob / Real.log 2) = 0 := by
    apply Finset.sum_eq_zero
    intro α hα
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hα
    simp only [h_outside α hα, ↓reduceIte]
  rw [h_outside_zero, add_zero]
  unfold allTExpansionPaulis
  rw [Finset.sum_biUnion]
  · have h_entropy_decomp : ∀ S : Finset (Fin n),
        ∑ P ∈ tExpansionPaulis S,
          (let prob := spectralDist (transformedObs f) P
           if prob = 0 then 0 else prob * Real.log prob / Real.log 2) =
        2 ^ S.card * (
          let prob := fourierCoeffSq f S / 2 ^ S.card
          if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
      intro S
      have h_terms_eq : ∀ P ∈ tExpansionPaulis S,
          (let prob := spectralDist (transformedObs f) P
           if prob = 0 then 0 else prob * Real.log prob / Real.log 2) =
          (let prob := fourierCoeffSq f S / 2 ^ S.card
           if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
        intro P hP
        simp only [h_at S P hP]
      calc ∑ P ∈ tExpansionPaulis S,
            (let prob := spectralDist (transformedObs f) P
             if prob = 0 then 0 else prob * Real.log prob / Real.log 2)
          = ∑ P ∈ tExpansionPaulis S,
              (let prob := fourierCoeffSq f S / 2 ^ S.card
               if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
            apply Finset.sum_congr rfl h_terms_eq
        _ = (tExpansionPaulis S).card *
              (let prob := fourierCoeffSq f S / 2 ^ S.card
               if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
            rw [Finset.sum_const]; simp only [nsmul_eq_mul]
        _ = 2 ^ S.card *
              (let prob := fourierCoeffSq f S / 2 ^ S.card
               if prob = 0 then 0 else prob * Real.log prob / Real.log 2) := by
            rw [tExpansion_card S]; norm_cast
    simp_rw [h_entropy_decomp]
    have h_term_simp : ∀ S : Finset (Fin n),
        (2 : ℝ) ^ S.card * (
          let prob := fourierCoeffSq f S / 2 ^ S.card
          if prob = 0 then 0 else prob * Real.log prob / Real.log 2) =
        (let c := fourierCoeff f S ^ 2
         if c = 0 then 0 else c * Real.log c / Real.log 2) -
        (S.card : ℝ) * fourierCoeff f S ^ 2 := by
      intro S
      unfold fourierCoeffSq
      have h2_ne : (2 : ℝ)^S.card ≠ 0 := pow_ne_zero S.card (by norm_num)
      have hlog2_ne : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      by_cases hc : fourierCoeff f S ^ 2 = 0
      · simp only [hc, zero_div, ↓reduceIte, mul_zero, sub_zero]
      · have h_prob_ne : fourierCoeff f S ^ 2 / 2 ^ S.card ≠ 0 := by
          rw [ne_eq, div_eq_zero_iff]
          push_neg
          exact ⟨hc, h2_ne⟩
        simp only [hc, h_prob_ne, ↓reduceIte]
        have hlog_div : Real.log (fourierCoeff f S ^ 2 / 2 ^ S.card) =
            Real.log (fourierCoeff f S ^ 2) - S.card * Real.log 2 := by
          rw [Real.log_div (by exact hc) h2_ne]
          simp only [Real.log_pow]
        rw [hlog_div]
        have h2_pos : (2 : ℝ)^S.card > 0 := pow_pos (by norm_num) _
        field_simp
    simp_rw [h_term_simp]
    rw [Finset.sum_sub_distrib]
    ring
  · intro S₁ _ S₂ _ hne
    exact tExpansionPaulis_pairwiseDisjoint S₁ S₂ hne

/-- Influence of transformed observable computed from spectral distribution structure. -/
lemma quantumInfluence_from_expansion {n : ℕ} (f : BoolFunc n)
    (h_at : ∀ S α, α ∈ tExpansionPaulis S →
      spectralDist (transformedObs f) α = fourierCoeffSq f S / 2^S.card)
    (h_outside : ∀ α, α ∉ allTExpansionPaulis →
      spectralDist (transformedObs f) α = 0) :
    quantumInfluence (transformedObs f) = totalInfluence f := by
  unfold quantumInfluence totalInfluence
  have hsplit : ∑ P : Fin n → Fin 4, pauliWeight P * spectralDist (transformedObs f) P =
      ∑ P ∈ allTExpansionPaulis, pauliWeight P * spectralDist (transformedObs f) P +
      ∑ P ∈ (Finset.univ \ allTExpansionPaulis), pauliWeight P * spectralDist (transformedObs f) P := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    simp only [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hsplit]
  have h_outside_zero : ∑ P ∈ (Finset.univ \ allTExpansionPaulis),
      pauliWeight P * spectralDist (transformedObs f) P = 0 := by
    apply Finset.sum_eq_zero
    intro α hα
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hα
    rw [h_outside α hα, mul_zero]
  rw [h_outside_zero, add_zero]
  unfold allTExpansionPaulis
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro S _
    have h_weight : ∀ α ∈ tExpansionPaulis S, pauliWeight α = S.card :=
      fun α hα => tExpansion_weight_preserved S α hα
    have h_term_eq : ∀ α ∈ tExpansionPaulis S,
        (pauliWeight α : ℝ) * spectralDist (transformedObs f) α =
        (S.card : ℝ) * (fourierCoeffSq f S / 2^S.card) := by
      intro α hα
      rw [h_weight α hα, h_at S α hα]
    rw [Finset.sum_congr rfl h_term_eq]
    simp only [Finset.sum_const]
    rw [tExpansion_card S]
    simp only [nsmul_eq_mul]
    unfold fourierCoeffSq
    have h2_ne : (2 : ℝ)^S.card ≠ 0 := pow_ne_zero S.card (by norm_num)
    field_simp
    push_cast
    ring
  · intro S₁ _ S₂ _ hne
    exact tExpansionPaulis_pairwiseDisjoint S₁ S₂ hne

end Alethfeld.Quantum.EntropyIncrease.Entropy
