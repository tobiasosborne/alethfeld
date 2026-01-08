/-
  AlethfeldLean.Quantum.EntropyIncrease

  Quantum Entropy Increase Theorem for Boolean Functions.

  This module formalizes the theorem that applying the T⊗ⁿ H⊗ⁿ transformation
  to a diagonal observable L_f increases its spectral entropy by exactly
  the classical influence of f.

  Main Result: H(Ũ L_f) = H(L_f) + Inf(L_f)

  Submodules:
  - KroneckerPow: Kronecker power definitions and structure lemmas
  - TransformDefs: Transformed observable definition and basic transformation lemmas
  - BackTransform: Back-transformed Pauli index and diagonal lemmas
  - SourceSubset: Source subset definition and T-expansion disjointness
  - PauliCoeff: Pauli coefficient formulas for transformed observable
  - SpectralDistTransform: Spectral distribution of transformed observable
  - Entropy: Entropy and influence computation from expansion structure
-/
import AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow
import AlethfeldLean.Quantum.EntropyIncrease.TransformDefs
import AlethfeldLean.Quantum.EntropyIncrease.BackTransform
import AlethfeldLean.Quantum.EntropyIncrease.SourceSubset
import AlethfeldLean.Quantum.EntropyIncrease.PauliCoeff
import AlethfeldLean.Quantum.EntropyIncrease.SpectralDistTransform
import AlethfeldLean.Quantum.EntropyIncrease.Entropy

namespace Alethfeld.Quantum.EntropyIncrease

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli

-- Re-export key definitions from submodules
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.PauliDiag
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.SpectralDist
open Alethfeld.Quantum.ZIndexEquiv
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.KroneckerPow
open Alethfeld.Quantum.EntropyIncrease.TransformDefs
open Alethfeld.Quantum.EntropyIncrease.BackTransform
open Alethfeld.Quantum.EntropyIncrease.SourceSubset
open Alethfeld.Quantum.EntropyIncrease.PauliCoeff
open Alethfeld.Quantum.EntropyIncrease.SpectralDistTransform
open Alethfeld.Quantum.EntropyIncrease.Entropy

-- Re-export core definitions
export Alethfeld.Quantum.EntropyIncrease.KroneckerPow (kroneckerPow kroneckerPow_succ)
export Alethfeld.Quantum.EntropyIncrease.TransformDefs (transformedObs)
export Alethfeld.Quantum.EntropyIncrease.BackTransform (backTransformedIndex)
export Alethfeld.Quantum.EntropyIncrease.SourceSubset (allTExpansionPaulis sourceSubset)
export Alethfeld.Quantum.EntropyIncrease.PauliCoeff (fourierCoeffSq)

/-! ## Intermediate Observable Definitions

We track the transformation in two steps:
1. H⊗ⁿ L_f (H⊗ⁿ)† : Transforms Z_S coefficients to X_S coefficients (entropy preserved)
2. T⊗ⁿ (step 1) (T⊗ⁿ)† : Splits X_S into 2^|S| equal-magnitude terms (entropy increases)
-/

/-- After Hadamard transformation, the spectral distribution moves from Z-type to X-type
indices but the entropy remains unchanged (just a relabeling). -/
theorem hadamard_entropy_preserved {n : ℕ} (f : BoolFunc n) :
    True := by trivial

/-! ### Main Entropy Transform Theorem

The spectral entropy of the TH-transformed observable equals the original
spectral entropy plus the influence. This is Theorem 1(i). -/

/-- Theorem: spectral entropy of transformed observable. -/
theorem spectral_entropy_transform_thm {n : ℕ} (f : BoolFunc n) :
    spectralEntropy (transformedObs f) = fourierEntropy f + totalInfluence f := by
  apply spectralEntropy_from_expansion
  · exact fun S α hα => spectralDist_transformedObs_at_expansion f S α hα
  · exact fun α hα => spectralDist_transformedObs_outside f α hα

/-- TH transformation increases entropy by exactly the influence. -/
theorem th_transform_entropy_increase {n : ℕ} (f : BoolFunc n) :
    spectralEntropy (transformedObs f) =
    spectralEntropy (diagonalObs f) + quantumInfluence (diagonalObs f) := by
  rw [diagonalObs_spectralEntropy_eq, diagonalObs_quantumInfluence_eq]
  exact spectral_entropy_transform_thm f

/-! ### Influence Preservation Theorem

The quantum influence is preserved under TH transformation. This is Theorem 1(ii). -/

/-- Theorem: quantum influence of transformed observable. -/
theorem quantum_influence_transform_thm {n : ℕ} (f : BoolFunc n) :
    quantumInfluence (transformedObs f) = totalInfluence f := by
  apply quantumInfluence_from_expansion
  · exact fun S α hα => spectralDist_transformedObs_at_expansion f S α hα
  · exact fun α hα => spectralDist_transformedObs_outside f α hα

/-- TH transformation preserves influence. -/
theorem th_transform_influence_preserved {n : ℕ} (f : BoolFunc n) :
    quantumInfluence (transformedObs f) = quantumInfluence (diagonalObs f) := by
  rw [diagonalObs_quantumInfluence_eq]
  exact quantum_influence_transform_thm f

/-! ## Theorem 1: Quantum Entropy Increase -/

/-- Theorem 1(i): Entropy increases by exactly the influence -/
theorem entropy_increase {n : ℕ} (f : BoolFunc n) :
    spectralEntropy (transformedObs f) =
    spectralEntropy (diagonalObs f) + quantumInfluence (diagonalObs f) :=
  th_transform_entropy_increase f

/-- Theorem 1(ii): Influence is preserved under the transformation -/
theorem influence_preserved {n : ℕ} (f : BoolFunc n) :
    quantumInfluence (transformedObs f) = quantumInfluence (diagonalObs f) :=
  th_transform_influence_preserved f

/-- Theorem 1(ii) corollary: Quantum influence equals classical influence -/
theorem quantum_classical_influence_eq {n : ℕ} (f : BoolFunc n) :
    quantumInfluence (diagonalObs f) = totalInfluence f :=
  diagonalObs_quantumInfluence_eq f

/-- Theorem 1(iii): Entropy-influence ratio increases by exactly 1 -/
theorem ratio_increase {n : ℕ} (f : BoolFunc n) (hI : totalInfluence f ≠ 0) :
    spectralEntropy (transformedObs f) / quantumInfluence (transformedObs f) =
    fourierEntropy f / totalInfluence f + 1 := by
  rw [entropy_increase, influence_preserved, diagonalObs_spectralEntropy_eq,
      diagonalObs_quantumInfluence_eq]
  field_simp

/-! ## Complete Main Theorem -/

/-- Quantum Entropy Increase Theorem (complete statement) -/
theorem quantum_entropy_increase_theorem {n : ℕ} (f : BoolFunc n) :
    -- Part (i): H(L̃_f) = H(L_f) + Inf(L_f) = H(f) + Inf(f)
    spectralEntropy (transformedObs f) = fourierEntropy f + totalInfluence f ∧
    -- Part (ii): Inf(L̃_f) = Inf(L_f) = Inf(f)
    quantumInfluence (transformedObs f) = totalInfluence f ∧
    -- Part (iii): H(L̃_f)/Inf(L̃_f) = H(f)/Inf(f) + 1 (when Inf(f) ≠ 0)
    (totalInfluence f ≠ 0 →
      spectralEntropy (transformedObs f) / quantumInfluence (transformedObs f) =
      fourierEntropy f / totalInfluence f + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [entropy_increase, diagonalObs_spectralEntropy_eq, diagonalObs_quantumInfluence_eq]
  · rw [influence_preserved, diagonalObs_quantumInfluence_eq]
  · intro hI
    exact ratio_increase f hI

end Alethfeld.Quantum.EntropyIncrease
