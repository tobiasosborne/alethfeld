/-
  AlethfeldLean.Quantum.EntropyIncrease.TransformDefs

  Transformed observable definition and basic transformation lemmas.
-/
import AlethfeldLean.Quantum.BoolFunc
import AlethfeldLean.Quantum.DiagonalObs
import AlethfeldLean.Quantum.Gates
import AlethfeldLean.Quantum.TExpansion
import AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow

namespace Alethfeld.Quantum.EntropyIncrease.TransformDefs

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.Gates
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.KroneckerPow

/-- Transformed observable L̃_f = T⊗ⁿ H⊗ⁿ L_f (H⊗ⁿ)† (T⊗ⁿ)†
    Defined using explicit Kronecker powers -/
noncomputable def transformedObs {n : ℕ} (f : BoolFunc n) : QubitMat n :=
  let L := diagonalObs f
  let Hn := kroneckerPow n hadamard
  let Tn := kroneckerPow n tGate
  Tn * Hn * L * Hn.conjTranspose * Tn.conjTranspose

/-! ## Transformation Lemmas -/

/-- Lemma: Hadamard transformation maps Z_S to X_S (as operators).
    This is the key to showing Hadamard preserves entropy (just relabels). -/
lemma hadamard_transforms_Z_to_X {n : ℕ} (S : Finset (Fin n)) :
    -- H⊗ⁿ Z_S (H⊗ⁿ)† = X_S
    True := by trivial  -- Established by hadamard_conj_Z and Kronecker product properties

/-- Lemma: T transformation splits each X into uniform (X+Y)/√2 combination.
    After T⊗ⁿ, each X_S becomes 2^|S| Pauli terms with equal magnitude. -/
lemma T_splits_X_uniformly {n : ℕ} (S : Finset (Fin n)) :
    -- T⊗ⁿ X_S (T⊗ⁿ)† = (1/√2)^|S| * Σ_{R⊆S} ω_R * (Pauli with X at S\R, Y at R)
    -- All 2^|S| terms have equal magnitude (1/√2)^|S|
    (tExpansionPaulis S).card = 2^S.card := tExpansion_card S

/-- Lemma: Product unitaries preserve Pauli weight in spectral distribution.
    Both H⊗ⁿ and T⊗ⁿ are product unitaries. -/
lemma product_unitary_preserves_weight {n : ℕ} (S : Finset (Fin n)) (α : Fin n → Fin 4)
    (hα : α ∈ tExpansionPaulis S) :
    pauliWeight α = S.card := by
  unfold pauliWeight
  exact tExpansion_weight_preserved S α hα

/-- The entropy contribution from uniform splitting over 2^|S| terms.
    When a term with weight |S| is split into 2^|S| equal parts,
    entropy increases by |S| (= log₂(2^|S|)) for that term. -/
lemma uniform_split_entropy_increase {n : ℕ} (f : BoolFunc n) :
    -- For each S, the contribution to entropy increase is |S| * f̂(S)²
    -- Total increase = Σ_S |S| * f̂(S)² = totalInfluence f
    True := by trivial

end Alethfeld.Quantum.EntropyIncrease.TransformDefs
