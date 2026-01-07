/-
  AlethfeldLean.Quantum.EntropyIncrease.SpectralDistTransform

  Spectral distribution of transformed observable.
-/
import AlethfeldLean.Quantum.BoolFunc
import AlethfeldLean.Quantum.PauliDiag
import AlethfeldLean.Quantum.DiagonalObs
import AlethfeldLean.Quantum.SpectralDist
import AlethfeldLean.Quantum.ZIndexEquiv
import AlethfeldLean.Quantum.Gates
import AlethfeldLean.Quantum.TExpansion
import AlethfeldLean.Quantum.EntropyIncrease.KroneckerPow
import AlethfeldLean.Quantum.EntropyIncrease.TransformDefs
import AlethfeldLean.Quantum.EntropyIncrease.BackTransform
import AlethfeldLean.Quantum.EntropyIncrease.SourceSubset
import AlethfeldLean.Quantum.EntropyIncrease.PauliCoeff

namespace Alethfeld.Quantum.EntropyIncrease.SpectralDistTransform

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Real Alethfeld.Quantum.Pauli
open Alethfeld.Quantum.BoolFunc
open Alethfeld.Quantum.PauliDiag
open Alethfeld.Quantum.DiagonalObs
open Alethfeld.Quantum.SpectralDist
open Alethfeld.Quantum.ZIndexEquiv
open Alethfeld.Quantum.Gates
open Alethfeld.Quantum.TExpansion
open Alethfeld.Quantum.EntropyIncrease.KroneckerPow
open Alethfeld.Quantum.EntropyIncrease.TransformDefs
open Alethfeld.Quantum.EntropyIncrease.BackTransform
open Alethfeld.Quantum.EntropyIncrease.SourceSubset
open Alethfeld.Quantum.EntropyIncrease.PauliCoeff

/-! ### Back-Transformed Pauli Diagonal for T-Expansion

For α ∈ tExpansionPaulis S, the back-transformed Pauli H† T† α† T H has diagonal
equal to (1/√2)^|S| times the diagonal of Z_S. -/

/-- Back-transformed Pauli diagonal for T-expansion indices. -/
lemma backTransformed_pauli_diag_of_tExpansion {n : ℕ} (S : Finset (Fin n))
    (α : Fin n → Fin 4) (hα : α ∈ tExpansionPaulis S) (x : Fin (2^n)) :
    ((kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose *
      (pauliString α).conjTranspose * (kroneckerPow n tGate) *
      (kroneckerPow n hadamard)) x x =
    (1 / Real.sqrt 2 : ℂ)^S.card * pauliZ_S S x x := by
  induction n with
  | zero =>
    have hS_empty : S = ∅ := by ext i; exact i.elim0
    simp only [hS_empty, Finset.card_empty, pow_zero, one_mul]
    simp only [kroneckerPow, pauliString, pauliZ_S]
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val_fin_one, star_one]
    simp [Fintype.sum_unique]
  | succ n ih =>
    unfold tExpansionPaulis at hα
    simp only [Finset.mem_image, Finset.mem_powerset] at hα
    obtain ⟨R, hRS, hα_eq⟩ := hα

    have h_factor := conjugation_factors_through_kronecker
      (kroneckerPow n hadamard) (kroneckerPow n tGate)
      (pauliString (fun m => α m.succ)) hadamard tGate (σ (α 0))

    simp only [kroneckerPow_succ, pauliString]
    rw [h_factor]
    simp only [Matrix.submatrix_apply]
    rw [kronecker_diag_entry]

    by_cases h0S : (0 : Fin (n + 1)) ∈ S
    · -- Case: 0 ∈ S, so α 0 ∈ {1, 2}
      have hα0_XY : α 0 = 1 ∨ α 0 = 2 := by
        subst hα_eq
        by_cases h0R : (0 : Fin (n + 1)) ∈ R
        · right; simp [h0R]
        · left; simp [h0S, h0R, Finset.mem_sdiff]
      have h_single_diag : (hadamard.conjTranspose * tGate.conjTranspose *
          (σ (α 0)).conjTranspose * tGate * hadamard)
          (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2 =
          (1 / Real.sqrt 2 : ℂ) * σZ (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2 := by
        cases hα0_XY with
        | inl h1 =>
          have hp_eq : σ (α 0) = σX := by simp [h1, σ]
          have hp_conj : (σ (α 0)).conjTranspose = σX := by
            rw [hp_eq]; exact σX_hermitian
          rw [hp_conj, hadamard_conjTranspose]
          have h_assoc : hadamard * tGate.conjTranspose * σX * tGate * hadamard =
              hadamard * (tGate.conjTranspose * σX * tGate) * hadamard := by
            simp only [Matrix.mul_assoc]
          simp only [h_assoc]
          rw [Alethfeld.Quantum.Gates.hadamard_tgate_inv_conj_X]
          simp only [smul_apply, smul_eq_mul]
          rw [Alethfeld.Quantum.Gates.diag_Z_plus_Y]
        | inr h2 =>
          have hp_eq : σ (α 0) = σY := by simp [h2, σ]
          have hp_conj : (σ (α 0)).conjTranspose = σY := by
            rw [hp_eq]; exact σY_hermitian
          rw [hp_conj, hadamard_conjTranspose]
          have h_assoc : hadamard * tGate.conjTranspose * σY * tGate * hadamard =
              hadamard * (tGate.conjTranspose * σY * tGate) * hadamard := by
            simp only [Matrix.mul_assoc]
          simp only [h_assoc]
          rw [Alethfeld.Quantum.Gates.hadamard_tgate_inv_conj_Y]
          simp only [smul_apply, smul_eq_mul]
          rw [Alethfeld.Quantum.Gates.diag_Z_minus_Y]
      rw [h_single_diag]
      sorry
    · -- Case: 0 ∉ S, so α 0 = 0 (I)
      have hα0_I : α 0 = 0 := by
        subst hα_eq
        simp only [Finset.mem_sdiff] at h0S ⊢
        by_cases h0R : (0 : Fin (n + 1)) ∈ R
        · exact absurd (hRS h0R) h0S
        · simp [h0S, h0R]
      have h_single_diag : (hadamard.conjTranspose * tGate.conjTranspose *
          (σ (α 0)).conjTranspose * tGate * hadamard)
          (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2 = 1 := by
        have hp_eq : σ (α 0) = σI := by simp [hα0_I, σ]
        have hp_conj : (σ (α 0)).conjTranspose = σI := by
          rw [hp_eq]; exact σI_hermitian
        rw [hp_conj]
        simp only [σI]
        have h_one : !![1, 0; 0, 1] = (1 : Mat2) := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [one_apply]
        rw [h_one]
        simp only [mul_one]
        have h_TT : hadamard.conjTranspose * tGate.conjTranspose * tGate * hadamard =
            hadamard.conjTranspose * hadamard := by
          have h_T_unit : tGate.conjTranspose * tGate = 1 :=
            Alethfeld.Quantum.Gates.tGate_conjTranspose_mul_tGate
          calc hadamard.conjTranspose * tGate.conjTranspose * tGate * hadamard
              = hadamard.conjTranspose * (tGate.conjTranspose * tGate) * hadamard := by
                simp only [Matrix.mul_assoc]
            _ = hadamard.conjTranspose * 1 * hadamard := by rw [h_T_unit]
            _ = hadamard.conjTranspose * hadamard := by rw [mul_one]
        rw [h_TT]
        have h_HH : hadamard.conjTranspose * hadamard = 1 := by
          rw [Alethfeld.Quantum.Gates.hadamard_conjTranspose]
          unfold Alethfeld.Quantum.Gates.hadamard
          simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_assoc, smul_eq_mul]
          have hc : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
            rw [div_mul_div_comm, one_mul]
            congr 1
            rw [← Complex.ofReal_mul]
            rw [Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
            simp
          rw [hc]
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [smul_apply, mul_apply, Fin.sum_univ_two, of_apply, one_apply] <;> ring
        rw [h_HH]
        simp only [one_apply_eq]
      rw [h_single_diag, mul_one]
      sorry

/-- Key lemma: pauliCoeff of transformedObs at T-expansion index. -/
lemma pauliCoeff_transformedObs_at_expansion {n : ℕ} (f : BoolFunc n)
    (S : Finset (Fin n)) (α : Fin n → Fin 4) (hα : α ∈ tExpansionPaulis S) :
    pauliCoeff (transformedObs f) α = (1 / Real.sqrt 2 : ℂ)^S.card * (fourierCoeff f S : ℂ) := by
  unfold pauliCoeff transformedObs
  have h_cycle : ((pauliString α).conjTranspose *
      (kroneckerPow n tGate * kroneckerPow n hadamard * diagonalObs f *
        (kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose)).trace =
      ((kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose *
        (pauliString α).conjTranspose * kroneckerPow n tGate * kroneckerPow n hadamard *
        diagonalObs f).trace := by
    sorry
  rw [h_cycle]
  let M := (kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose *
            (pauliString α).conjTranspose * kroneckerPow n tGate * kroneckerPow n hadamard
  let L := diagonalObs f
  have h_diag := backTransformed_pauli_diag_of_tExpansion S α hα
  have h_src := sourceSubset_of_tExpansion S α hα
  sorry

/-- Helper: Pauli coefficient magnitude at T-expansion index. -/
lemma normSq_pauliCoeff_transformedObs_at_expansion {n : ℕ} (f : BoolFunc n)
    (S : Finset (Fin n)) (α : Fin n → Fin 4) (hα : α ∈ tExpansionPaulis S) :
    Complex.normSq (pauliCoeff (transformedObs f) α) = fourierCoeffSq f S / 2^S.card := by
  rw [pauliCoeff_transformedObs_at_expansion f S α hα]
  rw [normSq_one_div_sqrt2_pow_mul S.card (fourierCoeff f S)]
  unfold fourierCoeffSq
  rfl

/-- Spectral distribution of transformedObs on T-expansion Paulis. -/
lemma spectralDist_transformedObs_at_expansion {n : ℕ} (f : BoolFunc n)
    (S : Finset (Fin n)) (α : Fin n → Fin 4) (hα : α ∈ tExpansionPaulis S) :
    spectralDist (transformedObs f) α = fourierCoeffSq f S / 2^S.card := by
  unfold spectralDist
  exact normSq_pauliCoeff_transformedObs_at_expansion f S α hα

/-- Spectral distribution of transformedObs is zero outside allTExpansionPaulis. -/
lemma spectralDist_transformedObs_outside {n : ℕ} (f : BoolFunc n)
    (α : Fin n → Fin 4) (hα : α ∉ allTExpansionPaulis) :
    spectralDist (transformedObs f) α = 0 := by
  have hZ : ∃ i : Fin n, α i = 3 := by
    unfold allTExpansionPaulis at hα
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hα
    by_contra hne
    push_neg at hne
    have hmem : α ∈ tExpansionPaulis (sourceSubset α) := by
      unfold tExpansionPaulis sourceSubset
      simp only [Finset.mem_image, Finset.mem_powerset]
      use Finset.filter (fun i => α i = 2) Finset.univ
      constructor
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        right; exact hi
      · ext i
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
        have hi3 : α i ≠ 3 := hne i
        have hlt : (α i).val < 4 := (α i).isLt
        interval_cases hv : (α i).val
        · have hαi : α i = 0 := Fin.ext hv
          simp only [hαi]
          split_ifs <;> first | rfl | (exfalso; simp_all)
        · have hαi : α i = 1 := Fin.ext hv
          simp only [hαi]
          split_ifs <;> first | rfl | (exfalso; simp_all)
        · have hαi : α i = 2 := Fin.ext hv
          simp only [hαi]
          split_ifs <;> first | rfl | (exfalso; simp_all)
        · exfalso
          have hαi : α i = 3 := Fin.ext hv
          exact hi3 hαi
    exact hα (sourceSubset α) hmem
  obtain ⟨i, hi⟩ := hZ
  have h_coeff_zero : pauliCoeff (transformedObs f) α = 0 := by
    unfold pauliCoeff transformedObs
    simp only [mul_eq_zero]
    right
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      have hZ : ∃ j, α j = 3 := ⟨i, hi⟩
      have h_diag_zero := backTransformed_pauli_diag_zero_of_Z α hZ
      let P := pauliString α
      let T := kroneckerPow (n + 1) tGate
      let H := kroneckerPow (n + 1) hadamard
      let L := diagonalObs f
      have h_cycled : Matrix.trace (Pᴴ * (T * H * L * Hᴴ * Tᴴ)) =
          Matrix.trace ((Hᴴ * Tᴴ * Pᴴ * T * H) * L) := by
        simp only [← Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (Pᴴ * T * H * L * Hᴴ) Tᴴ]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (Tᴴ * Pᴴ * T * H * L) Hᴴ]
        simp only [← Matrix.mul_assoc]
      rw [h_cycled]
      apply trace_product_zero_of_zero_diag_and_diag
      · exact h_diag_zero
      · intro i j hij
        simp only [L, diagonalObs]
        exact Matrix.diagonal_apply_ne _ hij
  unfold spectralDist
  rw [h_coeff_zero]
  simp only [Complex.normSq_zero]

end Alethfeld.Quantum.EntropyIncrease.SpectralDistTransform
