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

/-! ### Helper Definitions for Inductive Proofs -/

/-- The shifted subset: positions j such that j.succ ∈ S -/
def shiftedSubset {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.filter (fun j => j.succ ∈ S) Finset.univ

/-- Cardinality of S when 0 ∈ S equals cardinality of shiftedSubset plus 1 -/
lemma card_eq_shiftedSubset_add_one {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∈ S) :
    S.card = (shiftedSubset S).card + 1 := by
  -- The bijection between S \ {0} and shiftedSubset is j ↔ j.succ
  have h_eq : S.card = 1 + (S.erase 0).card := by
    have h1 := Finset.card_erase_of_mem h0
    have h2 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, h0⟩
    omega
  rw [h_eq, add_comm]
  congr 1
  unfold shiftedSubset
  apply Finset.card_bij (fun j hj => j.pred (by
    simp only [Finset.mem_erase] at hj
    exact hj.1))
  · intro i hi
    simp only [Finset.mem_erase] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.succ_pred i hi.1]
    exact hi.2
  · intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_erase] at hi₁ hi₂
    exact Fin.pred_inj.mp heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j.succ, ?_, ?_⟩
    · simp only [Finset.mem_erase, ne_eq, Fin.succ_ne_zero, not_false_eq_true, hj, and_self]
    · simp only [Fin.pred_succ]

/-- Cardinality of S when 0 ∉ S equals cardinality of shiftedSubset -/
lemma card_eq_shiftedSubset {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ S) :
    S.card = (shiftedSubset S).card := by
  unfold shiftedSubset
  apply Finset.card_bij (fun i hi => i.pred (fun heq => h0 (heq ▸ hi)))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_ne : i ≠ 0 := fun heq => h0 (heq ▸ hi)
    rw [Fin.succ_pred i h_ne]
    exact hi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.pred_inj.mp heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j.succ, hj, ?_⟩
    simp only [Fin.pred_succ]

/-- The shifted T-expansion: if α ∈ tExpansionPaulis S, then (fun m => α m.succ) ∈ tExpansionPaulis (shiftedSubset S) -/
lemma tExpansion_shift {n : ℕ} (S : Finset (Fin (n + 1))) (α : Fin (n + 1) → Fin 4)
    (hα : α ∈ tExpansionPaulis S) :
    (fun m => α m.succ) ∈ tExpansionPaulis (shiftedSubset S) := by
  unfold tExpansionPaulis at hα ⊢
  simp only [Finset.mem_image, Finset.mem_powerset] at hα ⊢
  obtain ⟨R, hRS, hα_eq⟩ := hα
  -- The shifted R' = {j : j.succ ∈ R}
  use Finset.filter (fun j => j.succ ∈ R) Finset.univ
  refine ⟨?_, ?_⟩
  · -- R' ⊆ shiftedSubset S
    intro j hj
    simp only [shiftedSubset, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hRS hj
  · -- The shifted α matches the T-expansion formula
    ext m
    subst hα_eq
    simp only [shiftedSubset, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]

/-- pauliZ_S diagonal decomposes as Kronecker product of shifted Z_S' and single-qubit Z/I -/
lemma pauliZ_S_diag_decompose {n : ℕ} (S : Finset (Fin (n + 1))) (x : Fin (2^(n+1))) :
    pauliZ_S S x x =
    pauliZ_S (shiftedSubset S) (finPow2SuccEquiv n x).1 (finPow2SuccEquiv n x).1 *
    (if (0 : Fin (n+1)) ∈ S then σZ else σI) (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2 := by
  unfold pauliZ_S
  simp only [pauliString, Matrix.submatrix_apply]
  rw [Alethfeld.Quantum.PauliDiag.Kronecker.kronecker_diag_entry]
  congr 1
  · -- First factor: pauliString for shifted indices
    congr 1
    ext m
    simp only [shiftedSubset, Finset.mem_filter, Finset.mem_univ, true_and]
  · -- Second factor: σZ or σI depending on whether 0 ∈ S
    simp only [σ]
    by_cases h0 : (0 : Fin (n+1)) ∈ S <;> simp [h0]

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
      -- Apply IH to first factor
      have h_shifted := tExpansion_shift S α (by
        unfold tExpansionPaulis
        simp only [Finset.mem_image, Finset.mem_powerset]
        exact ⟨R, hRS, hα_eq⟩)
      have h_ih := ih (shiftedSubset S) (fun m => α m.succ) h_shifted (finPow2SuccEquiv n x).1
      rw [h_ih]
      -- Use pauliZ_S decomposition
      rw [pauliZ_S_diag_decompose S x]
      simp only [h0S, ↓reduceIte]
      -- Use cardinality lemma
      have h_card := card_eq_shiftedSubset_add_one S h0S
      rw [h_card]
      ring
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
      -- Apply IH to first factor
      have h_shifted := tExpansion_shift S α (by
        unfold tExpansionPaulis
        simp only [Finset.mem_image, Finset.mem_powerset]
        exact ⟨R, hRS, hα_eq⟩)
      have h_ih := ih (shiftedSubset S) (fun m => α m.succ) h_shifted (finPow2SuccEquiv n x).1
      rw [h_ih]
      -- Use pauliZ_S decomposition
      rw [pauliZ_S_diag_decompose S x]
      simp only [h0S, ↓reduceIte]
      -- σI diagonal is 1
      have h_σI_diag : σI (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2 = 1 :=
        Alethfeld.Quantum.PauliDiag.Single.σI_diag_entry (finPow2SuccEquiv n x).2
      rw [h_σI_diag, mul_one]
      -- Use cardinality lemma
      have h_card := card_eq_shiftedSubset S h0S
      rw [h_card]

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
    -- Use trace cyclic property: Tr(AB) = Tr(BA)
    let P := pauliString α
    let T := kroneckerPow n tGate
    let H := kroneckerPow n hadamard
    let L := diagonalObs f
    calc (Pᴴ * (T * H * L * Hᴴ * Tᴴ)).trace
        = (Tᴴ * Pᴴ * T * H * L * Hᴴ).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm (Pᴴ * T * H * L * Hᴴ) Tᴴ]
          simp only [Matrix.mul_assoc]
      _ = (Hᴴ * Tᴴ * Pᴴ * T * H * L).trace := by
          rw [Matrix.trace_mul_comm (Tᴴ * Pᴴ * T * H * L) Hᴴ]
          simp only [Matrix.mul_assoc]
  rw [h_cycle]
  let M := (kroneckerPow n hadamard).conjTranspose * (kroneckerPow n tGate).conjTranspose *
            (pauliString α).conjTranspose * kroneckerPow n tGate * kroneckerPow n hadamard
  let L := diagonalObs f
  have h_diag := backTransformed_pauli_diag_of_tExpansion S α hα
  have h_src := sourceSubset_of_tExpansion S α hα
  -- The trace is ∑_x M(x,x) * L(x,x)
  have h_trace_eq : (M * L).trace = ∑ x : Fin (2^n), M x x * L x x := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_congr rfl
    intro x _
    simp only [Matrix.mul_apply]
    have h_L_diag : ∀ i j, i ≠ j → L i j = 0 := fun i j hij => by
      simp only [L, diagonalObs]
      exact Matrix.diagonal_apply_ne _ hij
    have h_offdiag_zero : ∀ y : Fin (2^n), y ≠ x → M x y * L y x = 0 := by
      intro y hyx
      have h_ne : x ≠ y := fun h => hyx h.symm
      rw [h_L_diag y x h_ne.symm, mul_zero]
    rw [Fintype.sum_eq_single x (fun y hy => h_offdiag_zero y hy)]
  rw [h_trace_eq]
  -- Substitute the diagonal values using h_diag
  have h_sum_eq : ∑ x : Fin (2^n), M x x * L x x =
      ∑ x : Fin (2^n), (1 / Real.sqrt 2 : ℂ)^S.card * pauliZ_S S x x * L x x := by
    apply Finset.sum_congr rfl
    intro x _
    simp only [M]
    rw [h_diag x]
  rw [h_sum_eq]
  -- L(x,x) = f(idxToBool x) since diagonalObs f is diagonal with entries f
  have h_L_diag_val : ∀ x : Fin (2^n), L x x =
      (f (fun i => x.val.testBit i.val) : ℂ) := fun x => by
    simp only [L, diagonalObs, Matrix.diagonal_apply_eq]
  simp_rw [h_L_diag_val]
  -- Rewrite the sum using distributivity
  have h_sum_factor : ∑ x : Fin (2^n), (1 / Real.sqrt 2 : ℂ)^S.card * pauliZ_S S x x *
      (f (fun i => x.val.testBit i.val) : ℂ) =
      (1 / Real.sqrt 2 : ℂ)^S.card * ∑ x : Fin (2^n), pauliZ_S S x x *
      (f (fun i => x.val.testBit i.val) : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h_sum_factor]
  -- Now show the sum of pauliZ_S * f = 2^n * fourierCoeff f S
  -- This follows from: pauliZ_S S x x = parityFunc S (bits x)
  -- and fourierCoeff f S = (1/2^n) Σ_x f(x) * parityFunc S x
  have h_pauliZ_S_sum : ∑ x : Fin (2^n), pauliZ_S S x x * (f (fun i => x.val.testBit i.val) : ℂ) =
      (2 : ℂ)^n * (fourierCoeff f S : ℂ) := by
    -- pauliZ_S S x x = parityFunc S (bits x)
    have h_eq : ∀ x : Fin (2^n), pauliZ_S S x x =
        (parityFunc S (fun i => x.val.testBit i.val) : ℂ) := by
      intro x
      rw [pauliZ_S_diag_entry]
      simp only [parityFunc]
      -- Use neg_one_pow_eq_ite: (-1)^n = if Even n then 1 else -1
      rw [neg_one_pow_eq_ite]
      -- Convert Even to % 2 = 0
      simp only [Nat.even_iff]
      norm_cast
    simp_rw [h_eq]
    -- Use boolFuncEquiv to reindex the sum
    have h_sum_reindex : ∑ x : Fin (2^n), (parityFunc S (fun i => x.val.testBit i.val) : ℂ) *
        (f (fun i => x.val.testBit i.val) : ℂ) =
        ∑ v : Fin n → Bool, (parityFunc S v : ℂ) * (f v : ℂ) := by
      rw [← Equiv.sum_comp (boolFuncEquiv n)]
      apply Finset.sum_congr rfl
      intro v _
      congr 2 <;>
        · congr 1
          funext i
          rw [← boolFuncEquiv_symm_apply (boolFuncEquiv n v) i]
          simp only [Equiv.symm_apply_apply]
    rw [h_sum_reindex]
    -- fourierCoeff f S = (1/2^n) * Σ_v f(v) * parityFunc S v
    unfold fourierCoeff
    have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
    have h2n_ne : (2 : ℝ)^n ≠ 0 := ne_of_gt h2n_pos
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_sum, Complex.ofReal_intCast]
    -- Goal: Σ_v χ(v) * f(v) = 2^n * (1/2^n * Σ_v f(v) * χ(v))
    have h_comm : ∀ v, (parityFunc S v : ℂ) * (f v : ℂ) = (f v : ℂ) * (parityFunc S v : ℂ) :=
      fun v => mul_comm _ _
    simp_rw [h_comm]
    field_simp
    simp only [Complex.ofReal_one, mul_one]
  rw [h_pauliZ_S_sum]
  have h2n_ne : (2 : ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp

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
