/-
  AlethfeldLean.QBF.Rank1.L4Maximum.Step3_EqualityCondition

  Step 3: Equality Characterization for Bloch Entropy Maximum

  Alethfeld Verified Proof | Graph: L4-maximum v1
  EDN Nodes: :L4-step4 (equality characterization)
  Status: CLEAN

  Key Result: blochEntropy v = log₂(3) if and only if v is a magic state.

  Proof Strategy:
  - Forward: If blochEntropy v = log₂(3), then the converted ProbDist3 is uniform,
    which means v.q values are all 1/3, making v a magic state.
  - Backward: If v is magic, then blochEntropy v = log₂(3) (computed directly).
-/
import AlethfeldLean.QBF.Rank1.L4Maximum.Step2_BlochEntropyBound

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped BigOperators
open Real Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L3Entropy
open Alethfeld.QBF.Rank1.ShannonMax

/-! ## Positivity Conditions -/

/-- For a Bloch vector with all positive q values, the converted distribution has all positive values -/
theorem blochToProbDist3_pos (v : BlochVector) (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) :
    ∀ i : Fin 3, (blochToProbDist3 v).p i > 0 := by
  intro i
  rw [blochToProbDist3_val]
  exact hq _ (Fin.succ_ne_zero i)

/-! ## Forward Direction: Maximum Entropy Implies Magic State -/

/-- If blochToProbDist3 v = uniformDist, then v is a magic state -/
theorem probDist3_uniform_implies_magic (v : BlochVector)
    (h : (blochToProbDist3 v).p = ShannonMax.uniformDist.p) :
    isMagicState v := by
  unfold isMagicState
  -- From h: (blochToProbDist3 v).p i = uniformDist.p i = 1/3 for all i
  have h0 : (blochToProbDist3 v).p 0 = 1/3 := by
    have := congr_fun h 0
    simp only [ShannonMax.uniform_val] at this
    exact this
  have h1 : (blochToProbDist3 v).p 1 = 1/3 := by
    have := congr_fun h 1
    simp only [ShannonMax.uniform_val] at this
    exact this
  have h2 : (blochToProbDist3 v).p 2 = 1/3 := by
    have := congr_fun h 2
    simp only [ShannonMax.uniform_val] at this
    exact this
  -- Now use that (blochToProbDist3 v).p i = v.q (i+1)
  rw [blochToProbDist3_p0] at h0
  rw [blochToProbDist3_p1] at h1
  rw [blochToProbDist3_p2] at h2
  exact ⟨h0, h1, h2⟩

/-- Forward direction: If blochEntropy v = log₂(3) with positive q values, then v is magic -/
theorem blochEntropy_max_implies_magic (v : BlochVector)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0)
    (hmax : L3Entropy.blochEntropy v = ShannonMax.log2 3) :
    isMagicState v := by
  -- From blochEntropy_eq_shannonEntropy: shannonEntropy (blochToProbDist3 v) = log₂(3)
  rw [blochEntropy_eq_shannonEntropy] at hmax
  -- By ShannonMax.entropy_eq_max_iff_uniform, this implies blochToProbDist3 v = uniformDist
  have hpos := blochToProbDist3_pos v hq
  have hunif := (ShannonMax.entropy_eq_max_iff_uniform (blochToProbDist3 v) hpos).mp hmax
  -- Therefore v is magic
  exact probDist3_uniform_implies_magic v hunif

/-! ## Backward Direction: Magic State Implies Maximum Entropy -/

/-- Backward direction: If v is magic, then blochEntropy v = log₂(3) -/
theorem magic_implies_blochEntropy_max (v : BlochVector) (hmag : isMagicState v) :
    L3Entropy.blochEntropy v = ShannonMax.log2 3 := by
  unfold L3Entropy.blochEntropy L3Entropy.entropyTerm
  -- hmag gives us v.q 1 = v.q 2 = v.q 3 = 1/3
  obtain ⟨h1, h2, h3⟩ := hmag
  -- Each entropyTerm evaluates to -(1/3) * log₂(1/3) = (1/3) * log₂(3)
  have hpos : (1 : ℝ)/3 > 0 := by norm_num
  simp only [h1, h2, h3, hpos, ↓reduceIte]
  -- Goal: -3 * ((1/3) * log₂(1/3)) = log₂(3)
  -- Note: log₂(1/3) = -log₂(3)
  unfold L3Entropy.log2 ShannonMax.log2
  rw [show (1 : ℝ)/3 = 3⁻¹ by norm_num, Real.log_inv, neg_div]
  ring

/-! ## Main Equality Characterization -/

/-- L4-step4: Bloch entropy equals log₂(3) iff magic state (for positive q values) -/
theorem blochEntropy_eq_max_iff_magic (v : BlochVector)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) :
    L3Entropy.blochEntropy v = ShannonMax.log2 3 ↔ isMagicState v := by
  constructor
  · exact blochEntropy_max_implies_magic v hq
  · exact magic_implies_blochEntropy_max v

/-- Combined bound and equality: blochEntropy v ≤ log₂(3) with equality iff magic -/
theorem blochEntropy_strict_bound (v : BlochVector)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) :
    L3Entropy.blochEntropy v ≤ ShannonMax.log2 3 ∧
    (L3Entropy.blochEntropy v = ShannonMax.log2 3 ↔ isMagicState v) :=
  ⟨blochEntropy_le_log2_three v, blochEntropy_eq_max_iff_magic v hq⟩

/-! ## Strict Bound for Non-Magic States -/

/-- If v is not magic (with positive q values), then blochEntropy v < log₂(3) -/
theorem blochEntropy_lt_max_of_not_magic (v : BlochVector)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) (hne : ¬isMagicState v) :
    L3Entropy.blochEntropy v < ShannonMax.log2 3 := by
  have hle := blochEntropy_le_log2_three v
  have hneq : L3Entropy.blochEntropy v ≠ ShannonMax.log2 3 := by
    intro h
    exact hne ((blochEntropy_eq_max_iff_magic v hq).mp h)
  exact lt_of_le_of_ne hle hneq

/-! ## Magic Product State Optimality -/

/-- Each qubit in magic product state achieves maximum Bloch entropy -/
theorem magicProductState_achieves_max {n : ℕ} (k : Fin n) :
    L3Entropy.blochEntropy (magicProductState k) = ShannonMax.log2 3 := by
  exact magic_implies_blochEntropy_max _ (magicProductState_isMagic k)

/-- For any product state with positive q values, total Bloch entropy is maximized at magic -/
theorem totalBlochEntropy_le_magic {n : ℕ} (bloch : Fin n → BlochVector)
    (hq : ∀ k : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch k).q ℓ > 0) :
    L3Entropy.totalBlochEntropy bloch ≤
    L3Entropy.totalBlochEntropy (magicProductState (n := n)) := by
  unfold L3Entropy.totalBlochEntropy
  apply Finset.sum_le_sum
  intro k _
  calc L3Entropy.blochEntropy (bloch k)
      ≤ ShannonMax.log2 3 := blochEntropy_le_log2_three (bloch k)
    _ = L3Entropy.blochEntropy (magicProductState k) :=
        (magicProductState_achieves_max k).symm

/-- Total Bloch entropy equals maximum iff all qubits are magic -/
theorem totalBlochEntropy_eq_max_iff {n : ℕ} (bloch : Fin n → BlochVector)
    (hq : ∀ k : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch k).q ℓ > 0) :
    L3Entropy.totalBlochEntropy bloch = n * ShannonMax.log2 3 ↔
    ∀ k : Fin n, isMagicState (bloch k) := by
  rw [← totalBlochEntropy_magic (n := n)]
  unfold L3Entropy.totalBlochEntropy
  constructor
  · -- Forward: If sums are equal and each term ≤, then each term =
    intro h
    have hle : ∀ k, L3Entropy.blochEntropy (bloch k) ≤ ShannonMax.log2 3 :=
      fun k => blochEntropy_le_log2_three (bloch k)
    have hge : ∀ k, L3Entropy.blochEntropy (bloch k) ≥ L3Entropy.blochEntropy (magicProductState k) := by
      intro k
      -- If any term is strictly less, the sum would be strictly less
      by_contra hlt
      push_neg at hlt
      -- The sum of bloch k would be strictly less than the magic sum
      have hsum_lt : ∑ j : Fin n, L3Entropy.blochEntropy (bloch j) <
          ∑ j : Fin n, L3Entropy.blochEntropy (magicProductState j) := by
        apply Finset.sum_lt_sum
        · intro j _
          calc L3Entropy.blochEntropy (bloch j)
              ≤ ShannonMax.log2 3 := blochEntropy_le_log2_three (bloch j)
            _ = L3Entropy.blochEntropy (magicProductState j) :=
                (magicProductState_achieves_max j).symm
        · exact ⟨k, Finset.mem_univ k, hlt⟩
      linarith
    intro k
    have heq : L3Entropy.blochEntropy (bloch k) = L3Entropy.blochEntropy (magicProductState k) := by
      have h1 : L3Entropy.blochEntropy (bloch k) ≤ L3Entropy.blochEntropy (magicProductState k) := by
        calc L3Entropy.blochEntropy (bloch k)
            ≤ ShannonMax.log2 3 := blochEntropy_le_log2_three (bloch k)
          _ = L3Entropy.blochEntropy (magicProductState k) := (magicProductState_achieves_max k).symm
      have h2 := hge k
      exact le_antisymm h1 h2
    rw [magicProductState_achieves_max] at heq
    exact (blochEntropy_eq_max_iff_magic (bloch k) (hq k)).mp heq
  · -- Backward: If all are magic, sums are equal
    intro h
    apply Finset.sum_congr rfl
    intro k _
    rw [magic_implies_blochEntropy_max (bloch k) (h k), magicProductState_achieves_max]

end Alethfeld.QBF.Rank1.L4Maximum
