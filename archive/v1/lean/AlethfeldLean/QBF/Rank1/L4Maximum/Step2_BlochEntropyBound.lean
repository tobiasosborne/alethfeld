/-
  AlethfeldLean.QBF.Rank1.L4Maximum.Step2_BlochEntropyBound

  Step 2: Bloch Entropy Upper Bound

  Alethfeld Verified Proof | Graph: L4-maximum v1
  EDN Nodes: :L4-step3, :L4-step4 (bound application)
  Status: CLEAN

  Key Result: blochEntropy v ≤ log₂(3) for any Bloch vector v.

  Proof Strategy:
  - Convert Bloch vector squared components to a probability distribution (ProbDist3)
  - Show blochEntropy equals shannonEntropy of this distribution
  - Apply the Shannon maximum entropy theorem
-/
import AlethfeldLean.QBF.Rank1.L4Maximum.Step1_Definitions

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped BigOperators
open Real Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L3Entropy
open Alethfeld.QBF.Rank1.ShannonMax

/-! ## Converting BlochVector to ProbDist3 -/

/-- Convert Bloch vector squared components (x², y², z²) to a ProbDist3.
    Since x² + y² + z² = 1 (from norm_sq), this is a valid probability distribution. -/
noncomputable def blochToProbDist3 (v : BlochVector) : ShannonMax.ProbDist3 where
  p := fun i => v.q (i.succ)  -- p(0) = q(1) = x², p(1) = q(2) = y², p(2) = q(3) = z²
  nonneg := fun i => BlochVector.q_nonneg v _
  sum_eq_one := by
    simp only [Fin.sum_univ_three]
    -- Need: v.q 1 + v.q 2 + v.q 3 = 1
    show v.q 1 + v.q 2 + v.q 3 = 1
    unfold BlochVector.q
    simp only
    have h := v.norm_sq
    linarith

/-- blochToProbDist3 maps i to v.q (i+1) -/
theorem blochToProbDist3_val (v : BlochVector) (i : Fin 3) :
    (blochToProbDist3 v).p i = v.q (i.succ) := rfl

/-- Specific values of blochToProbDist3 -/
theorem blochToProbDist3_p0 (v : BlochVector) : (blochToProbDist3 v).p 0 = v.q 1 := rfl
theorem blochToProbDist3_p1 (v : BlochVector) : (blochToProbDist3 v).p 1 = v.q 2 := rfl
theorem blochToProbDist3_p2 (v : BlochVector) : (blochToProbDist3 v).p 2 = v.q 3 := rfl

/-! ## Relating Entropy Definitions -/

/-- L3Entropy.log2 equals ShannonMax.log2 -/
theorem log2_eq (x : ℝ) : L3Entropy.log2 x = ShannonMax.log2 x := rfl

/-- L3Entropy.entropyTerm equals ShannonMax.entropyTerm -/
theorem entropyTerm_eq (p : ℝ) : L3Entropy.entropyTerm p = ShannonMax.entropyTerm p := rfl

/-- blochEntropy equals shannonEntropy of the converted distribution -/
theorem blochEntropy_eq_shannonEntropy (v : BlochVector) :
    L3Entropy.blochEntropy v = ShannonMax.shannonEntropy (blochToProbDist3 v) := by
  unfold L3Entropy.blochEntropy ShannonMax.shannonEntropy
  simp only [Fin.sum_univ_three, Fin.isValue]
  -- LHS: entropyTerm (v.q 1) + entropyTerm (v.q 2) + entropyTerm (v.q 3)
  -- RHS: entropyTerm (p 0) + entropyTerm (p 1) + entropyTerm (p 2)
  --    = entropyTerm (v.q 1) + entropyTerm (v.q 2) + entropyTerm (v.q 3)
  rw [blochToProbDist3_p0, blochToProbDist3_p1, blochToProbDist3_p2]
  -- Need to convert between namespaces
  simp only [entropyTerm_eq]

/-! ## Main Entropy Bound -/

/-- L4-step4: Bloch entropy is bounded by log₂(3) -/
theorem blochEntropy_le_log2_three (v : BlochVector) :
    L3Entropy.blochEntropy v ≤ ShannonMax.log2 3 := by
  rw [blochEntropy_eq_shannonEntropy]
  exact ShannonMax.entropy_le_log2_three (blochToProbDist3 v)

/-- Version with L3Entropy's log2 (they're equal) -/
theorem blochEntropy_le_log2_three' (v : BlochVector) :
    L3Entropy.blochEntropy v ≤ L3Entropy.log2 3 := by
  rw [log2_eq]
  exact blochEntropy_le_log2_three v

/-! ## Magic State Achieves Maximum -/

/-- The magic state converts to the uniform distribution (component-wise) -/
theorem magicBlochVector_toProbDist3_p_eq_uniform (i : Fin 3) :
    (blochToProbDist3 magicBlochVector).p i = ShannonMax.uniformDist.p i := by
  rw [blochToProbDist3_val, ShannonMax.uniform_val, magicBlochVector_q _ (Fin.succ_ne_zero i)]

/-- The magic state converts to the uniform distribution -/
theorem magicBlochVector_toProbDist3_eq_uniform :
    (blochToProbDist3 magicBlochVector).p = ShannonMax.uniformDist.p := by
  funext i
  exact magicBlochVector_toProbDist3_p_eq_uniform i

/-- Shannon entropy depends only on the p values -/
theorem shannonEntropy_congr (d1 d2 : ShannonMax.ProbDist3) (h : d1.p = d2.p) :
    ShannonMax.shannonEntropy d1 = ShannonMax.shannonEntropy d2 := by
  unfold ShannonMax.shannonEntropy
  simp only [h]

/-- Bloch entropy of magic state equals log₂(3) -/
theorem blochEntropy_magic : L3Entropy.blochEntropy magicBlochVector = ShannonMax.log2 3 := by
  rw [blochEntropy_eq_shannonEntropy]
  rw [shannonEntropy_congr _ ShannonMax.uniformDist magicBlochVector_toProbDist3_eq_uniform]
  exact ShannonMax.entropy_uniform

/-- Version with L3Entropy's log2 -/
theorem blochEntropy_magic' : L3Entropy.blochEntropy magicBlochVector = L3Entropy.log2 3 := by
  rw [log2_eq]
  exact blochEntropy_magic

/-! ## Total Bloch Entropy for Magic Product State -/

/-- Total Bloch entropy of magic product state -/
theorem totalBlochEntropy_magic {n : ℕ} :
    L3Entropy.totalBlochEntropy (magicProductState (n := n)) = n * ShannonMax.log2 3 := by
  unfold L3Entropy.totalBlochEntropy magicProductState
  simp only [blochEntropy_magic, Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul]

end Alethfeld.QBF.Rank1.L4Maximum
