/-
  AlethfeldLean.QBF.Rank1.L4Maximum.Step1_Definitions

  Step 1: Magic State Definitions for L4 Maximum Theorem

  Alethfeld Verified Proof | Graph: L4-maximum v1
  EDN Nodes: :L4-step3, :L4-step4 (definitions)
  Status: CLEAN

  This file defines:
  - isMagicState: predicate for when squared Bloch components are (1/3, 1/3, 1/3)
  - magicBlochVector: the specific Bloch vector (1/√3, 1/√3, 1/√3)
  - Key lemmas about the magic state
-/
import AlethfeldLean.QBF.Rank1.L3Entropy
import AlethfeldLean.QBF.Rank1.ShannonMax

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped BigOperators
open Real Alethfeld.Quantum.Bloch Alethfeld.QBF.Rank1.L3Entropy

/-! ## Magic State Definition -/

/-- A Bloch vector is in the magic state when its squared components are (1/3, 1/3, 1/3).
    This is equivalent to (x², y², z²) = (1/3, 1/3, 1/3). -/
def isMagicState (v : BlochVector) : Prop :=
  v.q 1 = 1/3 ∧ v.q 2 = 1/3 ∧ v.q 3 = 1/3

/-- Alternative characterization: magic state iff q values for 1,2,3 are all 1/3 -/
theorem isMagicState_iff (v : BlochVector) :
    isMagicState v ↔ ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ = 1/3 := by
  unfold isMagicState
  constructor
  · intro ⟨h1, h2, h3⟩ ℓ hℓ
    fin_cases ℓ <;> simp_all
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

/-! ## The Magic Bloch Vector -/

/-- Helper: 1/(√3)² = 1/3 -/
theorem one_div_sqrt_three_sq : (1 / Real.sqrt 3)^2 = 1/3 := by
  have h3 : (3 : ℝ) ≥ 0 := by norm_num
  rw [div_pow, one_pow, Real.sq_sqrt h3, one_div]

/-- Helper: sum of three copies of 1/3 equals 1 -/
theorem three_thirds_eq_one : (1 : ℝ)/3 + 1/3 + 1/3 = 1 := by ring

/-- Helper: 3 * (1/√3)² = 1 -/
theorem three_one_div_sqrt_three_sq : 3 * (1 / Real.sqrt 3)^2 = 1 := by
  rw [one_div_sqrt_three_sq]
  norm_num

/-- The magic Bloch vector: (1/√3, 1/√3, 1/√3) -/
noncomputable def magicBlochVector : BlochVector where
  x := 1 / Real.sqrt 3
  y := 1 / Real.sqrt 3
  z := 1 / Real.sqrt 3
  norm_sq := by
    simp only [one_div_sqrt_three_sq]
    norm_num

/-- The magic Bloch vector satisfies the magic state predicate -/
theorem magicBlochVector_isMagicState : isMagicState magicBlochVector := by
  unfold isMagicState magicBlochVector BlochVector.q
  simp only [one_div_sqrt_three_sq]
  trivial

/-- Magic Bloch vector q values -/
theorem magicBlochVector_q (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    magicBlochVector.q ℓ = 1/3 :=
  (isMagicState_iff magicBlochVector).mp magicBlochVector_isMagicState ℓ hℓ

/-- Magic Bloch vector q values are positive -/
theorem magicBlochVector_q_pos (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    magicBlochVector.q ℓ > 0 := by
  rw [magicBlochVector_q ℓ hℓ]
  norm_num

/-! ## Uniform Product State -/

/-- A product state where all qubits are in the magic state -/
noncomputable def magicProductState {n : ℕ} : Fin n → BlochVector :=
  fun _ => magicBlochVector

/-- All qubits in magic product state are magic -/
theorem magicProductState_isMagic {n : ℕ} (k : Fin n) :
    isMagicState (magicProductState k) :=
  magicBlochVector_isMagicState

/-- Magic product state q values are 1/3 -/
theorem magicProductState_q {n : ℕ} (k : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    (magicProductState k).q ℓ = 1/3 :=
  magicBlochVector_q ℓ hℓ

/-- Magic product state q values are positive -/
theorem magicProductState_q_pos {n : ℕ} (k : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    (magicProductState k).q ℓ > 0 :=
  magicBlochVector_q_pos ℓ hℓ

end Alethfeld.QBF.Rank1.L4Maximum
