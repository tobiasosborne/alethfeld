/-
  Test file for L2Influence module

  Verifies that the L2 implementation compiles and key theorems are accessible.
-/
import AlethfeldLean.QBF.Rank1.L2Influence

open Alethfeld.Quantum.Bloch Alethfeld.QBF.Rank1.L2Influence

-- Test: BlochVector.q is accessible and well-typed
#check BlochVector.q

-- Test: q_sum theorems
#check BlochVector.q_sum_eq_two
#check BlochVector.q_nonzero_sum_eq_one

-- Test: Influence definitions
#check @qProduct
#check @probability
#check @influence_j
#check @totalInfluence

-- Test: Main theorems
#check @total_influence_formula
#check @influence_independent_of_bloch
#check @influence_pos

-- Example: Create a concrete Bloch vector (z-axis)
noncomputable example : BlochVector := ⟨0, 0, 1, by norm_num⟩

-- Example: Verify q_sum_eq_two for z-axis state
example : (⟨0, 0, 1, by norm_num⟩ : BlochVector).q_sum_eq_two = by simp [BlochVector.q]; norm_num :=
  rfl

-- Example: Type check total_influence_formula
example {n : ℕ} (bloch : Fin n → BlochVector) :
    totalInfluence bloch = n * (2 : ℝ)^(1 - (n : ℤ)) :=
  total_influence_formula bloch

-- Example: Universality
example {n : ℕ} (bloch₁ bloch₂ : Fin n → BlochVector) :
    totalInfluence bloch₁ = totalInfluence bloch₂ :=
  influence_independent_of_bloch bloch₁ bloch₂
