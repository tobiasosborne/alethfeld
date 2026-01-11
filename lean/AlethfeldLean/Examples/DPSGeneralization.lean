/-
  Alethfeld generated skeleton
  Graph: graph-4be308-49c58e v76
  Taint status: clean (37/37 verified)

  Theorem: Symmetric Extension Characterization for Proper Cones

  Let C_A and C_B be proper cones. Let x ∈ C_A ⊗_max C_B.
  Then x has a symmetric extension to k copies of subsystem A for any k,
  if and only if, x ∈ C_A ⊗_min C_B.

  This is a generalization of the DPS (Doherty-Parrilo-Spedalieri) theorem
  from positive semidefinite cones to general proper cones.

  External references:
  - de Finetti theorem (DOI: 10.1214/aoms/1177729952)
-/

import Mathlib

namespace DPSGeneralization

/-! ## Definitions -/

/-- A proper cone in a finite-dimensional real vector space is:
    - Closed
    - Pointed (C ∩ -C = {0})
    - Generating (C - C = V) -/
structure ProperCone (V : Type*) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] where
  carrier : Set V
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  cone : ∀ x ∈ carrier, ∀ r : ℝ, 0 ≤ r → r • x ∈ carrier
  convex : Convex ℝ carrier
  pointed : ∀ x, x ∈ carrier → -x ∈ carrier → x = 0
  generating : ∀ v : V, ∃ c₁ c₂, c₁ ∈ carrier ∧ c₂ ∈ carrier ∧ v = c₁ - c₂

/-- The dual cone C* = {f ∈ V* : f(x) ≥ 0 for all x ∈ C} -/
def ProperCone.dual {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ProperCone V) : Set (V →L[ℝ] ℝ) :=
  {f | ∀ x ∈ C.carrier, 0 ≤ f x}

/-- Interior of the dual cone -/
def ProperCone.dualInterior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ProperCone V) : Set (V →L[ℝ] ℝ) :=
  {f | ∀ x ∈ C.carrier, x ≠ 0 → 0 < f x}

/-- Minimal tensor product: conv{a ⊗ b : a ∈ C_A, b ∈ C_B} -/
def minTensorProduct {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB) : Set (VA ⊗[ℝ] VB) :=
  convexHull ℝ {z | ∃ a ∈ CA.carrier, ∃ b ∈ CB.carrier, z = a ⊗ₜ[ℝ] b}

/-- Maximal tensor product: (C_A* ⊗_min C_B*)* -/
def maxTensorProduct {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB) : Set (VA ⊗[ℝ] VB) :=
  {z | ∀ f ∈ CA.dual, ∀ g ∈ CB.dual, 0 ≤ TensorProduct.lift (f.smulRight g) z}

/-- Symmetric extension of x to k copies -/
def HasSymmetricExtension {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB)
    (φ : VA →L[ℝ] ℝ) (x : VA ⊗[ℝ] VB) (k : ℕ) : Prop :=
  ∃ y_k : (⨂[ℝ]^k VA) ⊗[ℝ] VB,
    -- y_k is in the maximal tensor product cone
    -- y_k is symmetric under permutations
    -- reduction gives x
    sorry -- ADMITTED: full definition requires tensor power machinery

/-- x has symmetric extensions for ALL k -/
def HasAllSymmetricExtensions {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB)
    (φ : VA →L[ℝ] ℝ) (x : VA ⊗[ℝ] VB) : Prop :=
  ∀ k : ℕ, 0 < k → HasSymmetricExtension CA CB φ x k

/-! ## Main Theorem -/

/-- Direction (⇐): min tensor ⟹ symmetric extensions
    EDN steps: :2-fwd001 through :2-fwd010 -/
theorem min_implies_symmetric_extensions
    {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA] [FiniteDimensional ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB] [FiniteDimensional ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB)
    (φ : VA →L[ℝ] ℝ) (hφ : φ ∈ CA.dualInterior)
    (x : VA ⊗[ℝ] VB) (hx : x ∈ minTensorProduct CA CB) :
    HasAllSymmetricExtensions CA CB φ x := by
  -- Step :2-fwd001: Assume x ∈ C_A ⊗_min C_B
  -- Step :2-fwd002: x = Σ λᵢ (aᵢ ⊗ bᵢ) by definition
  -- Step :2-fwd003: Define y_k = Σ λᵢ (aᵢ^⊗k ⊗ bᵢ)
  -- Step :2-fwd004: y_k ∈ maximal tensor (min ⊆ max)
  -- Step :2-fwd005: y_k symmetric (aᵢ^⊗k is symmetric)
  -- Step :2-fwd006: Apply reduction map
  -- Step :2-fwd007: WLOG φ(aᵢ) = 1 (rescaling)
  -- Step :2-fwd008: Reduction gives x
  -- Step :2-fwd009: y_k satisfies definition
  -- Step :2-fwd010: Conclude
  sorry

/-- Direction (⇒): symmetric extensions ⟹ min tensor
    EDN steps: :2-bwd001 through :2-bwd017
    Uses de Finetti theorem (DOI: 10.1214/aoms/1177729952) -/
theorem symmetric_extensions_implies_min
    {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA] [FiniteDimensional ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB] [FiniteDimensional ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB)
    (φ : VA →L[ℝ] ℝ) (hφ : φ ∈ CA.dualInterior)
    (x : VA ⊗[ℝ] VB) (hx : x ∈ maxTensorProduct CA CB)
    (hext : HasAllSymmetricExtensions CA CB φ x) :
    x ∈ minTensorProduct CA CB := by
  -- Step :2-bwd001: Assume symmetric extensions exist for all k
  -- Step :2-bwd002: Choose basis {eⱼ} from int(C_B) (generating property)
  -- Step :2-bwd003: Dual functionals are strictly positive on int(C_B)
  -- Step :2-bwd004: Define reduced elements x̄_{eⱼ,k}
  -- Step :2-bwd005: Reduced elements are in cone
  -- Step :2-bwd006: Reduced elements are symmetric
  -- Step :2-bwd007: Sequence is exchangeable
  -- Step :2-bwd008: Apply de Finetti theorem [EXTERNAL]
  -- Step :2-bwd009: Define functional F_a
  -- Step :2-bwd010: F_a is linear and positive
  -- Step :2-bwd011: Riesz representation gives σ_a ∈ C_B
  -- Step :2-bwd012: Define probability density P
  -- Step :2-bwd013: Integral representation of y_k
  -- Step :2-bwd014: Marginal gives x
  -- Step :2-bwd015: Integral = convex combination
  -- Step :2-bwd016: x ∈ min tensor by definition
  -- Step :2-bwd017: Conclude
  sorry

/-- Main theorem (EDN: :1-qed001)
    Symmetric extension characterization for proper cones -/
theorem dps_generalization
    {VA VB : Type*} [NormedAddCommGroup VA] [NormedSpace ℝ VA] [FiniteDimensional ℝ VA]
    [NormedAddCommGroup VB] [NormedSpace ℝ VB] [FiniteDimensional ℝ VB]
    (CA : ProperCone VA) (CB : ProperCone VB)
    (φ : VA →L[ℝ] ℝ) (hφ : φ ∈ CA.dualInterior)
    (x : VA ⊗[ℝ] VB) (hx : x ∈ maxTensorProduct CA CB) :
    HasAllSymmetricExtensions CA CB φ x ↔ x ∈ minTensorProduct CA CB := by
  constructor
  · -- Direction (⇒): :1-bwd001
    exact symmetric_extensions_implies_min CA CB φ hφ x hx
  · -- Direction (⇐): :1-fwd001
    intro hmin
    exact min_implies_symmetric_extensions CA CB φ hφ x hmin

end DPSGeneralization
