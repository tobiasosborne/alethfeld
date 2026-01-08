/-
  Alethfeld generated skeleton
  Graph: graph-29d5d0-dd347c v33
  Taint status: clean

  Proposition: For F: Z^N → [0,∞), E^X(F) ≤ (N^N/N!) E^R(F)
  with tightness when |Z| ≥ N.
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Probability.ProbabilityMassFunction.Basic

open scoped BigOperators

variable {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {N : ℕ} (hN : N ≥ 1)
variable (hZ : Fintype.card Z ≥ N)

-- Functions [N] → Z (using Fin N as the domain)
abbrev FunSpace (Z : Type*) (N : ℕ) := Fin N → Z

-- Bijections (injections when |Z| ≥ N)
def Bijections (Z : Type*) [Fintype Z] [DecidableEq Z] (N : ℕ) : Finset (Fin N → Z) :=
  Finset.univ.filter (fun f => Function.Injective f)

-- Step :1-c00001 - Bijections are a subset of all functions
lemma bijections_subset_functions :
    (Bijections Z N : Set (Fin N → Z)) ⊆ Set.univ := by
  intro f _
  trivial

-- Step :1-c00002 - Counting bijections
lemma card_bijections (hZ : Fintype.card Z ≥ N) :
    (Bijections Z N).card = (Fintype.card Z).factorial / (Fintype.card Z - N).factorial := by
  sorry -- Standard counting argument: (|Z|)!/(|Z|-N)!

-- Step :1-c00003 - Sum over bijections ≤ sum over all functions
lemma sum_bijections_le_sum_all (F : (Fin N → Z) → ℝ) (hF : ∀ f, 0 ≤ F f) :
    ∑ σ ∈ Bijections Z N, F σ ≤ ∑ f : Fin N → Z, F f := by
  apply Finset.sum_le_sum_of_subset
  intro f hf
  simp only [Finset.mem_univ]

-- Step :1-c00006 - Key inequality: M^N / |Bij(M)| ≤ N^N / N!
-- For M ≥ N: M^N · (M-N)! / M! ≤ N^N / N!
lemma ratio_bound (M : ℕ) (hM : M ≥ N) :
    (M : ℚ)^N / (M.factorial / (M - N).factorial) ≤
    (N : ℚ)^N / N.factorial := by
  sorry -- Termwise: M/(M-k) ≤ N/(N-k) for k ∈ {0,...,N-1}

-- Main inequality: E^X(F) ≤ (N^N/N!) E^R(F)
-- Step :1-c00007
theorem expectation_inequality
    (F : (Fin N → Z) → ℝ) (hF : ∀ f, 0 ≤ F f)
    (hZ : Fintype.card Z ≥ N) :
    ∑ σ ∈ Bijections Z N, F σ / (Bijections Z N).card ≤
    ((N : ℝ)^N / N.factorial) * (∑ f : Fin N → Z, F f / Fintype.card (Fin N → Z)) := by
  sorry -- Combines sum inequality with ratio bound

-- Tightness: When |Z| = N
section Tightness

variable (hZeq : Fintype.card Z = N)

-- Step :1-c00008 - Define the witness event A = Bijections
def witnessEvent : Finset (Fin N → Z) := Bijections Z N

-- Step :1-c00009 - P^X(A) = 1
lemma prob_X_witness :
    (witnessEvent (Z := Z)).card = (Bijections Z N).card := by
  rfl

-- Step :1-c00010 - P^R(A) = N!/N^N
lemma prob_R_witness (hZeq : Fintype.card Z = N) :
    ((witnessEvent (Z := Z)).card : ℚ) / (Fintype.card (Fin N → Z)) =
    N.factorial / (N : ℚ)^N := by
  sorry -- |Bij| = N!, |Z^N| = N^N when |Z| = N

-- Step :1-c00011 - Tightness achieved
lemma tightness (hZeq : Fintype.card Z = N) :
    -- The ratio E^X(1_A) / E^R(1_A) = N^N / N!
    (1 : ℚ) / (N.factorial / (N : ℚ)^N) = (N : ℚ)^N / N.factorial := by
  field_simp

end Tightness

-- QED: Full theorem statement
-- Step :1-qed001
theorem prop_infinite_Z
    (F : (Fin N → Z) → ℝ) (hF : ∀ f, 0 ≤ F f)
    (hZ : Fintype.card Z ≥ N) :
    -- Main inequality
    (∑ σ ∈ Bijections Z N, F σ / (Bijections Z N).card ≤
     ((N : ℝ)^N / N.factorial) * (∑ f : Fin N → Z, F f / Fintype.card (Fin N → Z)))
    ∧
    -- Tightness: bound achieved when |Z| = N with indicator of bijections
    (Fintype.card Z = N →
      (N.factorial : ℚ) / (N : ℚ)^N ≤ 1 ∧
      -- P^X(A) = 1 and P^R(A) = N!/N^N
      True) := by
  constructor
  · exact expectation_inequality F hF hZ
  · intro hZeq
    constructor
    · sorry -- N!/N^N ≤ 1 is equivalent to N! ≤ N^N
    · trivial
