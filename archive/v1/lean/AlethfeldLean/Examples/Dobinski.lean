/-
  Dobinski's Formula for Bell Numbers

  Theorem: B_n = (1/e) * Σ_{k=0}^∞ k^n / k!

  where B_n is the n-th Bell number (number of partitions of an n-element set).

  This formalization follows the structured proof from dobinski-v2.edn.
  Key components:
  1. Power-Stirling expansion: k^n = Σ_{j=0}^n S(n,j) · k^{(j)}
  2. Falling factorial sum: Σ_{k=0}^∞ k^{(m)}/k! = e for all m
  3. Summation interchange (Fubini-style)
  4. Main theorem combining all components

  Generated from Alethfeld semantic proof graph.
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

open scoped BigOperators
open Finset Real NormedSpace

namespace Alethfeld.Dobinski

/-! ## Definitions -/

/-- Bell number: total number of partitions of an n-element set.
    B_n = Σ_{k=0}^n S(n,k) where S(n,k) is the Stirling number of the second kind. -/
noncomputable def bell (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), Nat.stirlingSecond n k

/-- Falling factorial as a real number for use in infinite series.
    This is just the cast of Nat.descFactorial to ℝ. -/
noncomputable def fallingFactorial (k m : ℕ) : ℝ := (k.descFactorial m : ℝ)

/-! ## Basic Properties of Falling Factorial -/

/-- The falling factorial is zero when k < m -/
lemma fallingFactorial_eq_zero {k m : ℕ} (h : k < m) :
    fallingFactorial k m = 0 := by
  simp only [fallingFactorial, Nat.descFactorial_of_lt h, Nat.cast_zero]

/-- The falling factorial equals k!/(k-m)! when k ≥ m -/
lemma fallingFactorial_eq_div {k m : ℕ} (h : m ≤ k) :
    fallingFactorial k m = (k.factorial : ℝ) / ((k - m).factorial : ℝ) := by
  simp only [fallingFactorial]
  have hdiv : k.descFactorial m = k.factorial / (k - m).factorial := Nat.descFactorial_eq_div h
  rw [hdiv]
  have hdvd : (k - m).factorial ∣ k.factorial := Nat.factorial_dvd_factorial (Nat.sub_le k m)
  have hneR : ((k - m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Nat.cast_div hdvd hneR]

/-- The 0th falling factorial is always 1 -/
@[simp]
lemma fallingFactorial_zero (k : ℕ) : fallingFactorial k 0 = 1 := by
  simp only [fallingFactorial, Nat.descFactorial_zero, Nat.cast_one]

/-- Falling factorial bounded by power -/
lemma fallingFactorial_le_pow (k m : ℕ) : fallingFactorial k m ≤ (k : ℝ) ^ m := by
  simp only [fallingFactorial]
  exact_mod_cast Nat.descFactorial_le_pow k m

/-! ## Key Lemma: Power-Stirling Expansion

    k^n = Σ_{j=0}^n S(n,j) · k^{(j)}

    This is a fundamental identity connecting ordinary powers to falling factorials
    via Stirling numbers of the second kind.
-/

/-- Key identity: k * k^{(j)} = k^{(j+1)} + j * k^{(j)}

    This is the falling factorial recurrence used in the power-Stirling expansion. -/
lemma fallingFactorial_mul (k j : ℕ) :
    fallingFactorial k j * (k : ℝ) = fallingFactorial k (j + 1) + j * fallingFactorial k j := by
  by_cases hj : j ≤ k
  · simp only [fallingFactorial]
    rw [Nat.descFactorial_succ]
    push_cast
    have h : (k : ℝ) = (k - j : ℕ) + j := by
      simp only [Nat.cast_sub hj]
      ring
    rw [h]
    ring
  · push_neg at hj
    simp only [fallingFactorial]
    rw [Nat.descFactorial_of_lt hj]
    rw [Nat.descFactorial_of_lt (Nat.lt_add_right 1 hj)]
    simp

/-- Sum shifting lemma for Stirling-falling factorial products.

    This relates the sum Σ S(n,j) * j * k^{(j)} to Σ (j+1) * S(n,j+1) * k^{(j+1)}
    by reindexing and using that S(n,n+1) = 0. -/
lemma sum_stirling_mul_shift (k n : ℕ) :
    ∑ j ∈ range (n + 1), (n.stirlingSecond j : ℝ) * (j : ℝ) * fallingFactorial k j =
    ∑ j ∈ range (n + 1), ((j + 1) : ℝ) * (n.stirlingSecond (j + 1) : ℝ) *
      fallingFactorial k (j + 1) := by
  -- LHS j=0 term is 0 (since factor j), so shift the index
  have h1 : ∑ j ∈ range (n + 1), (n.stirlingSecond j : ℝ) * (j : ℝ) * fallingFactorial k j =
      ∑ j ∈ range n, (n.stirlingSecond (j + 1) : ℝ) * ((j + 1) : ℝ) *
        fallingFactorial k (j + 1) := by
    conv_lhs => rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    simp
  rw [h1]
  -- RHS j=n term has S(n,n+1)=0, so drop it
  have h2 : ∑ j ∈ range (n + 1), ((j + 1) : ℝ) * (n.stirlingSecond (j + 1) : ℝ) *
      fallingFactorial k (j + 1) =
      ∑ j ∈ range n, ((j + 1) : ℝ) * (n.stirlingSecond (j + 1) : ℝ) *
        fallingFactorial k (j + 1) := by
    conv_lhs => rw [Finset.sum_range_succ]
    have hs : n.stirlingSecond (n + 1) = 0 := Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)
    simp only [hs, Nat.cast_zero, mul_zero, zero_mul]
    simp
  rw [h2]
  -- Now both sums are over range n with reordered factors
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Power-Stirling expansion identity:
    k^n = Σ_{j=0}^n S(n,j) · k^{(j)}

    This expresses ordinary powers in terms of falling factorials using
    Stirling numbers of the second kind as coefficients. -/
theorem power_stirling_expansion (k n : ℕ) :
    (k : ℝ) ^ n = ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_add, range_one, sum_singleton]
    simp only [Nat.stirlingSecond_zero, Nat.cast_one, one_mul]
    simp only [fallingFactorial, Nat.descFactorial_zero, Nat.cast_one]
  | succ n ih =>
    rw [pow_succ, ih, sum_mul]
    -- Transform each term using the falling factorial identity
    have step1 : ∀ j ∈ range (n + 1),
        (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j * k =
        (Nat.stirlingSecond n j : ℝ) * (fallingFactorial k (j + 1) + j * fallingFactorial k j) := by
      intros j _
      rw [mul_assoc, fallingFactorial_mul]
    rw [sum_congr rfl step1]
    simp_rw [mul_add]
    rw [sum_add_distrib]
    -- LHS: Σ S(n,j)*k^{(j+1)} + Σ S(n,j)*j*k^{(j)}
    -- For RHS, split at j=0 (since S(n+1,0) = 0)
    have hRHS : ∑ j ∈ range (n + 2), ((n + 1).stirlingSecond j : ℝ) * fallingFactorial k j =
        ∑ j ∈ range (n + 1), ((n + 1).stirlingSecond (j + 1) : ℝ) *
          fallingFactorial k (j + 1) := by
      conv_lhs => rw [Finset.sum_range_succ']
      simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul]
      simp
    rw [hRHS]
    -- Expand RHS using Stirling recurrence: S(n+1,j+1) = (j+1)*S(n,j+1) + S(n,j)
    have rhs_expand : ∑ j ∈ range (n + 1), ((n + 1).stirlingSecond (j + 1) : ℝ) *
        fallingFactorial k (j + 1) =
        ∑ j ∈ range (n + 1), ((j + 1) : ℝ) * (n.stirlingSecond (j + 1) : ℝ) *
          fallingFactorial k (j + 1) +
        ∑ j ∈ range (n + 1), (n.stirlingSecond j : ℝ) * fallingFactorial k (j + 1) := by
      rw [← sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.stirlingSecond_succ_succ]
      push_cast
      ring
    rw [rhs_expand]
    -- Rearrange to match: add_comm on RHS
    rw [add_comm (∑ j ∈ range (n + 1), ↑(n.stirlingSecond j) * fallingFactorial k (j + 1))]
    congr 1
    -- Need: Σ S(n,j)*j*k^{(j)} = Σ (j+1)*S(n,j+1)*k^{(j+1)}
    have lhs_eq : ∑ j ∈ range (n + 1), (n.stirlingSecond j : ℝ) * (↑j * fallingFactorial k j) =
        ∑ j ∈ range (n + 1), (n.stirlingSecond j : ℝ) * ↑j * fallingFactorial k j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [lhs_eq]
    exact sum_stirling_mul_shift k n

/-! ## Key Lemma: Falling Factorial Sum

    Σ_{k=0}^∞ k^{(m)}/k! = e for all m ∈ ℕ

    This is proved by:
    1. When k < m, the term is 0 (falling factorial vanishes)
    2. When k ≥ m, k^{(m)}/k! = 1/(k-m)!
    3. The sum becomes Σ_{j=0}^∞ 1/j! = e after reindexing
-/

/-- For k ≥ m, k^{(m)}/k! = 1/(k-m)! -/
lemma fallingFactorial_div_factorial {k m : ℕ} (h : m ≤ k) :
    fallingFactorial k m / (k.factorial : ℝ) = 1 / ((k - m).factorial : ℝ) := by
  rw [fallingFactorial_eq_div h]
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hkmf : ((k - m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- For k < m, k^{(m)}/k! = 0 -/
lemma fallingFactorial_div_factorial_eq_zero {k m : ℕ} (h : k < m) :
    fallingFactorial k m / (k.factorial : ℝ) = 0 := by
  simp only [fallingFactorial_eq_zero h, zero_div]

/-- The series Σ_{k=0}^∞ k^{(m)}/k! converges -/
lemma summable_fallingFactorial_div_factorial (m : ℕ) :
    Summable (fun k : ℕ => fallingFactorial k m / (k.factorial : ℝ)) := by
  -- The key observation: terms for k < m are 0, and for k >= m we get 1/(k-m)!
  -- We use reindexing: the series equals Σ_{j=0}^∞ 1/j! which is known to converge
  have hinj : Function.Injective (fun j : ℕ => j + m) := fun a b h => Nat.add_right_cancel h
  have hrange : ∀ k, k ∉ Set.range (fun j : ℕ => j + m) →
      fallingFactorial k m / (k.factorial : ℝ) = 0 := by
    intro k hk
    simp only [Set.mem_range, not_exists] at hk
    have hlt : k < m := by
      by_contra h
      push_neg at h
      exact hk (k - m) (Nat.sub_add_cancel h)
    exact fallingFactorial_div_factorial_eq_zero hlt
  have h1 : Summable (fun j : ℕ => (j.factorial : ℝ)⁻¹) := by
    have := Real.summable_pow_div_factorial 1
    simp only [one_pow, one_div] at this
    exact this
  have hcomp : (fun k => fallingFactorial k m / (k.factorial : ℝ)) ∘ (fun j => j + m) =
               fun j => (j.factorial : ℝ)⁻¹ := by
    ext j
    simp only [Function.comp_apply]
    have h : m ≤ j + m := Nat.le_add_left m j
    rw [fallingFactorial_div_factorial h, one_div, Nat.add_sub_cancel_right]
  rw [← hinj.summable_iff hrange, hcomp]
  exact h1

/-- Key identity: Σ_{k=0}^∞ k^{(m)}/k! = e for all m ∈ ℕ -/
theorem tsum_fallingFactorial_div_factorial (m : ℕ) :
    ∑' k : ℕ, fallingFactorial k m / (k.factorial : ℝ) = Real.exp 1 := by
  -- For k < m, terms are 0. For k ≥ m, term = 1/(k-m)!
  -- Reindexing with j = k - m gives Σ_{j=0}^∞ 1/j! = e
  have hinj : Function.Injective (fun j : ℕ => j + m) := fun a b h => Nat.add_right_cancel h
  have hsupp : Function.support (fun k => fallingFactorial k m / (k.factorial : ℝ)) ⊆
               Set.range (fun j : ℕ => j + m) := by
    intro k hk
    simp only [Function.mem_support] at hk
    simp only [Set.mem_range]
    by_contra h
    push_neg at h
    have hlt : k < m := by
      by_contra hge
      push_neg at hge
      exact h (k - m) (Nat.sub_add_cancel hge)
    exact hk (fallingFactorial_div_factorial_eq_zero hlt)
  have hcomp : ∀ j : ℕ, fallingFactorial (j + m) m / ((j + m).factorial : ℝ) =
               (j.factorial : ℝ)⁻¹ := by
    intro j
    have h : m ≤ j + m := Nat.le_add_left m j
    rw [fallingFactorial_div_factorial h, one_div, Nat.add_sub_cancel_right]
  calc ∑' k, fallingFactorial k m / (k.factorial : ℝ)
      = ∑' j, fallingFactorial (j + m) m / ((j + m).factorial : ℝ) := by
        rw [hinj.tsum_eq hsupp]
    _ = ∑' (j : ℕ), (j.factorial : ℝ)⁻¹ := by
        congr 1
        ext j
        exact hcomp j
    _ = Real.exp 1 := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
        simp only [one_pow, one_div]

/-! ## Convergence of the Main Series -/

/-- The series Σ_{k=0}^∞ k^n/k! converges absolutely -/
lemma summable_pow_div_factorial (n : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ n / (k.factorial : ℝ)) := by
  -- Use the ratio test: for large k, ‖f(k+1)‖ ≤ (1/2) * ‖f(k)‖
  -- f(k) = k^n / k!, so f(k+1)/f(k) = (k+1)^n / k^n / (k+1) ≤ 2^n / (k+1)
  -- For k ≥ 2^(n+1), this is ≤ 1/2
  apply summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num : (1:ℝ)/2 < 1)
  -- Need to show: eventually ‖f(k+1)‖ ≤ (1/2) * ‖f(k)‖
  filter_upwards [Filter.eventually_ge_atTop (2^(n+1))] with k hk
  have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.two_pow_pos (n+1)) hk)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk_ne)
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  have hfk_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hfk1_pos : (0 : ℝ) < (k + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos (k + 1))
  have hkn_pos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos hk_pos n
  have hk1n_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ n := pow_pos hk1_pos n
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (div_pos hk1n_pos hfk1_pos), abs_of_pos (div_pos hkn_pos hfk_pos)]
  rw [Nat.factorial_succ, Nat.cast_mul]
  -- Simplify: ((k+1)^n / ((k+1) * k!)) ≤ (1/2) * (k^n / k!)
  -- Key: k+1 ≤ 2k for k ≥ 1, so (k+1)^n ≤ (2k)^n = 2^n * k^n
  -- Need 2^n / (k+1) ≤ 1/2, i.e., 2^(n+1) ≤ k+1, which holds since k ≥ 2^(n+1)
  have h1k : 1 ≤ k := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos (n+1)) hk)
  have h2k : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr h1k
    linarith
  have hk1n_bound : ((k + 1 : ℕ) : ℝ) ^ n ≤ (2 * (k : ℝ)) ^ n := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) h2k
  -- Main calculation
  have h2n1_le : (2 : ℝ) ^ (n + 1) ≤ ((k + 1 : ℕ) : ℝ) := by
    have : (2 : ℝ) ^ (n + 1) = ((2 ^ (n + 1) : ℕ) : ℝ) := by norm_cast
    rw [this]
    exact Nat.cast_le.mpr (Nat.le_succ_of_le hk)
  calc ((k + 1 : ℕ) : ℝ) ^ n / (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ))
      = ((k + 1 : ℕ) : ℝ) ^ n / ((k + 1 : ℕ) : ℝ) / (k.factorial : ℝ) := by ring
    _ ≤ (2 * (k : ℝ)) ^ n / ((k + 1 : ℕ) : ℝ) / (k.factorial : ℝ) := by
        apply div_le_div_of_nonneg_right
        · apply div_le_div_of_nonneg_right hk1n_bound hk1_pos.le
        · exact hfk_pos.le
    _ = 2 ^ n * (k : ℝ) ^ n / ((k + 1 : ℕ) : ℝ) / (k.factorial : ℝ) := by rw [mul_pow]
    _ ≤ 1/2 * ((k : ℝ) ^ n / (k.factorial : ℝ)) := by
        -- Goal: 2^n * k^n / (k+1) / k! ≤ (1/2) * k^n / k!
        -- This is equivalent to: 2^n / (k+1) ≤ 1/2
        -- Which is: 2^(n+1) ≤ k+1
        have hkf_ne : (k.factorial : ℝ) ≠ 0 := ne_of_gt hfk_pos
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hk1_pos
        -- Convert goal to simpler form
        have heq : (2 : ℝ) ^ n * (k : ℝ) ^ n / ((k + 1 : ℕ) : ℝ) / (k.factorial : ℝ) =
                   (k : ℝ) ^ n / (k.factorial : ℝ) * ((2 : ℝ) ^ n / ((k + 1 : ℕ) : ℝ)) := by
          rw [div_div, mul_comm (((k + 1 : ℕ) : ℝ)), ← div_div]
          rw [mul_div_assoc, mul_comm]
          rw [mul_div_assoc]
        rw [heq]
        -- Goal: k^n / k! * (2^n / (k+1)) ≤ (1/2) * k^n / k!
        have hkf_div_pos : 0 < (k : ℝ) ^ n / (k.factorial : ℝ) := div_pos hkn_pos hfk_pos
        rw [mul_comm ((k : ℝ) ^ n / (k.factorial : ℝ))]
        apply mul_le_mul_of_nonneg_right _ hkf_div_pos.le
        -- Goal: 2^n / (k+1) ≤ 1/2
        rw [div_le_div_iff₀ hk1_pos (by norm_num : (0:ℝ) < 2)]
        -- Goal: 2^n * 2 ≤ 1 * (k+1)
        simp only [one_mul]
        calc (2 : ℝ) ^ n * 2 = 2 ^ (n + 1) := by ring
          _ ≤ ((k + 1 : ℕ) : ℝ) := h2n1_le

/-! ## Summation Interchange (Fubini-style)

    We need to justify exchanging the order of summation:
    Σ_{k=0}^∞ Σ_{j=0}^n a_{k,j} = Σ_{j=0}^n Σ_{k=0}^∞ a_{k,j}

    Since the inner sum (over j) is finite, this follows from
    linearity of infinite series.
-/

/-- Interchange of finite and infinite sums -/
lemma tsum_sum_interchange {f : ℕ → ℕ → ℝ} (n : ℕ)
    (hf : ∀ j, j ≤ n → Summable (fun k => f k j)) :
    ∑' k : ℕ, ∑ j ∈ range (n + 1), f k j = ∑ j ∈ range (n + 1), ∑' k : ℕ, f k j := by
  -- Summable.tsum_finsetSum has form: ∑' b, ∑ i ∈ s, g i b = ∑ i ∈ s, ∑' b, g i b
  -- We need: ∑' k, ∑ j ∈ s, f k j = ∑ j ∈ s, ∑' k, f k j
  -- With g j k := f k j, the Mathlib lemma gives us what we want directly
  have hg : ∀ j ∈ range (n + 1), Summable (fun k => f k j) := by
    intro j hj
    exact hf j (Finset.mem_range_succ_iff.mp hj)
  exact Summable.tsum_finsetSum (f := fun j k => f k j) (s := range (n + 1)) hg

/-! ## Main Theorem: Dobinski's Formula -/

/-- Dobinski's Formula: B_n = (1/e) * Σ_{k=0}^∞ k^n / k!

    The Bell number B_n equals (1/e) times the sum of k^n/k! over all k.
    This connects the combinatorial definition of Bell numbers
    to an analytic series expression.
-/
theorem dobinski_formula (n : ℕ) :
    (bell n : ℝ) = (Real.exp 1)⁻¹ * ∑' k : ℕ, (k : ℝ) ^ n / (k.factorial : ℝ) := by
  -- Step 1: Expand k^n using power-Stirling expansion
  have h1 : ∀ k : ℕ, (k : ℝ) ^ n = ∑ j ∈ range (n + 1),
      (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j := fun k => power_stirling_expansion k n
  -- Step 2: Substitute into the sum and exchange order
  have h2 : ∑' k : ℕ, (k : ℝ) ^ n / (k.factorial : ℝ) =
      ∑' k : ℕ, (∑ j ∈ range (n + 1),
        (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j) / (k.factorial : ℝ) := by
    congr 1
    funext k
    rw [h1]
  -- Step 3: Distribute and interchange sums
  have h3 : ∑' k : ℕ, (∑ j ∈ range (n + 1),
        (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j) / (k.factorial : ℝ) =
      ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) *
        ∑' k : ℕ, fallingFactorial k j / (k.factorial : ℝ) := by
    -- First distribute division over finite sum
    have hdist : ∀ k : ℕ, (∑ j ∈ range (n + 1),
        (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j) / (k.factorial : ℝ) =
        ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j /
          (k.factorial : ℝ) := fun k =>
      Finset.sum_div (range (n + 1)) (fun j => (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j)
        (k.factorial : ℝ)
    simp_rw [hdist]
    -- Rewrite a * b / c as a * (b / c)
    have hrewrite : ∀ k : ℕ, ∀ j : ℕ,
        (Nat.stirlingSecond n j : ℝ) * fallingFactorial k j / (k.factorial : ℝ) =
        (Nat.stirlingSecond n j : ℝ) * (fallingFactorial k j / (k.factorial : ℝ)) := by
      intros; ring
    simp_rw [hrewrite]
    -- Interchange sums
    rw [tsum_sum_interchange n]
    · congr 1
      ext j
      rw [← tsum_mul_left]
    · intro j _
      have hsumm := summable_fallingFactorial_div_factorial j
      exact Summable.mul_left _ hsumm
  -- Step 4: Apply the key lemma: each inner sum equals e
  have h4 : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) *
      ∑' k : ℕ, fallingFactorial k j / (k.factorial : ℝ) =
      ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * Real.exp 1 := by
    congr 1
    ext j
    rw [tsum_fallingFactorial_div_factorial]
  -- Step 5: Factor out e
  have h5 : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * Real.exp 1 =
      Real.exp 1 * ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) := by
    rw [← Finset.sum_mul]
    ring
  -- Step 6: Apply definition of Bell number
  have h6 : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) = (bell n : ℝ) := by
    simp only [bell, Nat.cast_sum]
  -- Combine all steps
  calc (bell n : ℝ)
      = (Real.exp 1)⁻¹ * (Real.exp 1 * (bell n : ℝ)) := by
        field_simp [Real.exp_ne_zero]
    _ = (Real.exp 1)⁻¹ * (Real.exp 1 * ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ)) := by
        rw [h6]
    _ = (Real.exp 1)⁻¹ * ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * Real.exp 1 := by
        rw [h5]
    _ = (Real.exp 1)⁻¹ * ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) *
        ∑' k : ℕ, fallingFactorial k j / (k.factorial : ℝ) := by rw [← h4]
    _ = (Real.exp 1)⁻¹ * ∑' k : ℕ, (k : ℝ) ^ n / (k.factorial : ℝ) := by rw [← h3, ← h2]

end Alethfeld.Dobinski
