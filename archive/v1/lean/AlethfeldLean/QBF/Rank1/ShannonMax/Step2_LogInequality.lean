/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step2_LogInequality

  Step 2: The Fundamental Log Inequality

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-log-ineq, :2-def-f, :2-f-deriv, :2-f-min, :2-f-val, :2-f-nonneg,
             :2-log-ineq-conclude, :2-log-ineq-eq
  Status: CLEAN

  Key Result: For all x > 0: ln(x) ≤ x - 1, with equality iff x = 1.

  Proof Strategy:
  - Define f(x) = x - 1 - ln(x)
  - Show f'(x) = 1 - 1/x
  - Show x = 1 is the unique global minimum
  - Conclude f(x) ≥ f(1) = 0
-/
import AlethfeldLean.QBF.Rank1.ShannonMax.Step1_Definitions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace Alethfeld.QBF.Rank1.ShannonMax

open Real

/-! ## :2-def-f - Definition of f(x) = x - 1 - ln(x)

The key function for proving the log inequality.
-/

/-- The function f(x) = x - 1 - ln(x) for x > 0 -/
noncomputable def f (x : ℝ) : ℝ := x - 1 - Real.log x

/-! ## :2-f-val - Value at x = 1

f(1) = 1 - 1 - ln(1) = 0
-/

/-- f(1) = 0 -/
theorem f_one : f 1 = 0 := by
  unfold f
  simp [Real.log_one]

/-! ## :1-log-ineq - The Fundamental Log Inequality

For all x > 0: ln(x) ≤ x - 1, with equality iff x = 1.

We use Mathlib's Real.add_one_le_exp and related lemmas.
-/

/-- The log inequality: ln(x) ≤ x - 1 for x > 0 -/
theorem log_le_sub_one {x : ℝ} (hx : x > 0) : Real.log x ≤ x - 1 := by
  have h := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at h
  linarith

/-- Equivalent form: x - 1 - ln(x) ≥ 0 for x > 0 -/
theorem f_nonneg {x : ℝ} (hx : x > 0) : f x ≥ 0 := by
  unfold f
  have h := log_le_sub_one hx
  linarith

/-- Equality condition: ln(x) = x - 1 iff x = 1 -/
theorem log_eq_sub_one_iff {x : ℝ} (hx : x > 0) : Real.log x = x - 1 ↔ x = 1 := by
  constructor
  · intro h
    -- If ln(x) = x - 1, then f(x) = 0
    -- Use strict convexity of exp: exp(t) > 1 + t for t ≠ 0
    -- Setting t = ln(x), we get x > 1 + ln(x) for x ≠ 1
    by_contra hne
    have hlog_ne : Real.log x ≠ 0 := by
      intro heq
      have hx_eq_one : x = 1 := Real.eq_one_of_pos_of_log_eq_zero hx heq
      exact hne hx_eq_one
    have hexp_strict := Real.add_one_lt_exp hlog_ne
    rw [Real.exp_log hx] at hexp_strict
    -- hexp_strict: log x + 1 < x, i.e., log x < x - 1
    linarith
  · intro h
    rw [h, Real.log_one]
    ring

/-- f(x) = 0 iff x = 1 -/
theorem f_eq_zero_iff {x : ℝ} (hx : x > 0) : f x = 0 ↔ x = 1 := by
  unfold f
  rw [sub_sub, sub_eq_zero]
  constructor
  · intro h
    have heq : Real.log x = x - 1 := by linarith
    exact (log_eq_sub_one_iff hx).mp heq
  · intro h
    rw [h, Real.log_one]
    ring

/-- Strict inequality for x ≠ 1: ln(x) < x - 1 -/
theorem log_lt_sub_one {x : ℝ} (hx : x > 0) (hne : x ≠ 1) : Real.log x < x - 1 := by
  have hlog_ne : Real.log x ≠ 0 := by
    intro heq
    have hx_eq_one : x = 1 := Real.eq_one_of_pos_of_log_eq_zero hx heq
    exact hne hx_eq_one
  have hexp_strict := Real.add_one_lt_exp hlog_ne
  rw [Real.exp_log hx] at hexp_strict
  linarith

/-! ## Derived Forms for Gibbs Inequality

These forms are used in the Gibbs inequality proof.
-/

/-- For x > 0: -ln(x) ≥ 1 - x -/
theorem neg_log_ge_one_sub {x : ℝ} (hx : x > 0) : -Real.log x ≥ 1 - x := by
  have h := log_le_sub_one hx
  linarith

/-- For x > 0: ln(1/x) ≥ 1 - x (using ln(1/x) = -ln(x)) -/
theorem log_inv_ge_one_sub {x : ℝ} (hx : x > 0) : Real.log (1/x) ≥ 1 - x := by
  rw [one_div, Real.log_inv]
  exact neg_log_ge_one_sub hx

/-- Equality in -ln(x) ≥ 1 - x iff x = 1 -/
theorem neg_log_eq_one_sub_iff {x : ℝ} (hx : x > 0) : -Real.log x = 1 - x ↔ x = 1 := by
  constructor
  · intro h
    have heq : Real.log x = x - 1 := by linarith
    exact (log_eq_sub_one_iff hx).mp heq
  · intro h
    rw [h, Real.log_one]
    ring

end Alethfeld.QBF.Rank1.ShannonMax
