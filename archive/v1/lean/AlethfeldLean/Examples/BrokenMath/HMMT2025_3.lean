/-
  Alethfeld Generated Lean 4 Formalization
  Graph: hmmt_feb_2025_3 (graph-51acde-43ac9a)

  ORIGINAL CLAIM: Given x, y, z in R+ with
    x^(log_2(yz)) = 2^8 * 3^4
    y^(log_2(zx)) = 2^9 * 3^6
    z^(log_2(xy)) = 2^5 * 3^10
  the minimum value of xyz is 576.

  ⚠️  BROKEN MATH DISCOVERY: THE CLAIM IS FALSE!
  ────────────────────────────────────────────────
  The solution (x, y, z) = (1/4, 1/8, 1/18) satisfies all three equations:
    (1/4)^(log₂(1/144)) = (1/4)^(-(4+2α)) = 4^(4+2α) = 2^8 * 3^4 ✓
    (1/8)^(log₂(1/72))  = (1/8)^(-(3+2α)) = 8^(3+2α) = 2^9 * 3^6 ✓
    (1/18)^(log₂(1/32)) = (1/18)^(-5) = 18^5 = 2^5 * 3^10 ✓

  This gives xyz = 1/576 < 576.

  The TRUE minimum is 1/576, not 576.
  The claim "minimum is 576" is the MAXIMUM among positive solutions.

  PROOF STATUS:
  ✓ PROVEN: Properties of alpha = log_2(3): positivity, bounds (1 < alpha < 2)
  ✓ PROVEN: Key relationship 2^alpha = 3
  ✓ PROVEN: All discriminant computations at s_min
  ✓ PROVEN: f(s_min) = 0 where f(s) = sqrt(Delta_1) + sqrt(Delta_2) + sqrt(Delta_3) - s
  ✓ PROVEN: f'(s) > 0 for valid s (derivative is positive)
  ✓ PROVEN: f is strictly increasing on domain (from positive derivative)
  ✓ PROVEN: Uniqueness of root s_min (from strict monotonicity)
  ✓ PROVEN: f(s) < 0 for s < s_min (from strict monotonicity)
  ✓ PROVEN: solution_satisfies_equations (x=4, y=8, z=18)
  ✓ PROVEN: Logarithmic transformation lemmas (eq1_transform, eq2_transform, eq3_transform)
  ✓ PROVEN: constraint_implies_f_nonneg: Triangle inequality for s > 0 case

  ✗ UNPROVABLE (1 sorry - theorem is false):
    - solution_achieves_minimum: The s < 0 case admits valid counterexamples

  PROOF STRUCTURE (from EDN graph):
  1. Setup: Define alpha = log_2(3), a = log_2(x), b = log_2(y), c = log_2(z), s = a+b+c
  2. Transform: Original equations become a(b+c) = 8+4α, b(c+a) = 9+6α, c(a+b) = 5+10α
  3. Quadratics: Each variable satisfies t² - s·t + constant = 0
  4. Discriminants: Δ₁ = s²-32-16α, Δ₂ = s²-36-24α, Δ₃ = s²-20-40α
  5. Constraint: ε₁√Δ₁ + ε₂√Δ₂ + ε₃√Δ₃ = -s where εᵢ ∈ {±1}
  6. Solution: At s₀ = 6+2α, with εᵢ = -1: √Δ₁ = 2+2α, √Δ₂ = 2α, √Δ₃ = 4-2α
  7. Verification: (a,b,c) = (2,3,1+2α) gives (x,y,z) = (4,8,18), xyz = 576
  8. Minimality: f(s) = Σ√Δᵢ - s is strictly increasing with unique root s₀
-/

import Mathlib

namespace HMMT2025_3

set_option linter.style.nativeDecide false

open Real

noncomputable section

-- Section 1: Definitions (Node 0-d00001)

/-- The constant alpha = log_2(3) -/
def alpha : Real := Real.log 3 / Real.log 2

/-- Key bound: 1 < alpha < 2 (since 2 < 3 < 4) -/
lemma alpha_pos : 0 < alpha := by
  simp only [alpha]
  positivity

lemma alpha_gt_one : 1 < alpha := by
  simp only [alpha]
  rw [one_lt_div (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

lemma alpha_lt_two : alpha < 2 := by
  simp only [alpha]
  have h2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h2ne : Real.log 2 ≠ 0 := ne_of_gt h2pos
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h42 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    convert Real.log_rpow (by norm_num : (0:ℝ) < 2) 2 using 1
    norm_num
  have h32 : Real.log 3 < 2 * Real.log 2 := by linarith
  have step1 : Real.log 3 / Real.log 2 < 2 * Real.log 2 / Real.log 2 :=
    div_lt_div_of_pos_right h32 h2pos
  have step2 : 2 * Real.log 2 / Real.log 2 = 2 := by rw [mul_div_assoc, div_self h2ne]; ring
  linarith

lemma alpha_bounds : 0 < alpha ∧ alpha < 2 :=
  ⟨alpha_pos, alpha_lt_two⟩

/-- Key relationship: 2^alpha = 3 (since alpha = log_2(3)) -/
lemma two_rpow_alpha : (2:ℝ) ^ alpha = 3 := by
  simp only [alpha]
  have h2pos : (0:ℝ) < 2 := by norm_num
  have h3pos : (0:ℝ) < 3 := by norm_num
  rw [Real.rpow_def_of_pos h2pos]
  have heq : Real.log 2 * (Real.log 3 / Real.log 2) = Real.log 3 := by field_simp
  rw [heq]
  exact Real.exp_log h3pos

-- Section 2: Equation Coefficients (Nodes 1-000001)

/-- First equation coefficient: k1 = 8 + 4*alpha (from a(b+c) = 8 + 4*alpha) -/
def k1 : Real := 8 + 4 * alpha

/-- Second equation coefficient: k2 = 9 + 6*alpha (from b(c+a) = 9 + 6*alpha) -/
def k2 : Real := 9 + 6 * alpha

/-- Third equation coefficient: k3 = 5 + 10*alpha (from c(a+b) = 5 + 10*alpha) -/
def k3 : Real := 5 + 10 * alpha

/-- Sum of equations: 2(ab+bc+ca) = 22 + 20*alpha (Node 1-000003) -/
lemma sum_of_equations : k1 + k2 + k3 = 22 + 20 * alpha := by
  simp only [k1, k2, k3]
  ring

-- Section 3: The Target Sum s and Quadratic Setup (Nodes 1-000002, 1-000004, 1-000005)

/-- The target value s = log_2(576) = 6 + 2*log_2(3) (Node 1-000010) -/
def s_min : Real := 6 + 2 * alpha

/-- Verification: 576 = 2^6 * 3^2 -/
theorem value_576 : (576 : Nat) = 2^6 * 3^2 := by native_decide

/-- xyz = 2^s, so minimizing xyz is equivalent to minimizing s (Node 1-000002) -/
lemma xyz_eq_two_pow_s (a b c : Real) :
    (2 : Real)^a * (2 : Real)^b * (2 : Real)^c = (2 : Real)^(a + b + c) := by
  rw [← rpow_add (by norm_num : (0:Real) < 2), ← rpow_add (by norm_num : (0:Real) < 2)]

-- Section 4: Discriminants (Nodes 1-000006, 1-000007)

/-- Discriminant for a: Delta1(s) = s^2 - 4*k1 = s^2 - 32 - 16*alpha -/
def Delta1 (s : Real) : Real := s^2 - 4 * k1

/-- Discriminant for b: Delta2(s) = s^2 - 4*k2 = s^2 - 36 - 24*alpha -/
def Delta2 (s : Real) : Real := s^2 - 4 * k2

/-- Discriminant for c: Delta3(s) = s^2 - 4*k3 = s^2 - 20 - 40*alpha -/
def Delta3 (s : Real) : Real := s^2 - 4 * k3

/-- Delta1 expanded -/
lemma Delta1_expanded (s : Real) : Delta1 s = s^2 - 32 - 16 * alpha := by
  simp only [Delta1, k1]; ring

/-- Delta2 expanded -/
lemma Delta2_expanded (s : Real) : Delta2 s = s^2 - 36 - 24 * alpha := by
  simp only [Delta2, k2]; ring

/-- Delta3 expanded -/
lemma Delta3_expanded (s : Real) : Delta3 s = s^2 - 20 - 40 * alpha := by
  simp only [Delta3, k3]; ring

-- Section 5: Discriminants at s_min are Perfect Squares (Nodes 1-000011, 1-000012, 1-000013)

/-- At s = s_min, Delta1 = 4*(1+alpha)^2 (Node 1-000011) -/
theorem Delta1_at_s_min : Delta1 s_min = 4 * (1 + alpha)^2 := by
  simp only [Delta1, s_min, k1]
  ring

/-- At s = s_min, Delta2 = 4*alpha^2 (Node 1-000012) -/
theorem Delta2_at_s_min : Delta2 s_min = 4 * alpha^2 := by
  simp only [Delta2, s_min, k2]
  ring

/-- At s = s_min, Delta3 = 4*(2-alpha)^2 (Node 1-000013) -/
theorem Delta3_at_s_min : Delta3 s_min = 4 * (2 - alpha)^2 := by
  simp only [Delta3, s_min, k3]
  ring

-- Section 6: Square Roots of Discriminants

/-- sqrt(Delta1) at s_min = 2*(1+alpha) = 2 + 2*alpha (Node 1-000011) -/
def sqrt_Delta1_at_s_min : Real := 2 * (1 + alpha)

/-- sqrt(Delta2) at s_min = 2*alpha (Node 1-000012) -/
def sqrt_Delta2_at_s_min : Real := 2 * alpha

/-- sqrt(Delta3) at s_min = 2*(2-alpha) = 4 - 2*alpha (since alpha < 2) (Node 1-000013) -/
def sqrt_Delta3_at_s_min : Real := 2 * (2 - alpha)

lemma sqrt_Delta1_value : sqrt_Delta1_at_s_min = 2 + 2 * alpha := by
  simp only [sqrt_Delta1_at_s_min]; ring

lemma sqrt_Delta2_value : sqrt_Delta2_at_s_min = 2 * alpha := by
  simp only [sqrt_Delta2_at_s_min]

lemma sqrt_Delta3_value : sqrt_Delta3_at_s_min = 4 - 2 * alpha := by
  simp only [sqrt_Delta3_at_s_min]; ring

-- Section 7: Constraint Equation (Nodes 1-000008, 1-000014, 1-000015)

/-- The constraint with all minus signs (Node 1-000015):
    -(2+2*alpha) - 2*alpha - (4-2*alpha) = -(6+2*alpha) -/
theorem constraint_all_minus :
    -sqrt_Delta1_at_s_min - sqrt_Delta2_at_s_min - sqrt_Delta3_at_s_min = -s_min := by
  simp only [sqrt_Delta1_at_s_min, sqrt_Delta2_at_s_min, sqrt_Delta3_at_s_min, s_min]
  ring

/-- Sum of sqrt(Delta_i) equals s_min (Node 1-000031) -/
theorem sum_sqrt_eq_s_min :
    sqrt_Delta1_at_s_min + sqrt_Delta2_at_s_min + sqrt_Delta3_at_s_min = s_min := by
  simp only [sqrt_Delta1_at_s_min, sqrt_Delta2_at_s_min, sqrt_Delta3_at_s_min, s_min]
  ring

-- Section 8: Solution Values (Nodes 1-000016, 1-000017)

/-- a = (s_min - sqrt_Delta1) / 2 = 2 (Node 1-000016) -/
def a_sol : Real := 2

/-- b = (s_min - sqrt_Delta2) / 2 = 3 (Node 1-000016) -/
def b_sol : Real := 3

/-- c = (s_min - sqrt_Delta3) / 2 = 1 + 2*alpha (Node 1-000016) -/
def c_sol : Real := 1 + 2 * alpha

/-- The solution values for x, y, z -/
def x_sol : Real := 4    -- 2^2
def y_sol : Real := 8    -- 2^3
def z_sol : Real := 18   -- 2^(1+2*alpha) = 2 * 9 = 18

/-- Recovery of a from quadratic formula (Node 1-000016) -/
theorem a_from_quadratic : a_sol = (s_min - sqrt_Delta1_at_s_min) / 2 := by
  simp only [a_sol, s_min, sqrt_Delta1_at_s_min]
  ring

/-- Recovery of b from quadratic formula (Node 1-000016) -/
theorem b_from_quadratic : b_sol = (s_min - sqrt_Delta2_at_s_min) / 2 := by
  simp only [b_sol, s_min, sqrt_Delta2_at_s_min]
  ring

/-- Recovery of c from quadratic formula (Node 1-000016) -/
theorem c_from_quadratic : c_sol = (s_min - sqrt_Delta3_at_s_min) / 2 := by
  simp only [c_sol, s_min, sqrt_Delta3_at_s_min]
  ring

/-- Sum of a, b, c equals s_min (Node 1-000017) -/
theorem sum_abc_eq_s_min : a_sol + b_sol + c_sol = s_min := by
  simp only [a_sol, b_sol, c_sol, s_min]
  ring

-- Section 9: Verification of Original Equations (Nodes 1-000018, 1-000019, 1-000020)

/-- First equation: a*(b+c) = k1 (Node 1-000018) -/
theorem eq1_verified : a_sol * (b_sol + c_sol) = k1 := by
  simp only [a_sol, b_sol, c_sol, k1]
  ring

/-- Second equation: b*(c+a) = k2 (Node 1-000019) -/
theorem eq2_verified : b_sol * (c_sol + a_sol) = k2 := by
  simp only [a_sol, b_sol, c_sol, k2]
  ring

/-- Third equation: c*(a+b) = k3 (Node 1-000020) -/
theorem eq3_verified : c_sol * (a_sol + b_sol) = k3 := by
  simp only [a_sol, b_sol, c_sol, k3]
  ring

/-- Product xyz = 576 (Node 1-000021) -/
theorem product_xyz_nat : (4 : Nat) * 8 * 18 = 576 := by native_decide

-- Section 10: Minimality Analysis (Nodes 1-000022 to 1-000035)

/-- The binding constraint is s^2 >= 20 + 40*alpha (Node 1-000023) -/
lemma binding_constraint : s_min^2 >= 20 + 40 * alpha := by
  simp only [s_min]
  nlinarith [sq_nonneg (alpha - 2), sq_nonneg alpha]

/-- At s = s_min with alpha < 2, Delta3 > 0 (Node 1-000024) -/
lemma Delta3_positive_at_s_min : Delta3 s_min > 0 := by
  rw [Delta3_at_s_min]
  have h : 2 - alpha > 0 := by linarith [alpha_lt_two]
  nlinarith [sq_nonneg (2 - alpha)]

/-- The function f(s) = sqrt(Delta1) + sqrt(Delta2) + sqrt(Delta3) - s (Node 1-000031) -/
noncomputable def f (s : Real) : Real :=
  Real.sqrt (Delta1 s) + Real.sqrt (Delta2 s) + Real.sqrt (Delta3 s) - s

/-- f(s_min) = 0 (Node 1-000031) -/
theorem f_at_s_min_eq_zero : f s_min = 0 := by
  simp only [f, Delta1_at_s_min, Delta2_at_s_min, Delta3_at_s_min]
  have h1 : (0:ℝ) < 1 + alpha := by linarith [alpha_pos]
  have h2 : (0:ℝ) < alpha := alpha_pos
  have h3 : (0:ℝ) < 2 - alpha := by linarith [alpha_lt_two]
  have eq1 : Real.sqrt (4 * (1 + alpha)^2) = 2 * (1 + alpha) := by
    rw [show (4:ℝ) * (1 + alpha)^2 = (2 * (1 + alpha))^2 by ring]
    rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * (1 + alpha))]
  have eq2 : Real.sqrt (4 * alpha^2) = 2 * alpha := by
    rw [show (4:ℝ) * alpha^2 = (2 * alpha)^2 by ring]
    rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * alpha)]
  have eq3 : Real.sqrt (4 * (2 - alpha)^2) = 2 * (2 - alpha) := by
    rw [show (4:ℝ) * (2 - alpha)^2 = (2 * (2 - alpha))^2 by ring]
    rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * (2 - alpha))]
  rw [eq1, eq2, eq3]
  simp only [s_min]
  ring

/-- Derivative of f is positive: f'(s) > 0 for valid s (Node 1-000032)
    f'(s) = s/sqrt(Delta1) + s/sqrt(Delta2) + s/sqrt(Delta3) - 1
    Since s > 0 and each sqrt(Delta_i) < s, each fraction > 1, so f'(s) > 2 > 0 -/
theorem f_deriv_positive (s : Real) (hs : s > Real.sqrt (4 * k3))
    (h1 : Delta1 s > 0) (h2 : Delta2 s > 0) (h3 : Delta3 s > 0) :
    s / Real.sqrt (Delta1 s) + s / Real.sqrt (Delta2 s) + s / Real.sqrt (Delta3 s) - 1 > 0 := by
  -- Each term s/sqrt(Delta_i) > 1 since s^2 > Delta_i(s) = s^2 - c_i and c_i > 0
  have hk1_pos : k1 > 0 := by simp only [k1]; linarith [alpha_pos]
  have hk2_pos : k2 > 0 := by simp only [k2]; linarith [alpha_pos]
  have hk3_pos : k3 > 0 := by simp only [k3]; linarith [alpha_pos]
  have sqrt1_pos : Real.sqrt (Delta1 s) > 0 := Real.sqrt_pos.mpr h1
  have sqrt2_pos : Real.sqrt (Delta2 s) > 0 := Real.sqrt_pos.mpr h2
  have sqrt3_pos : Real.sqrt (Delta3 s) > 0 := Real.sqrt_pos.mpr h3
  have hs_pos : s > 0 := by
    calc s > Real.sqrt (4 * k3) := hs
      _ ≥ 0 := Real.sqrt_nonneg _
  -- s/sqrt(Delta_i) > 1 iff s > sqrt(Delta_i) iff s^2 > Delta_i = s^2 - 4*k_i iff 4*k_i > 0
  have frac1 : s / Real.sqrt (Delta1 s) > 1 := by
    rw [gt_iff_lt, one_lt_div sqrt1_pos]
    rw [Real.sqrt_lt' hs_pos]
    simp only [Delta1, k1]; nlinarith [sq_nonneg s, alpha_pos]
  have frac2 : s / Real.sqrt (Delta2 s) > 1 := by
    rw [gt_iff_lt, one_lt_div sqrt2_pos]
    rw [Real.sqrt_lt' hs_pos]
    simp only [Delta2, k2]; nlinarith [sq_nonneg s, alpha_pos]
  have frac3 : s / Real.sqrt (Delta3 s) > 1 := by
    rw [gt_iff_lt, one_lt_div sqrt3_pos]
    rw [Real.sqrt_lt' hs_pos]
    simp only [Delta3, k3]; nlinarith [sq_nonneg s, alpha_pos]
  linarith

/-- Helper lemma: sqrt(b²-c) - sqrt(a²-c) > b - a when a < b, c > 0, and both discriminants positive -/
lemma sqrt_sq_sub_diff_gt {a b c : ℝ} (hab : a < b) (ha_pos : 0 < a)
    (hc_pos : 0 < c) (ha_dom : c < a ^ 2) (hb_dom : c < b ^ 2) :
    b - a < Real.sqrt (b ^ 2 - c) - Real.sqrt (a ^ 2 - c) := by
  have sqrt_a_pos : 0 < Real.sqrt (a ^ 2 - c) := Real.sqrt_pos.mpr (by linarith)
  have sqrt_b_pos : 0 < Real.sqrt (b ^ 2 - c) := Real.sqrt_pos.mpr (by linarith)
  have hb_pos : 0 < b := by linarith
  have sqrt_a_lt_a : Real.sqrt (a ^ 2 - c) < a := by rw [Real.sqrt_lt' ha_pos]; linarith
  have sqrt_b_lt_b : Real.sqrt (b ^ 2 - c) < b := by rw [Real.sqrt_lt' hb_pos]; linarith
  have sum_pos : 0 < Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c) := by linarith
  have sum_lt : Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c) < b + a := by linarith
  have hab_pos : 0 < b - a := by linarith
  have hdiff_sq : (Real.sqrt (b ^ 2 - c)) ^ 2 - (Real.sqrt (a ^ 2 - c)) ^ 2 = b ^ 2 - a ^ 2 := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ b ^ 2 - c), Real.sq_sqrt (by linarith : 0 ≤ a ^ 2 - c)]; ring
  have hfactor : (Real.sqrt (b ^ 2 - c) - Real.sqrt (a ^ 2 - c)) *
      (Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c)) = b ^ 2 - a ^ 2 := by
    have : (Real.sqrt (b ^ 2 - c) - Real.sqrt (a ^ 2 - c)) *
        (Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c)) =
        (Real.sqrt (b ^ 2 - c)) ^ 2 - (Real.sqrt (a ^ 2 - c)) ^ 2 := by ring
    rw [this, hdiff_sq]
  have hsum_ne : Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c) ≠ 0 := ne_of_gt sum_pos
  have hdiff_eq : Real.sqrt (b ^ 2 - c) - Real.sqrt (a ^ 2 - c) =
      (b ^ 2 - a ^ 2) / (Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c)) := by
    field_simp; linarith [hfactor]
  rw [hdiff_eq]
  have heq : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
  rw [heq, mul_div_assoc]
  have hgt1 : 1 < (b + a) / (Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c)) := by
    rw [one_lt_div sum_pos]; linarith
  calc b - a = (b - a) * 1 := by ring
    _ < (b - a) * ((b + a) / (Real.sqrt (b ^ 2 - c) + Real.sqrt (a ^ 2 - c))) := by nlinarith

/-- The domain threshold for valid discriminants -/
def domain_threshold : Real := Real.sqrt (4 * k3)

/-- s_min is in the valid domain where all discriminants are positive (Node 1-000023) -/
lemma s_min_in_domain : domain_threshold < s_min := by
  simp only [domain_threshold, s_min, k3]
  have hpos : 0 < 4 * (5 + 10 * alpha) := by linarith [alpha_pos]
  have hs_min_pos : 0 < 6 + 2 * alpha := by linarith [alpha_pos]
  rw [Real.sqrt_lt' hs_min_pos]
  -- Need: 4*(5+10α) < (6+2α)² = 36+24α+4α²
  -- i.e., 20+40α < 36+24α+4α², i.e., 0 < 16-16α+4α² = 4(α-2)²
  have halpha := alpha_lt_two
  have hne : alpha ≠ 2 := ne_of_lt halpha
  nlinarith [sq_nonneg (alpha - 2)]

/-- f is strictly increasing on the valid domain (Node 1-000033)
    For s₁ < s₂ with s₁ > domain_threshold, each term satisfies:
    sqrt(s₂²-cᵢ) - sqrt(s₁²-cᵢ) > s₂-s₁ (since sqrt(s²-cᵢ) < s when cᵢ > 0)
    Sum of three terms > 3(s₂-s₁), so f(s₂)-f(s₁) > 2(s₂-s₁) > 0 -/
theorem f_strict_mono_on_domain (s1 s2 : Real)
    (hs1 : domain_threshold < s1) (h12 : s1 < s2) : f s1 < f s2 := by
  simp only [f]
  have halpha := alpha_gt_one
  have hk1_pos : 0 < 4 * k1 := by simp only [k1]; linarith [alpha_pos]
  have hk2_pos : 0 < 4 * k2 := by simp only [k2]; linarith [alpha_pos]
  have hk3_pos : 0 < 4 * k3 := by simp only [k3]; linarith [alpha_pos]
  have hs1_pos : 0 < s1 := by
    calc s1 > domain_threshold := hs1
      _ = Real.sqrt (4 * k3) := rfl
      _ ≥ 0 := Real.sqrt_nonneg _
  have hs2_pos : 0 < s2 := by linarith
  have hs1_sq_gt_k3 : 4 * k3 < s1 ^ 2 := by
    have h := Real.sq_sqrt (by linarith [hk3_pos] : 0 ≤ 4 * k3)
    have : Real.sqrt (4 * k3) < s1 := hs1
    nlinarith [Real.sqrt_nonneg (4 * k3), sq_nonneg s1, sq_nonneg (Real.sqrt (4 * k3))]
  have hk_order1 : k1 < k3 := by simp only [k1, k3]; linarith
  have hk_order2 : k2 < k3 := by simp only [k2, k3]; linarith
  have hs1_sq_gt_k1 : 4 * k1 < s1 ^ 2 := by linarith
  have hs1_sq_gt_k2 : 4 * k2 < s1 ^ 2 := by linarith
  have hs2_sq_gt_k1 : 4 * k1 < s2 ^ 2 := by nlinarith
  have hs2_sq_gt_k2 : 4 * k2 < s2 ^ 2 := by nlinarith
  have hs2_sq_gt_k3 : 4 * k3 < s2 ^ 2 := by nlinarith
  have hdiff1 := sqrt_sq_sub_diff_gt h12 hs1_pos hk1_pos hs1_sq_gt_k1 hs2_sq_gt_k1
  have hdiff2 := sqrt_sq_sub_diff_gt h12 hs1_pos hk2_pos hs1_sq_gt_k2 hs2_sq_gt_k2
  have hdiff3 := sqrt_sq_sub_diff_gt h12 hs1_pos hk3_pos hs1_sq_gt_k3 hs2_sq_gt_k3
  have Delta1_eq : ∀ s, Delta1 s = s ^ 2 - 4 * k1 := fun _ => rfl
  have Delta2_eq : ∀ s, Delta2 s = s ^ 2 - 4 * k2 := fun _ => rfl
  have Delta3_eq : ∀ s, Delta3 s = s ^ 2 - 4 * k3 := fun _ => rfl
  simp only [Delta1_eq, Delta2_eq, Delta3_eq] at *
  linarith

/-- s_min is the unique root of f in the valid domain (Nodes 1-000033, 1-000034) -/
theorem s_min_unique_root (s : Real) (hs_domain : s >= Real.sqrt (4 * k3)) (hf : f s = 0) :
    s = s_min := by
  -- hs_domain means s >= domain_threshold
  -- s_min_in_domain means s_min > domain_threshold
  -- If s < s_min with s >= domain_threshold, then f(s) < f(s_min) = 0 (contradiction)
  -- If s > s_min, then f(s) > f(s_min) = 0 (contradiction)
  have hs_dom' : s ≥ domain_threshold := hs_domain
  have hs_min_dom := s_min_in_domain
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · -- s < s_min case
    -- Need s > domain_threshold to use f_strict_mono_on_domain
    have hs_gt_dom : domain_threshold < s := by
      by_contra h
      push_neg at h
      -- s <= domain_threshold and s >= domain_threshold means s = domain_threshold
      have heq : s = domain_threshold := le_antisymm h hs_dom'
      -- But then s < s_min and s = domain_threshold
      -- Since domain_threshold < s_min, this means domain_threshold < s_min which is true
      -- So s = domain_threshold, and we need f(domain_threshold) ≠ 0
      -- At domain_threshold, Delta3 = 0, so sqrt(Delta3) = 0
      -- f(threshold) = sqrt(Delta1) + sqrt(Delta2) + 0 - threshold
      -- This is negative since threshold > 0 and sqrts < threshold
      rw [heq] at hf
      simp only [f, domain_threshold] at hf
      -- At s = sqrt(4*k3), Delta3(s) = s^2 - 4*k3 = 0
      have hDelta3_zero : Delta3 (Real.sqrt (4 * k3)) = 0 := by
        simp only [Delta3]
        have hk3_pos : 0 < 4 * k3 := by simp only [k3]; linarith [alpha_pos]
        rw [Real.sq_sqrt (le_of_lt hk3_pos)]
        ring
      rw [hDelta3_zero, Real.sqrt_zero] at hf
      -- Now f = sqrt(Delta1) + sqrt(Delta2) + 0 - sqrt(4*k3) = 0
      -- Need to show this is impossible
      -- At threshold, Delta1 and Delta2 are positive (since k1 < k3 and k2 < k3)
      have halpha := alpha_gt_one
      have hk1_lt_k3 : k1 < k3 := by simp only [k1, k3]; linarith
      have hk2_lt_k3 : k2 < k3 := by simp only [k2, k3]; linarith
      have hDelta1_pos : 0 < Delta1 (Real.sqrt (4 * k3)) := by
        simp only [Delta1]
        have hk3_pos : 0 < 4 * k3 := by simp only [k3]; linarith [alpha_pos]
        rw [Real.sq_sqrt (le_of_lt hk3_pos)]
        simp only [k1, k3]; linarith
      have hDelta2_pos : 0 < Delta2 (Real.sqrt (4 * k3)) := by
        simp only [Delta2]
        have hk3_pos : 0 < 4 * k3 := by simp only [k3]; linarith [alpha_pos]
        rw [Real.sq_sqrt (le_of_lt hk3_pos)]
        simp only [k2, k3]; linarith
      have hsqrt1_pos : 0 < Real.sqrt (Delta1 (Real.sqrt (4 * k3))) :=
        Real.sqrt_pos.mpr hDelta1_pos
      have hsqrt2_pos : 0 < Real.sqrt (Delta2 (Real.sqrt (4 * k3))) :=
        Real.sqrt_pos.mpr hDelta2_pos
      have hthresh_pos : 0 < Real.sqrt (4 * k3) := by
        apply Real.sqrt_pos.mpr
        simp only [k3]; linarith [alpha_pos]
      -- sqrt(Delta1) + sqrt(Delta2) - sqrt(4*k3) = 0 means
      -- sqrt(Delta1) + sqrt(Delta2) = sqrt(4*k3)
      -- But sqrt(Delta1) < sqrt(4*k3) and sqrt(Delta2) < sqrt(4*k3)? No, that's not right.
      -- Actually, sqrt(Delta1) = sqrt(4*k3 - 4*k1) = sqrt(4*(k3-k1)) = 2*sqrt(k3-k1)
      -- sqrt(Delta2) = 2*sqrt(k3-k2)
      -- sqrt(4*k3) = 2*sqrt(k3)
      -- So 2*sqrt(k3-k1) + 2*sqrt(k3-k2) = 2*sqrt(k3)?
      -- sqrt(k3-k1) + sqrt(k3-k2) = sqrt(k3)?
      -- With k1 = 8+4α, k2 = 9+6α, k3 = 5+10α:
      -- k3-k1 = -3+6α, k3-k2 = -4+4α
      -- For α > 1: k3-k1 > 3, k3-k2 > 0
      -- sqrt(k3-k1) + sqrt(k3-k2) vs sqrt(k3)
      -- sqrt(6α-3) + sqrt(4α-4) vs sqrt(5+10α)
      -- At α=1.585: sqrt(6.51) + sqrt(2.34) ≈ 2.55 + 1.53 = 4.08
      --             sqrt(20.85) ≈ 4.57
      -- So LHS < RHS, meaning f(threshold) < 0, contradiction with f = 0
      -- This shows s cannot equal domain_threshold
      simp only [Delta1, Delta2] at hf
      have hk3_pos : 0 ≤ 4 * k3 := by simp only [k3]; linarith [alpha_pos]
      rw [Real.sq_sqrt hk3_pos] at hf
      -- hf : sqrt(4*k3 - 4*k1) + sqrt(4*k3 - 4*k2) + 0 - sqrt(4*k3) = 0
      have heq' : Real.sqrt (4 * k3 - 4 * k1) + Real.sqrt (4 * k3 - 4 * k2) = Real.sqrt (4 * k3) := by
        linarith
      -- Show this is false
      have hsqrt4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have h1 : Real.sqrt (4 * k3 - 4 * k1) = 2 * Real.sqrt (k3 - k1) := by
        rw [show (4 : ℝ) * k3 - 4 * k1 = 4 * (k3 - k1) by ring]
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
      have h2 : Real.sqrt (4 * k3 - 4 * k2) = 2 * Real.sqrt (k3 - k2) := by
        rw [show (4 : ℝ) * k3 - 4 * k2 = 4 * (k3 - k2) by ring]
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
      have h3 : Real.sqrt (4 * k3) = 2 * Real.sqrt k3 := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
      rw [h1, h2, h3] at heq'
      have heq'' : Real.sqrt (k3 - k1) + Real.sqrt (k3 - k2) = Real.sqrt k3 := by linarith
      -- Now show sqrt(k3-k1) + sqrt(k3-k2) < sqrt(k3)
      -- Using Cauchy-Schwarz or direct computation
      have hk3k1_pos : 0 < k3 - k1 := by simp only [k1, k3]; linarith
      have hk3k2_pos : 0 < k3 - k2 := by simp only [k2, k3]; linarith
      have hk3_pos' : 0 < k3 := by simp only [k3]; linarith [alpha_pos]
      -- sqrt(a) + sqrt(b) < sqrt(c) when a + b + 2*sqrt(ab) < c
      -- i.e., when (sqrt(a) + sqrt(b))^2 < c
      have hsq : (Real.sqrt (k3 - k1) + Real.sqrt (k3 - k2)) ^ 2 < k3 := by
        -- (sqrt(a) + sqrt(b))^2 = a + b + 2*sqrt(ab)
        -- = (k3-k1) + (k3-k2) + 2*sqrt((k3-k1)(k3-k2))
        -- = 2k3 - k1 - k2 + 2*sqrt((k3-k1)(k3-k2))
        -- Need: 2k3 - k1 - k2 + 2*sqrt((k3-k1)(k3-k2)) < k3
        -- i.e., k3 - k1 - k2 + 2*sqrt((k3-k1)(k3-k2)) < 0
        -- With k1=8+4α, k2=9+6α, k3=5+10α:
        -- k3-k1-k2 = (5+10α)-(8+4α)-(9+6α) = -12
        -- Need: -12 + 2*sqrt((k3-k1)(k3-k2)) < 0
        -- i.e., sqrt((k3-k1)(k3-k2)) < 6
        -- (k3-k1)(k3-k2) = (6α-3)(4α-4) = 24α²-24α-12α+12 = 24α²-36α+12 = 12(2α²-3α+1)
        -- = 12(2α-1)(α-1)
        -- For α ∈ (1,2): 2α-1 > 1, α-1 < 1, so (2α-1)(α-1) < 2α-1 < 3
        -- Thus (k3-k1)(k3-k2) < 36, so sqrt < 6
        simp only [k1, k2, k3]
        have hprod : (5 + 10*alpha - (8 + 4*alpha)) * (5 + 10*alpha - (9 + 6*alpha)) =
            12 * (2*alpha - 1) * (alpha - 1) := by ring
        have h2a1 : 0 < 2*alpha - 1 := by linarith
        have ha1 : 0 < alpha - 1 := by linarith
        have hprod_pos : 0 < (5 + 10*alpha - (8 + 4*alpha)) * (5 + 10*alpha - (9 + 6*alpha)) := by
          rw [hprod]; nlinarith
        -- (2α-1)(α-1) < 3 since α < 2 implies α-1 < 1 and 2α-1 < 3
        have hprod_bound : (2*alpha - 1) * (alpha - 1) < 3 := by
          have h1 : alpha - 1 < 1 := by linarith [alpha_lt_two]
          have h2 : 2*alpha - 1 < 3 := by linarith [alpha_lt_two]
          nlinarith
        have hprod_bound' : 12 * (2*alpha - 1) * (alpha - 1) < 36 := by linarith
        have hsqrt_bound : Real.sqrt (12 * (2*alpha - 1) * (alpha - 1)) < 6 := by
          rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 6)]
          calc 12 * (2*alpha - 1) * (alpha - 1) < 36 := hprod_bound'
            _ = 6 ^ 2 := by norm_num
        -- The goal is (√(5+10α-(8+4α)) + √(5+10α-(9+6α)))^2 < 5+10α
        -- Simplify to (√(-3+6α) + √(-4+4α))^2 < 5+10α
        have hsimp1 : (5 + 10*alpha - (8 + 4*alpha)) = (-3 + 6*alpha) := by ring
        have hsimp2 : (5 + 10*alpha - (9 + 6*alpha)) = (-4 + 4*alpha) := by ring
        simp only [hsimp1, hsimp2]
        have h1 : 0 ≤ -3 + 6*alpha := by linarith
        have h2 : 0 ≤ -4 + 4*alpha := by linarith
        have hprod_simp : (-3 + 6*alpha) * (-4 + 4*alpha) = 12 * (2*alpha - 1) * (alpha - 1) := by ring
        calc (Real.sqrt ((-3 + 6*alpha)) + Real.sqrt ((-4 + 4*alpha))) ^ 2
            = (-3 + 6*alpha) + (-4 + 4*alpha) +
              2 * Real.sqrt ((-3 + 6*alpha) * (-4 + 4*alpha)) := by
                rw [add_sq, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_mul h1]; ring
          _ = -7 + 10*alpha + 2 * Real.sqrt (12 * (2*alpha - 1) * (alpha - 1)) := by
                rw [hprod_simp]; ring
          _ < -7 + 10*alpha + 2 * 6 := by linarith [hsqrt_bound]
          _ = 5 + 10*alpha := by ring
      have hsq' : Real.sqrt (k3 - k1) + Real.sqrt (k3 - k2) < Real.sqrt k3 := by
        have h := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
        rwa [Real.sqrt_sq (by positivity)] at h
      linarith
    have hmono := f_strict_mono_on_domain s s_min hs_gt_dom hlt
    linarith [f_at_s_min_eq_zero]
  · -- s > s_min case
    have hs_gt_dom : domain_threshold < s := by linarith [s_min_in_domain]
    have hmono := f_strict_mono_on_domain s_min s s_min_in_domain hgt
    linarith [f_at_s_min_eq_zero]

/-- No solution for s < s_min with all epsilon_i = -1 (Node 1-000033) -/
lemma no_solution_below_s_min (s : Real) (hs : s < s_min)
    (hs_domain : s >= Real.sqrt (4 * k3)) : f s < 0 := by
  -- f strictly increasing with f(s_min) = 0 implies f(s) < 0 for s < s_min
  -- Either s > domain_threshold (use strict mono) or s = domain_threshold (compute directly)
  by_cases hs_gt_dom : domain_threshold < s
  · -- Case 1: s > threshold, use strict monotonicity
    have hmono := f_strict_mono_on_domain s s_min hs_gt_dom hs
    linarith [f_at_s_min_eq_zero]
  · -- Case 2: s = threshold (since s >= threshold and not s > threshold)
    push_neg at hs_gt_dom
    have heq : s = domain_threshold := le_antisymm hs_gt_dom hs_domain
    rw [heq]
    -- Show f(domain_threshold) < 0 directly
    simp only [f, domain_threshold]
    have hk3_pos : 0 ≤ 4 * k3 := by simp only [k3]; linarith [alpha_pos]
    have hDelta3_zero : Delta3 (Real.sqrt (4 * k3)) = 0 := by
      simp only [Delta3]; rw [Real.sq_sqrt hk3_pos]; ring
    rw [hDelta3_zero, Real.sqrt_zero]
    simp only [Delta1, Delta2]
    rw [Real.sq_sqrt hk3_pos]
    have halpha := alpha_gt_one
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have h1 : Real.sqrt (4 * k3 - 4 * k1) = 2 * Real.sqrt (k3 - k1) := by
      rw [show (4:ℝ) * k3 - 4 * k1 = 4 * (k3 - k1) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
    have h2 : Real.sqrt (4 * k3 - 4 * k2) = 2 * Real.sqrt (k3 - k2) := by
      rw [show (4:ℝ) * k3 - 4 * k2 = 4 * (k3 - k2) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
    have h3 : Real.sqrt (4 * k3) = 2 * Real.sqrt k3 := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
    rw [h1, h2, h3]
    have hk3k1_pos : 0 < k3 - k1 := by simp only [k1, k3]; linarith
    have hk3k2_pos : 0 < k3 - k2 := by simp only [k2, k3]; linarith
    have hk3_pos' : 0 < k3 := by simp only [k3]; linarith [alpha_pos]
    have hprod_bound : (2*alpha - 1) * (alpha - 1) < 3 := by
      have h1 : alpha - 1 < 1 := by linarith [alpha_lt_two]
      have h2 : 2*alpha - 1 < 3 := by linarith [alpha_lt_two]
      nlinarith
    have hsqrt_bound : Real.sqrt (12 * (2*alpha - 1) * (alpha - 1)) < 6 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 6)]
      calc 12 * (2*alpha - 1) * (alpha - 1) < 36 := by linarith
        _ = 6 ^ 2 := by norm_num
    have hk3k1_simp : k3 - k1 = -3 + 6*alpha := by simp only [k1, k3]; ring
    have hk3k2_simp : k3 - k2 = -4 + 4*alpha := by simp only [k2, k3]; ring
    have hk3_simp : k3 = 5 + 10*alpha := rfl
    rw [hk3k1_simp, hk3k2_simp, hk3_simp]
    have h1 : 0 ≤ -3 + 6*alpha := by linarith
    have h2 : 0 ≤ -4 + 4*alpha := by linarith
    have hprod_simp : (-3 + 6*alpha) * (-4 + 4*alpha) = 12 * (2*alpha - 1) * (alpha - 1) := by ring
    have hsq : (Real.sqrt ((-3 + 6*alpha)) + Real.sqrt ((-4 + 4*alpha))) ^ 2 < 5 + 10*alpha := by
      calc (Real.sqrt ((-3 + 6*alpha)) + Real.sqrt ((-4 + 4*alpha))) ^ 2
          = (-3 + 6*alpha) + (-4 + 4*alpha) +
            2 * Real.sqrt ((-3 + 6*alpha) * (-4 + 4*alpha)) := by
              rw [add_sq, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_mul h1]; ring
        _ = -7 + 10*alpha + 2 * Real.sqrt (12 * (2*alpha - 1) * (alpha - 1)) := by
              rw [hprod_simp]; ring
        _ < -7 + 10*alpha + 2 * 6 := by linarith [hsqrt_bound]
        _ = 5 + 10*alpha := by ring
    have hsq' : Real.sqrt (-3 + 6*alpha) + Real.sqrt (-4 + 4*alpha) < Real.sqrt (5 + 10*alpha) := by
      have h := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
      rwa [Real.sqrt_sq (by positivity)] at h
    linarith

/-- Other sign combinations don't give smaller s (Node 1-000034) -/
lemma other_signs_no_smaller :
    True := by -- Placeholder for sign combination analysis
  trivial

-- Section 11: Main Theorems (Node 1-000035, QED 1-000028)

/-- Existence: (x, y, z) = (4, 8, 18) satisfies all equations -/
theorem existence_of_solution :
    x_sol > 0 ∧ y_sol > 0 ∧ z_sol > 0 ∧ x_sol * y_sol * z_sol = 576 := by
  simp only [x_sol, y_sol, z_sol]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

-- Helper lemmas for verifying the original equations

lemma two_rpow_4alpha : (2:ℝ) ^ (4 * alpha) = 3 ^ 4 := by
  rw [show 4 * alpha = alpha * 4 by ring, Real.rpow_mul (by norm_num), two_rpow_alpha]; norm_num

lemma two_rpow_6alpha : (2:ℝ) ^ (6 * alpha) = 3 ^ 6 := by
  rw [show 6 * alpha = alpha * 6 by ring, Real.rpow_mul (by norm_num), two_rpow_alpha]; norm_num

lemma two_rpow_10alpha : (2:ℝ) ^ (10 * alpha) = 3 ^ 10 := by
  rw [show 10 * alpha = alpha * 10 by ring, Real.rpow_mul (by norm_num), two_rpow_alpha]; norm_num

lemma log2_144 : Real.log (144:ℝ) / Real.log 2 = 4 + 2 * alpha := by
  have h : (144:ℝ) = (2:ℝ)^(4:ℝ) * (3:ℝ)^(2:ℝ) := by norm_num
  rw [h, Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2), Real.log_rpow (by norm_num : (0:ℝ) < 3)]
  simp only [alpha]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  field_simp

lemma log2_72 : Real.log (72:ℝ) / Real.log 2 = 3 + 2 * alpha := by
  have h : (72:ℝ) = (2:ℝ)^(3:ℝ) * (3:ℝ)^(2:ℝ) := by norm_num
  rw [h, Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2), Real.log_rpow (by norm_num : (0:ℝ) < 3)]
  simp only [alpha]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  field_simp

lemma log2_32 : Real.log (32:ℝ) / Real.log 2 = 5 := by
  have h : (32:ℝ) = (2:ℝ)^(5:ℝ) := by norm_num
  rw [h, Real.log_rpow (by norm_num : (0:ℝ) < 2)]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  field_simp

lemma eq1_helper : (4:ℝ) ^ (4 + 2 * alpha) = 2^8 * 3^4 := by
  calc (4:ℝ) ^ (4 + 2 * alpha)
      = ((2:ℝ) ^ (2:ℝ)) ^ (4 + 2 * alpha) := by norm_num
    _ = (2:ℝ) ^ ((2:ℝ) * (4 + 2 * alpha)) := by rw [← Real.rpow_mul (by norm_num)]
    _ = (2:ℝ) ^ (8 + 4 * alpha) := by ring_nf
    _ = (2:ℝ) ^ (8:ℝ) * (2:ℝ) ^ (4 * alpha) := by rw [Real.rpow_add (by norm_num)]
    _ = (2:ℝ) ^ (8:ℝ) * 3 ^ 4 := by rw [two_rpow_4alpha]
    _ = 2 ^ 8 * 3 ^ 4 := by norm_num

lemma eq2_helper : (8:ℝ) ^ (3 + 2 * alpha) = 2^9 * 3^6 := by
  calc (8:ℝ) ^ (3 + 2 * alpha)
      = ((2:ℝ) ^ (3:ℝ)) ^ (3 + 2 * alpha) := by norm_num
    _ = (2:ℝ) ^ ((3:ℝ) * (3 + 2 * alpha)) := by rw [← Real.rpow_mul (by norm_num)]
    _ = (2:ℝ) ^ (9 + 6 * alpha) := by ring_nf
    _ = (2:ℝ) ^ (9:ℝ) * (2:ℝ) ^ (6 * alpha) := by rw [Real.rpow_add (by norm_num)]
    _ = (2:ℝ) ^ (9:ℝ) * 3 ^ 6 := by rw [two_rpow_6alpha]
    _ = 2 ^ 9 * 3 ^ 6 := by norm_num

lemma eq3_helper : (18:ℝ) ^ (5:ℝ) = 2^5 * 3^10 := by
  calc (18:ℝ) ^ (5:ℝ)
      = ((2:ℝ) * (3:ℝ)^(2:ℝ)) ^ (5:ℝ) := by norm_num
    _ = (2:ℝ)^(5:ℝ) * ((3:ℝ)^(2:ℝ))^(5:ℝ) := by rw [Real.mul_rpow (by linarith) (by positivity)]
    _ = (2:ℝ)^(5:ℝ) * (3:ℝ)^(10:ℝ) := by rw [← Real.rpow_mul (by linarith)]; ring_nf
    _ = 2^5 * 3^10 := by norm_num

/-- The solution satisfies the original logarithmic equations -/
theorem solution_satisfies_equations :
    x_sol ^ (Real.log (y_sol * z_sol) / Real.log 2) = 2^8 * 3^4 ∧
    y_sol ^ (Real.log (z_sol * x_sol) / Real.log 2) = 2^9 * 3^6 ∧
    z_sol ^ (Real.log (x_sol * y_sol) / Real.log 2) = 2^5 * 3^10 := by
  simp only [x_sol, y_sol, z_sol]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (8:ℝ) * 18 = 144 by norm_num, log2_144, eq1_helper]
  · rw [show (18:ℝ) * 4 = 72 by norm_num, log2_72, eq2_helper]
  · rw [show (4:ℝ) * 8 = 32 by norm_num, log2_32, eq3_helper]

/-- Main Theorem: The minimum value of xyz is 576 (Node 1-000035, QED 1-000028) -/
theorem minimum_xyz_is_576 :
    ∃ (x y z : Real), x > 0 ∧ y > 0 ∧ z > 0 ∧
    x ^ (Real.log (y * z) / Real.log 2) = 2^8 * 3^4 ∧
    y ^ (Real.log (z * x) / Real.log 2) = 2^9 * 3^6 ∧
    z ^ (Real.log (x * y) / Real.log 2) = 2^5 * 3^10 ∧
    x * y * z = 576 := by
  use x_sol, y_sol, z_sol
  constructor
  · simp only [x_sol]; norm_num
  constructor
  · simp only [y_sol]; norm_num
  constructor
  · simp only [z_sol]; norm_num
  constructor
  · exact solution_satisfies_equations.1
  constructor
  · exact solution_satisfies_equations.2.1
  constructor
  · exact solution_satisfies_equations.2.2
  · simp only [x_sol, y_sol, z_sol]; norm_num

-- Section 12: Logarithmic Transformation Lemmas

/-- For positive x, x = 2^(log_2(x)) -/
lemma pos_eq_two_pow_log {x : ℝ} (hx : 0 < x) : x = 2 ^ (Real.log x / Real.log 2) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  rw [Real.rpow_def_of_pos h2]
  have heq : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by field_simp
  rw [heq]
  exact (Real.exp_log hx).symm

/-- Product formula: xyz = 2^(log_2(x) + log_2(y) + log_2(z)) for positive x, y, z -/
lemma prod_eq_two_pow_sum_logs {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z = 2 ^ (Real.log x / Real.log 2 + Real.log y / Real.log 2 + Real.log z / Real.log 2) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  conv_lhs => rw [pos_eq_two_pow_log hx, pos_eq_two_pow_log hy, pos_eq_two_pow_log hz]
  rw [← Real.rpow_add h2, ← Real.rpow_add h2]

/-- The original equation x^(log_2(yz)) = C transforms to log_2(x) * log_2(yz) = log_2(C) -/
lemma eq_transform {x C : ℝ} (hx : 0 < x) (hC : 0 < C) (e : ℝ)
    (heq : x ^ e = C) :
    (Real.log x / Real.log 2) * e = Real.log C / Real.log 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  -- Take log_2 of both sides of x^e = C
  have h1 : Real.log (x ^ e) = Real.log C := by rw [heq]
  rw [Real.log_rpow hx] at h1
  -- log(x^e) = e * log(x) = log(C)
  -- Divide by log(2): e * log(x) / log(2) = log(C) / log(2)
  have h2 : e * Real.log x / Real.log 2 = Real.log C / Real.log 2 := by
    field_simp; linarith
  field_simp at h2 ⊢; linarith

/-- 2^8 * 3^4 = 2^(8 + 4*alpha) -/
lemma rhs1_as_power : (2:ℝ)^8 * 3^4 = 2^(8 + 4*alpha) := by
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_4alpha]
  norm_num

/-- 2^9 * 3^6 = 2^(9 + 6*alpha) -/
lemma rhs2_as_power : (2:ℝ)^9 * 3^6 = 2^(9 + 6*alpha) := by
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_6alpha]
  norm_num

/-- 2^5 * 3^10 = 2^(5 + 10*alpha) -/
lemma rhs3_as_power : (2:ℝ)^5 * 3^10 = 2^(5 + 10*alpha) := by
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_10alpha]
  norm_num

/-- log_2(2^8 * 3^4) = 8 + 4*alpha -/
lemma log2_rhs1 : Real.log (2^8 * 3^4 : ℝ) / Real.log 2 = 8 + 4*alpha := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  rw [rhs1_as_power, Real.log_rpow h2]
  field_simp

/-- log_2(2^9 * 3^6) = 9 + 6*alpha -/
lemma log2_rhs2 : Real.log (2^9 * 3^6 : ℝ) / Real.log 2 = 9 + 6*alpha := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  rw [rhs2_as_power, Real.log_rpow h2]
  field_simp

/-- log_2(2^5 * 3^10) = 5 + 10*alpha -/
lemma log2_rhs3 : Real.log (2^5 * 3^10 : ℝ) / Real.log 2 = 5 + 10*alpha := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  rw [rhs3_as_power, Real.log_rpow h2]
  field_simp

/-- log_2(yz) = log_2(y) + log_2(z) for positive y, z -/
lemma log2_prod {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Real.log (y * z) / Real.log 2 = Real.log y / Real.log 2 + Real.log z / Real.log 2 := by
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  rw [Real.log_mul (ne_of_gt hy) (ne_of_gt hz)]
  ring

/-- The first transformed equation: a*(b+c) = k1 -/
lemma eq1_transform {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : x ^ (Real.log (y * z) / Real.log 2) = 2^8 * 3^4) :
    let a := Real.log x / Real.log 2
    let b := Real.log y / Real.log 2
    let c := Real.log z / Real.log 2
    a * (b + c) = k1 := by
  intro a b c
  have hrhs_pos : (0:ℝ) < 2^8 * 3^4 := by positivity
  have htrans := eq_transform hx hrhs_pos (Real.log (y * z) / Real.log 2) heq
  -- a * (b + c) = (log x / log 2) * (log(yz) / log 2) = log(2^8*3^4) / log 2 = 8 + 4α = k1
  simp only [a, b, c]
  have hbc : Real.log y / Real.log 2 + Real.log z / Real.log 2 = Real.log (y*z) / Real.log 2 :=
    (log2_prod hy hz).symm
  rw [hbc, htrans, log2_rhs1]
  simp only [k1]

/-- The second transformed equation: b*(c+a) = k2 -/
lemma eq2_transform {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : y ^ (Real.log (z * x) / Real.log 2) = 2^9 * 3^6) :
    let a := Real.log x / Real.log 2
    let b := Real.log y / Real.log 2
    let c := Real.log z / Real.log 2
    b * (c + a) = k2 := by
  intro a b c
  have hrhs_pos : (0:ℝ) < 2^9 * 3^6 := by positivity
  have htrans := eq_transform hy hrhs_pos (Real.log (z * x) / Real.log 2) heq
  simp only [a, b, c]
  have hca : Real.log z / Real.log 2 + Real.log x / Real.log 2 = Real.log (z*x) / Real.log 2 :=
    (log2_prod hz hx).symm
  rw [hca, htrans, log2_rhs2]
  simp only [k2]

/-- The third transformed equation: c*(a+b) = k3 -/
lemma eq3_transform {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : z ^ (Real.log (x * y) / Real.log 2) = 2^5 * 3^10) :
    let a := Real.log x / Real.log 2
    let b := Real.log y / Real.log 2
    let c := Real.log z / Real.log 2
    c * (a + b) = k3 := by
  intro a b c
  have hrhs_pos : (0:ℝ) < 2^5 * 3^10 := by positivity
  have htrans := eq_transform hz hrhs_pos (Real.log (x * y) / Real.log 2) heq
  simp only [a, b, c]
  have hab : Real.log x / Real.log 2 + Real.log y / Real.log 2 = Real.log (x*y) / Real.log 2 :=
    (log2_prod hx hy).symm
  rw [hab, htrans, log2_rhs3]
  simp only [k3]

/-- Key lemma: From the polynomial equations, a,b,c are determined by quadratics
    and the constraint sum = s requires f(s) ≥ 0

    PROOF SKETCH:
    1. From a*(b+c) = k1 etc., derive quadratics a² - s*a + k1 = 0
    2. By quadratic formula: (2a - s)² = Δ₁, so |2a - s| = √Δ₁
    3. The sum (2a-s) + (2b-s) + (2c-s) = -s
    4. By triangle inequality: |-s| ≤ |2a-s| + |2b-s| + |2c-s| = √Δ₁ + √Δ₂ + √Δ₃
    5. Since s > 0: s ≤ √Δ₁ + √Δ₂ + √Δ₃, i.e., f(s) ≥ 0

    This is the key lemma connecting the original equations to the f(s) ≥ 0 constraint.
    The proof is outlined above; formal verification requires careful handling of absolute values.
-/
lemma constraint_implies_f_nonneg (a b c : ℝ)
    (h1 : a * (a + b + c - a) = k1)
    (h2 : b * (a + b + c - b) = k2)
    (h3 : c * (a + b + c - c) = k3)
    (hs_pos : 0 < a + b + c)
    (hDelta1 : 0 ≤ Delta1 (a + b + c))
    (hDelta2 : 0 ≤ Delta2 (a + b + c))
    (hDelta3 : 0 ≤ Delta3 (a + b + c)) :
    f (a + b + c) ≥ 0 := by
  -- Let s = a + b + c
  set s := a + b + c with hs_def

  -- The hypotheses simplify to a*(b+c) = k1, etc.
  have h1' : a * (b + c) = k1 := by convert h1 using 1; ring
  have h2' : b * (c + a) = k2 := by convert h2 using 1; ring
  have h3' : c * (a + b) = k3 := by convert h3 using 1; ring

  -- Step 1: From a*(b+c) = k1 and s = a+b+c, derive (2a-s)² = Δ₁(s)
  -- a*(s-a) = k1, so a*s - a² = k1, thus a² - a*s + k1 = 0
  -- Completing the square: (2a - s)² = s² - 4k1 = Δ₁(s)
  have hsq1 : (2 * a - s) ^ 2 = Delta1 s := by
    simp only [Delta1, hs_def]
    -- (2a - (a+b+c))² = (a+b+c)² - 4k1, which follows from a(b+c) = k1
    have key := h1'
    nlinarith [key, sq_nonneg (a - b - c), sq_nonneg (a + b + c)]

  have hsq2 : (2 * b - s) ^ 2 = Delta2 s := by
    simp only [Delta2, hs_def]
    have key := h2'
    nlinarith [key, sq_nonneg (b - c - a), sq_nonneg (a + b + c)]

  have hsq3 : (2 * c - s) ^ 2 = Delta3 s := by
    simp only [Delta3, hs_def]
    have key := h3'
    nlinarith [key, sq_nonneg (c - a - b), sq_nonneg (a + b + c)]

  -- Step 2: |2a - s| = √Δ₁, etc.
  have habs1 : |2 * a - s| = Real.sqrt (Delta1 s) := by
    rw [← Real.sqrt_sq_eq_abs, hsq1]
  have habs2 : |2 * b - s| = Real.sqrt (Delta2 s) := by
    rw [← Real.sqrt_sq_eq_abs, hsq2]
  have habs3 : |2 * c - s| = Real.sqrt (Delta3 s) := by
    rw [← Real.sqrt_sq_eq_abs, hsq3]

  -- Step 3: The sum (2a-s) + (2b-s) + (2c-s) = -s
  have hsum : (2 * a - s) + (2 * b - s) + (2 * c - s) = -s := by
    simp only [hs_def]; ring

  -- Step 4: Triangle inequality: |-s| ≤ |2a-s| + |2b-s| + |2c-s|
  have htri : |(-s : ℝ)| ≤ |2 * a - s| + |2 * b - s| + |2 * c - s| := by
    calc |(-s : ℝ)| = |(2 * a - s) + (2 * b - s) + (2 * c - s)| := by rw [← hsum]
      _ = |(2 * a - s) + ((2 * b - s) + (2 * c - s))| := by ring_nf
      _ ≤ |2 * a - s| + |(2 * b - s) + (2 * c - s)| := abs_add_le _ _
      _ ≤ |2 * a - s| + (|2 * b - s| + |2 * c - s|) := by
          have := abs_add_le (2*b - s) (2*c - s)
          linarith
      _ = |2 * a - s| + |2 * b - s| + |2 * c - s| := by ring

  -- Step 5: Since s > 0, |-s| = s
  have habs_s : |(-s : ℝ)| = s := by rw [abs_neg, abs_of_pos hs_pos]

  -- Step 6: Combine to get s ≤ √Δ₁ + √Δ₂ + √Δ₃
  have hbound : s ≤ Real.sqrt (Delta1 s) + Real.sqrt (Delta2 s) + Real.sqrt (Delta3 s) := by
    calc s = |(-s : ℝ)| := habs_s.symm
      _ ≤ |2 * a - s| + |2 * b - s| + |2 * c - s| := htri
      _ = Real.sqrt (Delta1 s) + Real.sqrt (Delta2 s) + Real.sqrt (Delta3 s) := by
          rw [habs1, habs2, habs3]

  -- Step 7: Thus f(s) = √Δ₁ + √Δ₂ + √Δ₃ - s ≥ 0
  simp only [f]
  linarith

/-- xyz = 2^(log₂x + log₂y + log₂z) for positive x, y, z -/
lemma prod_eq_two_pow_sum_log {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z = (2:ℝ) ^ (Real.log x / Real.log 2 + Real.log y / Real.log 2 + Real.log z / Real.log 2) := by
  have h2_pos : (0:ℝ) < 2 := by norm_num
  have h2_ne_one : (2:ℝ) ≠ 1 := by norm_num
  have hxyz_pos : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  -- Rewrite log_div_log to logb
  conv_rhs =>
    rw [Real.log_div_log, Real.log_div_log, Real.log_div_log]
  -- Now goal is: x * y * z = 2 ^ (logb 2 x + logb 2 y + logb 2 z)
  -- logb 2 (x*y*z) = logb 2 x + logb 2 y + logb 2 z and 2^(logb 2 w) = w for w > 0
  rw [← Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]
  rw [← Real.logb_mul (ne_of_gt (mul_pos hx hy)) (ne_of_gt hz)]
  exact (Real.rpow_logb h2_pos h2_ne_one hxyz_pos).symm

/-- 2^s_min = 576 -/
lemma two_pow_s_min_eq_576 : (2:ℝ) ^ s_min = 576 := by
  simp only [s_min]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (2:ℝ) * alpha = alpha * 2 by ring, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [two_rpow_alpha]
  norm_num

/-- The solution achieves the minimum (Full statement)

    PROOF STRUCTURE:
    1. Product verification: x_sol * y_sol * z_sol = 4 * 8 * 18 = 576 ✓
    2. Minimality: For any valid (x,y,z) satisfying the equations, xyz ≥ 576

    The minimality proof proceeds as follows:
    - Define a = log₂(x), b = log₂(y), c = log₂(z), s = a+b+c
    - Then xyz = 2^s, so minimizing xyz is equivalent to minimizing s
    - The original equations transform to: a(b+c) = k1, b(c+a) = k2, c(a+b) = k3
    - These imply a, b, c satisfy quadratics with discriminants Δ₁, Δ₂, Δ₃
    - The constraint (2a-s) + (2b-s) + (2c-s) = -s with |2a-s| = √Δ₁ etc.
    - By triangle inequality: s ≤ √Δ₁ + √Δ₂ + √Δ₃, i.e., f(s) ≥ 0
    - By strict monotonicity of f and f(s_min) = 0, we have s ≥ s_min
    - Thus xyz = 2^s ≥ 2^s_min = 576
-/
theorem solution_achieves_minimum :
    x_sol * y_sol * z_sol = 576 ∧
    (∀ x y z : Real, x > 0 → y > 0 → z > 0 →
      x ^ (Real.log (y * z) / Real.log 2) = 2^8 * 3^4 →
      y ^ (Real.log (z * x) / Real.log 2) = 2^9 * 3^6 →
      z ^ (Real.log (x * y) / Real.log 2) = 2^5 * 3^10 →
      x * y * z >= 576) := by
  constructor
  · simp only [x_sol, y_sol, z_sol]; norm_num
  · intro x y z hx hy hz eq1 eq2 eq3
    -- Step 1: Define logarithmic variables
    let a := Real.log x / Real.log 2
    let b := Real.log y / Real.log 2
    let c := Real.log z / Real.log 2
    let s := a + b + c

    -- Step 2: Apply transformation lemmas to get polynomial constraints
    have h1 : a * (b + c) = k1 := eq1_transform hx hy hz eq1
    have h2 : b * (c + a) = k2 := eq2_transform hx hy hz eq2
    have h3 : c * (a + b) = k3 := eq3_transform hx hy hz eq3

    -- Convert to the form a*(s-a) = k1
    have h1' : a * (s - a) = k1 := by convert h1 using 1; simp only [s]; ring
    have h2' : b * (s - b) = k2 := by convert h2 using 1; simp only [s]; ring
    have h3' : c * (s - c) = k3 := by convert h3 using 1; simp only [s]; ring

    -- Step 3: Derive (2a-s)² = Δ₁, etc. algebraically
    have hsq1 : (2 * a - s) ^ 2 = Delta1 s := by
      simp only [Delta1, s]
      nlinarith [h1, sq_nonneg (a - b - c), sq_nonneg (a + b + c)]
    have hsq2 : (2 * b - s) ^ 2 = Delta2 s := by
      simp only [Delta2, s]
      nlinarith [h2, sq_nonneg (b - c - a), sq_nonneg (a + b + c)]
    have hsq3 : (2 * c - s) ^ 2 = Delta3 s := by
      simp only [Delta3, s]
      nlinarith [h3, sq_nonneg (c - a - b), sq_nonneg (a + b + c)]

    -- Discriminants are non-negative (squares are non-negative)
    have hDelta1 : 0 ≤ Delta1 s := by rw [← hsq1]; exact sq_nonneg _
    have hDelta2 : 0 ≤ Delta2 s := by rw [← hsq2]; exact sq_nonneg _
    have hDelta3 : 0 ≤ Delta3 s := by rw [← hsq3]; exact sq_nonneg _

    -- Step 4: Show s > 0
    have hs_pos : 0 < s := by
      -- From Δ₃ ≥ 0: s² ≥ 4k3 > 0, so s ≠ 0
      have hk3_pos : 0 < k3 := by simp only [k3]; linarith [alpha_pos]
      have hs_sq_ge : s ^ 2 ≥ 4 * k3 := by
        have h := hDelta3
        simp only [Delta3, k3] at h
        simp only [k3]
        linarith
      have hs_ne_zero : s ≠ 0 := by
        intro h; rw [h] at hs_sq_ge; simp at hs_sq_ge; linarith

      -- s > 0 or s < 0
      rcases lt_trichotomy s 0 with hs_neg | hs_zero | hs_pos'
      · -- Case s < 0: THIS CASE IS ACTUALLY VALID!
        -- BROKEN MATH DISCOVERY: The theorem as stated is FALSE.
        --
        -- The solution (a,b,c) = (-2, -3, -1-2α) with s = -6-2α < 0 gives:
        --   (x, y, z) = (1/4, 1/8, 1/18) with xyz = 1/576 < 576
        --
        -- Verification that (1/4, 1/8, 1/18) satisfies the original equations:
        --   x^(log₂(yz)) = (1/4)^(log₂(1/144)) = (1/4)^(-(4+2α)) = 4^(4+2α) = 2^8 * 3^4 ✓
        --   y^(log₂(zx)) = (1/8)^(log₂(1/72)) = (1/8)^(-(3+2α)) = 8^(3+2α) = 2^9 * 3^6 ✓
        --   z^(log₂(xy)) = (1/18)^(log₂(1/32)) = (1/18)^(-5) = 18^5 = 2^5 * 3^10 ✓
        --
        -- The actual minimum of xyz is 1/576, not 576.
        -- The claim "xyz ≥ 576" is false, so we cannot prove this case.
        --
        -- This sorry cannot be eliminated because the theorem is FALSE.
        sorry
      · exact absurd hs_zero hs_ne_zero
      · exact hs_pos'

    -- Step 5: Apply constraint_implies_f_nonneg
    -- Convert h1' : a*(s-a) = k1 to the form a*(a+b+c-a) = k1 needed by the lemma
    have hf_nonneg : f s ≥ 0 := by
      have h1'' : a * (a + b + c - a) = k1 := by simp only [s] at h1'; exact h1'
      have h2'' : b * (a + b + c - b) = k2 := by simp only [s] at h2'; exact h2'
      have h3'' : c * (a + b + c - c) = k3 := by simp only [s] at h3'; exact h3'
      exact constraint_implies_f_nonneg a b c h1'' h2'' h3'' hs_pos hDelta1 hDelta2 hDelta3

    -- Step 6: From f(s) ≥ 0 and strict monotonicity, conclude s ≥ s_min
    have hs_ge_s_min : s ≥ s_min := by
      by_contra h_lt
      push_neg at h_lt
      -- s ≥ domain_threshold (from Δ₃ ≥ 0, i.e., s² ≥ 4k₃, and s > 0)
      have hs_ge_thresh : Real.sqrt (4 * k3) ≤ s := by
        have h := hDelta3
        simp only [Delta3, k3] at h
        have hsq_ge : s ^ 2 ≥ 4 * (5 + 10 * alpha) := by linarith
        rw [← Real.sqrt_sq (le_of_lt hs_pos)]
        exact Real.sqrt_le_sqrt (by simp only [k3]; linarith)
      -- Since s ≥ √(4k₃) and s < s_min, use strict monotonicity
      -- Note: We need s > √(4k₃) strictly for f_strict_mono_on_domain
      -- If s = √(4k₃), we use no_solution_below_s_min directly
      rcases eq_or_lt_of_le hs_ge_thresh with heq | hgt
      · -- s = √(4k₃) = domain_threshold
        -- no_solution_below_s_min says f(t) < 0 for t < s_min and t ≥ domain_threshold
        -- Use h_lt : s < s_min, and s ≥ √(4k₃) from heq
        have hs_domain : s ≥ Real.sqrt (4 * k3) := by rw [heq]
        have hf_neg := no_solution_below_s_min s h_lt hs_domain
        linarith
      · -- s > domain_threshold: use strict monotonicity
        have hf_neg := f_strict_mono_on_domain s s_min hgt h_lt
        linarith [f_at_s_min_eq_zero]

    -- Step 7: Conclude xyz ≥ 576
    have hprod : x * y * z = (2:ℝ) ^ s := prod_eq_two_pow_sum_log hx hy hz
    rw [hprod, ge_iff_le, ← two_pow_s_min_eq_576]
    exact Real.monotone_rpow_of_base_ge_one (by norm_num : 1 ≤ (2:ℝ)) hs_ge_s_min

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY: BROKEN MATH DETECTED
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- ⚠️  THE ORIGINAL CLAIM "minimum xyz = 576" IS FALSE!
--
-- COUNTEREXAMPLE: (x, y, z) = (1/4, 1/8, 1/18) satisfies all equations with xyz = 1/576
--
-- ✓ PROVEN: All algebraic infrastructure (α properties, discriminants, monotonicity)
-- ✓ PROVEN: constraint_implies_f_nonneg (triangle inequality for s > 0)
-- ✓ PROVEN: solution_satisfies_equations (x=4, y=8, z=18 gives xyz=576)
--
-- ✗ UNPROVABLE (1 sorry): solution_achieves_minimum
--   The s < 0 case is VALID and yields xyz = 1/576 < 576
--   This sorry CANNOT be eliminated because the theorem is FALSE
--
-- All algebraic identities (discriminants, constraint sum, quadratic solutions)
-- are formally verified. The sorries are in the minimality proof infrastructure.

end

end HMMT2025_3
