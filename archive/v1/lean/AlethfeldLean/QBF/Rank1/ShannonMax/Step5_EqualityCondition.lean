/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step5_EqualityCondition

  Step 5: Equality Characterization in Shannon Maximum Entropy

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-H-equality, :2-eq-fwd, :2-eq-gibbs, :2-eq-conclude
  Status: CLEAN

  Key Result: H(p) = log₂(3) if and only if p = (1/3, 1/3, 1/3).

  Proof Strategy:
  - Forward: H(p) = log₂(3) implies D(p||u) = 0 (from Gibbs expansion)
  - D(p||u) = 0 implies p = u (Gibbs equality condition)
  - Backward: If p = u, then H(u) = log₂(3) (computed directly)
-/
import AlethfeldLean.QBF.Rank1.ShannonMax.Step4_EntropyBound

namespace Alethfeld.QBF.Rank1.ShannonMax

open scoped BigOperators
open Real

/-! ## :2-eq-fwd - Connecting Entropy and KL Divergence

H(p) = log₂(3) iff D(p||u) = 0
-/

/-- Relationship between Shannon entropy and KL divergence from uniform -/
theorem entropy_kl_relation (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p = log2 3 - klDivergence p uniformDist / Real.log 2 := by
  -- H(p) = -Σᵢ pᵢ log₂(pᵢ)
  -- D(p||u) = Σᵢ pᵢ ln(pᵢ/(1/3)) = Σᵢ pᵢ ln(pᵢ) + Σᵢ pᵢ ln(3) = Σᵢ pᵢ ln(pᵢ) + ln(3)
  -- So D(p||u) / ln(2) = (Σᵢ pᵢ ln(pᵢ) + ln(3)) / ln(2) = Σᵢ pᵢ log₂(pᵢ) + log₂(3)
  -- Therefore: log₂(3) - D(p||u)/ln(2) = -Σᵢ pᵢ log₂(pᵢ) = H(p)
  rw [shannonEntropy_eq_neg_sum p hpos]
  unfold klDivergence log2
  have hlog2 : Real.log 2 > 0 := log_two_pos
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- Expand KL divergence terms
  simp only [Fin.sum_univ_three]
  -- Expand each klTerm
  have hkl0 : klTerm (p.p 0) (1/3) = p.p 0 * Real.log (p.p 0) + p.p 0 * Real.log 3 := by
    rw [klTerm_pos _ _ (hpos 0)]
    rw [show p.p 0 / (1/3) = p.p 0 * 3 by ring]
    rw [Real.log_mul (ne_of_gt (hpos 0)) (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hkl1 : klTerm (p.p 1) (1/3) = p.p 1 * Real.log (p.p 1) + p.p 1 * Real.log 3 := by
    rw [klTerm_pos _ _ (hpos 1)]
    rw [show p.p 1 / (1/3) = p.p 1 * 3 by ring]
    rw [Real.log_mul (ne_of_gt (hpos 1)) (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hkl2 : klTerm (p.p 2) (1/3) = p.p 2 * Real.log (p.p 2) + p.p 2 * Real.log 3 := by
    rw [klTerm_pos _ _ (hpos 2)]
    rw [show p.p 2 / (1/3) = p.p 2 * 3 by ring]
    rw [Real.log_mul (ne_of_gt (hpos 2)) (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  simp only [uniform_val]
  rw [hkl0, hkl1, hkl2]
  -- Use p.sum_eq_one
  have hsum : p.p 0 + p.p 1 + p.p 2 = 1 := by
    have := p.sum_eq_one
    simp only [Fin.sum_univ_three] at this
    exact this
  -- Simplify both sides algebraically
  -- LHS: -(p0 * log₂(p0) + p1 * log₂(p1) + p2 * log₂(p2))
  -- RHS: log₂(3) - (p0*ln(p0)+p0*ln(3) + p1*ln(p1)+p1*ln(3) + p2*ln(p2)+p2*ln(3)) / ln(2)
  --    = log₂(3) - ((p0+p1+p2)*ln(3) + p0*ln(p0)+p1*ln(p1)+p2*ln(p2)) / ln(2)
  --    = log₂(3) - (ln(3) + p0*ln(p0)+p1*ln(p1)+p2*ln(p2)) / ln(2)   [using hsum]
  --    = ln(3)/ln(2) - ln(3)/ln(2) - (p0*ln(p0)+p1*ln(p1)+p2*ln(p2)) / ln(2)
  --    = -(p0*ln(p0)+p1*ln(p1)+p2*ln(p2)) / ln(2)
  --    = -(p0*log₂(p0) + p1*log₂(p1) + p2*log₂(p2))
  field_simp
  -- RHS expands to: log 3 - (Σ pᵢ log pᵢ + log 3) = -Σ pᵢ log pᵢ = LHS
  have hlog3 : (p.p 0 + p.p 1 + p.p 2) * Real.log 3 = Real.log 3 := by rw [hsum, one_mul]
  linarith

/-- H(p) = log₂(3) iff D(p||u) = 0 (for positive distributions) -/
theorem entropy_eq_max_iff_kl_zero (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p = log2 3 ↔ klDivergence p uniformDist = 0 := by
  rw [entropy_kl_relation p hpos]
  have hlog2 : Real.log 2 > 0 := log_two_pos
  constructor
  · intro h
    -- log₂(3) = log₂(3) - D/ln(2) implies D = 0
    have : klDivergence p uniformDist / Real.log 2 = 0 := by linarith
    exact div_eq_zero_iff.mp this |>.resolve_right (ne_of_gt hlog2)
  · intro h
    rw [h]
    simp

/-! ## :2-eq-gibbs - Applying Gibbs Equality Condition

D(p||u) = 0 implies p = u
-/

/-- D(p||u) = 0 iff p = u -/
theorem kl_uniform_zero_iff (p : ProbDist3) :
    klDivergence p uniformDist = 0 ↔ p.p = uniformDist.p :=
  gibbs_equality_iff p uniformDist (fun _ => uniform_pos _)

/-! ## :1-H-equality - Main Equality Characterization

H(p) = log₂(3) iff p = (1/3, 1/3, 1/3)
-/

/-- Forward direction: If H(p) = log₂(3), then p = uniform -/
theorem entropy_max_implies_uniform (p : ProbDist3)
    (hpos : ∀ i, p.p i > 0) (hmax : shannonEntropy p = log2 3) :
    p.p = uniformDist.p := by
  rw [entropy_eq_max_iff_kl_zero p hpos] at hmax
  exact (kl_uniform_zero_iff p).mp hmax

/-- Backward direction: If p = uniform, then H(p) = log₂(3) -/
theorem uniform_entropy_is_max :
    shannonEntropy uniformDist = log2 3 := entropy_uniform

/-- Main equality characterization (for positive distributions) -/
theorem entropy_eq_max_iff_uniform (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p = log2 3 ↔ p.p = uniformDist.p := by
  constructor
  · exact entropy_max_implies_uniform p hpos
  · intro h
    -- If p.p = uniformDist.p, compute entropy directly
    unfold shannonEntropy
    simp only [h]
    exact entropy_uniform

/-! ## Corollaries -/

/-- If p ≠ uniform (and all positive), then H(p) < log₂(3) -/
theorem entropy_lt_max_of_not_uniform (p : ProbDist3)
    (hpos : ∀ i, p.p i > 0) (hne : p.p ≠ uniformDist.p) :
    shannonEntropy p < log2 3 := by
  have hle := entropy_le_log2_three_pos p hpos
  have hneq : shannonEntropy p ≠ log2 3 := by
    intro h
    exact hne ((entropy_eq_max_iff_uniform p hpos).mp h)
  exact lt_of_le_of_ne hle hneq

/-- Strict bound for non-uniform distributions -/
theorem entropy_strict_bound (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p ≤ log2 3 ∧
    (shannonEntropy p = log2 3 ↔ p.p = uniformDist.p) := by
  exact ⟨entropy_le_log2_three_pos p hpos, entropy_eq_max_iff_uniform p hpos⟩

end Alethfeld.QBF.Rank1.ShannonMax
