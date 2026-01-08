/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step4_EntropyBound

  Step 4: Shannon Entropy Upper Bound

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-H-bound, :2-bound-inst through :2-bound-final
  Status: CLEAN

  Key Result: H(p) ≤ log₂(3) for any distribution p on 3 outcomes.
-/
import AlethfeldLean.QBF.Rank1.ShannonMax.Step3_GibbsInequality

namespace Alethfeld.QBF.Rank1.ShannonMax

open scoped BigOperators
open Real

/-! ## :2-bound-inst - Apply Gibbs with q = uniform -/

/-- Gibbs inequality specialized to uniform distribution -/
theorem gibbs_uniform (p : ProbDist3) :
    ∑ i, klTerm (p.p i) (uniformDist.p i) ≥ 0 :=
  gibbs_inequality p uniformDist (fun _ => uniform_pos _)

/-! ## Key Lemmas -/

/-- klTerm with uniform: pᵢ ln(3pᵢ) when pᵢ > 0 -/
theorem klTerm_uniform {p : ℝ} (hp : p > 0) :
    klTerm p (1/3) = p * Real.log (3 * p) := by
  rw [klTerm_pos p (1/3) hp]
  congr 1
  field_simp

/-- Sum of klTerms with uniform (for positive distributions) -/
theorem sum_klTerm_uniform (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    ∑ i, klTerm (p.p i) (1/3) = Real.log 3 + ∑ i, (p.p i * Real.log (p.p i)) := by
  -- Expand each term and collect
  have hexp : ∀ i, klTerm (p.p i) (1/3) = p.p i * Real.log 3 + p.p i * Real.log (p.p i) := by
    intro i
    rw [klTerm_uniform (hpos i)]
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt (hpos i))]
    ring
  simp only [hexp, Finset.sum_add_distrib]
  congr 1
  -- ∑ p_i * log 3 = log 3 * ∑ p_i = log 3 * 1 = log 3
  rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

/-- From Gibbs ≥ 0: -Σᵢ pᵢ ln(pᵢ) ≤ ln(3) -/
theorem neg_sum_log_le_log3 (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    -∑ i, (p.p i * Real.log (p.p i)) ≤ Real.log 3 := by
  have hgibbs := gibbs_uniform p
  simp only [uniform_val] at hgibbs
  rw [sum_klTerm_uniform p hpos] at hgibbs
  linarith

/-- Converting from ln to log₂ -/
theorem neg_sum_log2_le (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    -∑ i, (p.p i * log2 (p.p i)) ≤ log2 3 := by
  have h := neg_sum_log_le_log3 p hpos
  unfold log2
  have hlog2 : Real.log 2 > 0 := log_two_pos
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- Expand the sum explicitly for Fin 3
  simp only [Fin.sum_univ_three]
  -- Simplify the goal
  have hrw : ∀ x, p.p x * (Real.log (p.p x) / Real.log 2) =
      (p.p x * Real.log (p.p x)) / Real.log 2 := by
    intro x
    ring
  simp only [hrw]
  -- Goal: -(p0*ln(p0)/ln2 + p1*ln(p1)/ln2 + p2*ln(p2)/ln2) ≤ ln3/ln2
  have hcombine : (p.p 0 * Real.log (p.p 0)) / Real.log 2 +
      (p.p 1 * Real.log (p.p 1)) / Real.log 2 + (p.p 2 * Real.log (p.p 2)) / Real.log 2 =
      (p.p 0 * Real.log (p.p 0) + p.p 1 * Real.log (p.p 1) + p.p 2 * Real.log (p.p 2)) /
      Real.log 2 := by ring
  rw [hcombine]
  -- Goal: -((...) / ln2) ≤ ln3 / ln2
  -- Use the fact that -(x/y) = (-x)/y
  rw [show -((p.p 0 * Real.log (p.p 0) + p.p 1 * Real.log (p.p 1) +
      p.p 2 * Real.log (p.p 2)) / Real.log 2) =
      (-(p.p 0 * Real.log (p.p 0) + p.p 1 * Real.log (p.p 1) +
      p.p 2 * Real.log (p.p 2))) / Real.log 2 by ring]
  apply div_le_div_of_nonneg_right _ (le_of_lt hlog2)
  -- Goal: -(p0*ln(p0) + p1*ln(p1) + p2*ln(p2)) ≤ ln3
  simp only [Fin.sum_univ_three] at h
  linarith

/-! ## Binary Entropy Auxiliary Lemmas -/

/-- log₂(2) = 1 < log₂(3) -/
theorem log2_two_lt_log2_three : log2 2 < log2 3 := by
  unfold log2
  apply div_lt_div_of_pos_right _ log_two_pos
  exact Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)

/-- Binary entropy -p log₂ p - q log₂ q ≤ 1 for p + q = 1, p,q ≥ 0 -/
theorem binary_entropy_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    entropyTerm a + entropyTerm b ≤ log2 2 := by
  rw [log2_two]
  by_cases ha_pos : a > 0
  · by_cases hb_pos : b > 0
    · -- Both positive case: use Gibbs inequality for binary
      rw [entropyTerm_pos a ha_pos, entropyTerm_pos b hb_pos]
      unfold log2
      have hln2 : Real.log 2 > 0 := log_two_pos
      have hln2_ne : Real.log 2 ≠ 0 := ne_of_gt hln2
      -- Need: -a * (ln a / ln 2) - b * (ln b / ln 2) ≤ 1
      -- Rewrite: -(a * ln a + b * ln b) / ln 2 ≤ 1
      have hrw : -a * (Real.log a / Real.log 2) + -b * (Real.log b / Real.log 2) =
          -(a * Real.log a + b * Real.log b) / Real.log 2 := by
        field_simp
        ring
      rw [hrw, div_le_one hln2, neg_le_iff_add_nonneg]
      -- Need: a ln a + b ln b + ln 2 ≥ 0
      -- This is D((a,b)||(1/2,1/2)) = a ln(2a) + b ln(2b) ≥ 0
      -- Use kl_term_ge_diff' from Step3
      have hterm1 : klTerm a (1/2) ≥ a - 1/2 := kl_term_ge_diff' ha (by norm_num : (1/2 : ℝ) > 0)
      have hterm2 : klTerm b (1/2) ≥ b - 1/2 := kl_term_ge_diff' hb (by norm_num : (1/2 : ℝ) > 0)
      rw [klTerm_pos a (1/2) ha_pos] at hterm1
      rw [klTerm_pos b (1/2) hb_pos] at hterm2
      -- a * ln(a / (1/2)) = a * ln(2a), similarly for b
      have h1 : a * Real.log (a / (1/2)) = a * Real.log 2 + a * Real.log a := by
        rw [show a / (1/2) = 2 * a by field_simp]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ha_pos)]
        ring
      have h2 : b * Real.log (b / (1/2)) = b * Real.log 2 + b * Real.log b := by
        rw [show b / (1/2) = 2 * b by field_simp]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hb_pos)]
        ring
      rw [h1] at hterm1
      rw [h2] at hterm2
      -- hterm1: a * ln 2 + a * ln a ≥ a - 1/2
      -- hterm2: b * ln 2 + b * ln b ≥ b - 1/2
      -- Add them:
      have hsum : (a * Real.log 2 + a * Real.log a) + (b * Real.log 2 + b * Real.log b) ≥
          (a - 1/2) + (b - 1/2) := by linarith
      -- Need to show: 0 ≤ ln 2 + (a ln a + b ln b)
      -- i.e., ln 2 + a ln a + b ln b ≥ 0
      have hfinal : Real.log 2 + (a * Real.log a + b * Real.log b) ≥ 0 := by
        calc Real.log 2 + (a * Real.log a + b * Real.log b)
            = (a * Real.log 2 + a * Real.log a) + (b * Real.log 2 + b * Real.log b) -
              (a + b) * Real.log 2 + Real.log 2 := by ring
          _ = (a * Real.log 2 + a * Real.log a) + (b * Real.log 2 + b * Real.log b) -
              Real.log 2 + Real.log 2 := by rw [hab, one_mul]
          _ = (a * Real.log 2 + a * Real.log a) + (b * Real.log 2 + b * Real.log b) := by ring
          _ ≥ (a - 1/2) + (b - 1/2) := hsum
          _ = a + b - 1 := by ring
          _ = 0 := by rw [hab]; ring
      exact hfinal
    · -- b = 0 case
      push_neg at hb_pos
      have hb0 : b = 0 := le_antisymm hb_pos hb
      rw [hb0] at hab; simp at hab
      rw [hab, hb0, entropyTerm_zero, add_zero]
      rw [entropyTerm_pos 1 (by norm_num : (1:ℝ) > 0), log2_one]
      simp
  · -- a = 0 case
    push_neg at ha_pos
    have ha0 : a = 0 := le_antisymm ha_pos ha
    rw [ha0] at hab; simp at hab
    rw [ha0, hab, entropyTerm_zero, zero_add]
    rw [entropyTerm_pos 1 (by norm_num : (1:ℝ) > 0), log2_one]
    simp

/-! ## :1-H-bound - Main Entropy Bound -/

/-- Entropy bound for strictly positive distributions -/
theorem entropy_le_log2_three_pos (p : ProbDist3) (hpos : ∀ i, p.p i > 0) :
    shannonEntropy p ≤ log2 3 := by
  rw [shannonEntropy_eq_neg_sum p hpos]
  exact neg_sum_log2_le p hpos

/-- General entropy bound (allowing some pᵢ = 0) -/
theorem entropy_le_log2_three (p : ProbDist3) : shannonEntropy p ≤ log2 3 := by
  by_cases h : ∀ i, p.p i > 0
  · exact entropy_le_log2_three_pos p h
  · -- Some pᵢ = 0 case - entropy is bounded by binary entropy ≤ log₂(2) < log₂(3)
    push_neg at h
    obtain ⟨i, hi⟩ := h
    have hi0 : p.p i = 0 := le_antisymm hi (p.nonneg i)
    unfold shannonEntropy
    -- Expand the sum over Fin 3
    simp only [Fin.sum_univ_three]
    -- Case split on which index is zero
    fin_cases i
    all_goals {
      simp only at hi0
      -- The pattern p.p 0 vs p.p ⟨0, ...⟩ - use conv to rewrite
      first
      | (-- i = 0
         have h0 : p.p 0 = 0 := hi0
         rw [h0, entropyTerm_zero, zero_add]
         have hsum : p.p 1 + p.p 2 = 1 := by
           have := p.sum_eq_one
           simp only [Fin.sum_univ_three, h0, zero_add] at this
           exact this
         calc entropyTerm (p.p 1) + entropyTerm (p.p 2)
             ≤ log2 2 := binary_entropy_bound (p.p 1) (p.p 2) (p.nonneg 1) (p.nonneg 2) hsum
           _ ≤ log2 3 := le_of_lt log2_two_lt_log2_three)
      | (-- i = 1
         have h1 : p.p 1 = 0 := hi0
         rw [h1, entropyTerm_zero, add_zero]
         have hsum : p.p 0 + p.p 2 = 1 := by
           have := p.sum_eq_one
           simp only [Fin.sum_univ_three, h1] at this
           linarith
         calc entropyTerm (p.p 0) + entropyTerm (p.p 2)
             ≤ log2 2 := binary_entropy_bound (p.p 0) (p.p 2) (p.nonneg 0) (p.nonneg 2) hsum
           _ ≤ log2 3 := le_of_lt log2_two_lt_log2_three)
      | (-- i = 2
         have h2 : p.p 2 = 0 := hi0
         rw [h2, entropyTerm_zero, add_zero]
         have hsum : p.p 0 + p.p 1 = 1 := by
           have := p.sum_eq_one
           simp only [Fin.sum_univ_three, h2] at this
           linarith
         calc entropyTerm (p.p 0) + entropyTerm (p.p 1)
             ≤ log2 2 := binary_entropy_bound (p.p 0) (p.p 1) (p.nonneg 0) (p.nonneg 1) hsum
           _ ≤ log2 3 := le_of_lt log2_two_lt_log2_three)
    }

end Alethfeld.QBF.Rank1.ShannonMax
