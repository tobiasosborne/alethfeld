/-
  AlethfeldLean.QBF.Rank1.ShannonMax.Step3_GibbsInequality

  Step 3: Gibbs Inequality (Non-negativity of Relative Entropy)

  Alethfeld Verified Proof | Graph: shannon-max-002 v2
  EDN Nodes: :1-gibbs, :2-gibbs-setup through :2-gibbs-eq-final
  Status: CLEAN

  Key Result: For distributions p, q with q_i > 0:
    D(p||q) = Σᵢ pᵢ ln(pᵢ/qᵢ) ≥ 0
  with equality iff p = q.
-/
import AlethfeldLean.QBF.Rank1.ShannonMax.Step2_LogInequality

namespace Alethfeld.QBF.Rank1.ShannonMax

open scoped BigOperators
open Real

/-! ## Relative Entropy (KL Divergence) -/

/-- Relative entropy term: pᵢ ln(pᵢ/qᵢ) with convention 0 ln(0/q) = 0 -/
noncomputable def klTerm (p q : ℝ) : ℝ :=
  if p > 0 then p * Real.log (p / q) else 0

/-- KL term when p > 0 -/
theorem klTerm_pos (p q : ℝ) (hp : p > 0) : klTerm p q = p * Real.log (p / q) := by
  unfold klTerm
  simp [hp]

/-- KL term when p = 0 -/
theorem klTerm_zero (q : ℝ) : klTerm 0 q = 0 := by
  unfold klTerm
  simp

/-- Relative entropy (KL divergence) between two distributions -/
noncomputable def klDivergence (p q : ProbDist3) : ℝ :=
  ∑ i, klTerm (p.p i) (q.p i)

/-! ## Key Lemma: klTerm p q ≥ p - q -/

/-- Key step: pᵢ ln(pᵢ/qᵢ) ≥ pᵢ - qᵢ when pᵢ > 0 and qᵢ > 0 -/
theorem kl_term_ge_diff {p q : ℝ} (hp : p > 0) (hq : q > 0) :
    klTerm p q ≥ p - q := by
  rw [klTerm_pos p q hp]
  -- ln(p/q) ≥ 1 - q/p follows from log inequality
  -- Multiply by p to get: p ln(p/q) ≥ p - q
  have hqp : q / p > 0 := div_pos hq hp
  have h := neg_log_ge_one_sub hqp
  -- -ln(q/p) ≥ 1 - q/p, i.e., ln(p/q) ≥ 1 - q/p
  have heq : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  rw [heq]
  -- p * (-ln(q/p)) ≥ p - q
  -- We have -ln(q/p) ≥ 1 - q/p
  -- Multiply by p > 0: p * (-ln(q/p)) ≥ p * (1 - q/p) = p - q
  have hmul : p * (-Real.log (q / p)) ≥ p * (1 - q / p) :=
    mul_le_mul_of_nonneg_left h (le_of_lt hp)
  calc p * (-Real.log (q / p)) ≥ p * (1 - q / p) := hmul
    _ = p - q := by field_simp

/-- Combined: klTerm p q ≥ p - q for p ≥ 0, q > 0 -/
theorem kl_term_ge_diff' {p q : ℝ} (hp : p ≥ 0) (hq : q > 0) :
    klTerm p q ≥ p - q := by
  rcases hp.lt_or_eq with hpos | heq
  · exact kl_term_ge_diff hpos hq
  · rw [← heq, klTerm_zero]
    linarith [le_of_lt hq]

/-! ## :1-gibbs - Gibbs Inequality -/

/-- Gibbs Inequality: D(p||q) ≥ 0 -/
theorem gibbs_inequality (p q : ProbDist3) (hq : ∀ i, q.p i > 0) :
    klDivergence p q ≥ 0 := by
  unfold klDivergence
  calc ∑ i, klTerm (p.p i) (q.p i)
      ≥ ∑ i, (p.p i - q.p i) := by
        apply Finset.sum_le_sum
        intro i _
        exact kl_term_ge_diff' (p.nonneg i) (hq i)
    _ = (∑ i, p.p i) - (∑ i, q.p i) := by rw [Finset.sum_sub_distrib]
    _ = 1 - 1 := by rw [p.sum_eq_one, q.sum_eq_one]
    _ = 0 := by ring

/-! ## Equality Condition -/

/-- Equality in single term: klTerm p q = p - q iff p = q (when both positive) -/
theorem kl_term_eq_diff_iff {p q : ℝ} (hp : p > 0) (hq : q > 0) :
    klTerm p q = p - q ↔ p = q := by
  rw [klTerm_pos p q hp]
  constructor
  · intro h
    -- p * ln(p/q) = p - q implies p = q
    -- This uses the equality condition of the log inequality
    have hpq : p / q > 0 := div_pos hp hq
    have hqp : q / p > 0 := div_pos hq hp
    -- From p * ln(p/q) = p - q, divide by p to get ln(p/q) = 1 - q/p
    have hdiv : Real.log (p / q) = 1 - q / p := by
      have hp_ne : p ≠ 0 := ne_of_gt hp
      field_simp at h ⊢
      linarith
    -- ln(p/q) = -ln(q/p), so -ln(q/p) = 1 - q/p, i.e., ln(q/p) = q/p - 1
    have heq : Real.log (p / q) = -Real.log (q / p) := by
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
      rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
      ring
    rw [heq] at hdiv
    have hlog : Real.log (q / p) = q / p - 1 := by linarith
    -- By log_eq_sub_one_iff, q/p = 1, so q = p
    have hone := (log_eq_sub_one_iff hqp).mp hlog
    field_simp at hone
    exact hone.symm
  · intro h
    rw [h, div_self (ne_of_gt hq), Real.log_one, mul_zero]
    ring

/-- Gibbs equality condition: D(p||q) = 0 iff p = q -/
theorem gibbs_equality_iff (p q : ProbDist3) (hq : ∀ i, q.p i > 0) :
    klDivergence p q = 0 ↔ p.p = q.p := by
  constructor
  · intro h
    -- If D(p||q) = 0, then each term achieves equality in its bound
    -- Sum of non-negative terms equals 0 implies each term is 0
    have hge := gibbs_inequality p q hq
    -- The gap between klTerm and (p - q) sums to 0
    have hsum : ∑ i, (klTerm (p.p i) (q.p i) - (p.p i - q.p i)) = 0 := by
      unfold klDivergence at h
      calc ∑ i, (klTerm (p.p i) (q.p i) - (p.p i - q.p i))
          = (∑ i, klTerm (p.p i) (q.p i)) - ∑ i, (p.p i - q.p i) := by
            rw [Finset.sum_sub_distrib]
        _ = 0 - (∑ i, p.p i - ∑ i, q.p i) := by
            rw [h, Finset.sum_sub_distrib]
        _ = 0 - (1 - 1) := by rw [p.sum_eq_one, q.sum_eq_one]
        _ = 0 := by ring
    -- Each gap is ≥ 0, and sum is 0, so each gap is 0
    have hall_nonneg : ∀ j, klTerm (p.p j) (q.p j) - (p.p j - q.p j) ≥ 0 := by
      intro j
      have := kl_term_ge_diff' (p.nonneg j) (hq j)
      linarith
    -- By Finset.sum_eq_zero_iff_of_nonneg, each term is 0
    have hterms : ∀ i, klTerm (p.p i) (q.p i) = p.p i - q.p i := by
      intro i
      have hi := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hall_nonneg j) |>.mp hsum i
        (Finset.mem_univ i)
      linarith
    -- Now prove p.p = q.p using kl_term_eq_diff_iff
    funext i
    have hi := hterms i
    by_cases hp : p.p i > 0
    · exact (kl_term_eq_diff_iff hp (hq i)).mp hi
    · -- If p.p i = 0, then klTerm = 0 and hi says 0 = 0 - q.p i, so q.p i = 0
      -- But hq says q.p i > 0, contradiction unless we show p.p i = 0 = q.p i is impossible
      push_neg at hp
      have hp0 : p.p i = 0 := le_antisymm hp (p.nonneg i)
      rw [hp0, klTerm_zero] at hi
      -- hi: 0 = 0 - q.p i = -q.p i
      -- So q.p i = 0, contradiction with hq i
      have hqi : q.p i = 0 := by linarith
      linarith [hq i]
  · intro h
    -- If p.p = q.p, then D(p||q) = 0
    unfold klDivergence
    simp only [h]
    apply Finset.sum_eq_zero
    intro i _
    rw [klTerm_pos (q.p i) (q.p i) (hq i)]
    simp [div_self (ne_of_gt (hq i)), Real.log_one]

end Alethfeld.QBF.Rank1.ShannonMax
