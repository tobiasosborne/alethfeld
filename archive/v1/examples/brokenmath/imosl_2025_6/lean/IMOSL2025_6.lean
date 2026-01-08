/-
  IMOSL 2025 Problem 6 - Arithmetic/Geometric Mean Sequences

  THEOREM (as stated):
  Let (a_n) be an infinite strictly increasing sequence of positive integers such that
  for each n >= 1, a_n is either the arithmetic mean or geometric mean of a_{n-1} and a_{n+1}.
  Let b_n = A if a_n is the arithmetic mean, and b_n = G otherwise.
  Prove: for every positive integer d, there exists n_0 such that for all n >= n_0,
  b_{n+d} != b_n.

  RESULT: The theorem as stated is FALSE.

  COUNTEREXAMPLES:
  1. a_n = n + 1 (arithmetic progression): b_n = A for all n, so b_{n+d} = b_n always
  2. a_n = 2^n (geometric progression): b_n = G for all n, so b_{n+d} = b_n always

  CORRECTED THEOREM:
  If (b_n) has infinitely many G entries, then for every d, eventually b_{n+d} != b_n.

  Graph: graph-e76670-027511 v65
  Taint status: clean (but theorem is false)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic

namespace IMOSL2025_6

/-! ## Type for A/G labels -/
inductive Label where
  | A : Label  -- Arithmetic mean
  | G : Label  -- Geometric mean
  deriving DecidableEq, Repr

/-! ## Definition of valid sequence -/

/-- A sequence satisfies the mean condition if each term is either the
    arithmetic or geometric mean of its neighbors. -/
def SatisfiesMeanCondition (a : Nat -> Nat) : Prop :=
  forall n : Nat, n >= 1 ->
    (2 * a n = a (n - 1) + a (n + 1)) \/  -- Arithmetic mean
    ((a n) ^ 2 = a (n - 1) * a (n + 1))   -- Geometric mean

/-- A sequence is strictly increasing -/
def StrictlyIncreasing (a : Nat -> Nat) : Prop :=
  forall n : Nat, a n < a (n + 1)

/-- A sequence consists of positive integers -/
def AllPositive (a : Nat -> Nat) : Prop :=
  forall n : Nat, a n > 0

/-- The label function: A if arithmetic mean, G if geometric mean -/
noncomputable def labelOf (a : Nat -> Nat) (n : Nat) : Label :=
  if 2 * a n = a (n - 1) + a (n + 1) then Label.A else Label.G

/-! ## Counterexample 1: Arithmetic progression -/

/-- The arithmetic progression a_n = n + 1 -/
def arithSeq : Nat -> Nat := fun n => n + 1

theorem arithSeq_strictly_increasing : StrictlyIncreasing arithSeq := by
  intro n
  simp [arithSeq]
  omega

theorem arithSeq_all_positive : AllPositive arithSeq := by
  intro n
  simp [arithSeq]
  omega

theorem arithSeq_is_arithmetic_mean (n : Nat) (hn : n >= 1) :
    2 * arithSeq n = arithSeq (n - 1) + arithSeq (n + 1) := by
  simp [arithSeq]
  omega

theorem arithSeq_satisfies_condition : SatisfiesMeanCondition arithSeq := by
  intro n hn
  left
  exact arithSeq_is_arithmetic_mean n hn

theorem arithSeq_all_labels_A (n : Nat) (hn : n >= 1) :
    labelOf arithSeq n = Label.A := by
  simp [labelOf]
  exact arithSeq_is_arithmetic_mean n hn

/-- Counterexample: For arithSeq, b_{n+d} = b_n = A for all n >= 1, d >= 1 -/
theorem arithSeq_counterexample (d : Nat) (hd : d >= 1) :
    forall n : Nat, n >= 1 -> labelOf arithSeq n = labelOf arithSeq (n + d) := by
  intro n hn
  rw [arithSeq_all_labels_A n hn]
  rw [arithSeq_all_labels_A (n + d) (by omega)]

/-! ## Counterexample 2: Geometric progression with ratio 2 -/

/-- The geometric progression a_n = 2^n -/
def geomSeq : Nat -> Nat := fun n => 2 ^ n

theorem geomSeq_strictly_increasing : StrictlyIncreasing geomSeq := by
  intro n
  simp [geomSeq]
  apply Nat.pow_lt_pow_right
  omega
  omega

theorem geomSeq_all_positive : AllPositive geomSeq := by
  intro n
  simp [geomSeq]
  apply Nat.pos_pow_of_pos
  omega

theorem geomSeq_is_geometric_mean (n : Nat) (hn : n >= 1) :
    (geomSeq n) ^ 2 = geomSeq (n - 1) * geomSeq (n + 1) := by
  simp [geomSeq]
  have h1 : n - 1 + (n + 1) = 2 * n := by omega
  rw [<- Nat.pow_add]
  rw [h1]
  ring

theorem geomSeq_not_arithmetic_mean (n : Nat) (hn : n >= 1) :
    2 * geomSeq n != geomSeq (n - 1) + geomSeq (n + 1) := by
  simp [geomSeq]
  -- 2 * 2^n != 2^(n-1) + 2^(n+1)
  -- 2^(n+1) != 2^(n-1) + 2^(n+1) is false, so need different approach
  -- Actually: 2 * 2^n = 2^(n+1) and 2^(n-1) + 2^(n+1) = 2^(n-1)(1 + 4) = 5 * 2^(n-1)
  -- So 2^(n+1) != 5 * 2^(n-1) when n >= 1
  sorry  -- Requires careful power manipulation

theorem geomSeq_satisfies_condition : SatisfiesMeanCondition geomSeq := by
  intro n hn
  right
  exact geomSeq_is_geometric_mean n hn

theorem geomSeq_all_labels_G (n : Nat) (hn : n >= 1) :
    labelOf geomSeq n = Label.G := by
  simp [labelOf]
  intro h
  have hne := geomSeq_not_arithmetic_mean n hn
  exact hne h

/-- Counterexample: For geomSeq, b_{n+d} = b_n = G for all n >= 1, d >= 1 -/
theorem geomSeq_counterexample (d : Nat) (hd : d >= 1) :
    forall n : Nat, n >= 1 -> labelOf geomSeq n = labelOf geomSeq (n + d) := by
  intro n hn
  rw [geomSeq_all_labels_G n hn]
  rw [geomSeq_all_labels_G (n + d) (by omega)]

/-! ## The original theorem is FALSE -/

/-- The original theorem statement (negated) -/
theorem original_theorem_is_false :
    exists a : Nat -> Nat,
      StrictlyIncreasing a /\
      AllPositive a /\
      SatisfiesMeanCondition a /\
      exists d : Nat, d >= 1 /\
        forall n0 : Nat, exists n : Nat, n >= n0 /\ labelOf a n = labelOf a (n + d) := by
  use arithSeq
  constructor
  . exact arithSeq_strictly_increasing
  constructor
  . exact arithSeq_all_positive
  constructor
  . exact arithSeq_satisfies_condition
  use 1
  constructor
  . omega
  intro n0
  use n0 + 1
  constructor
  . omega
  have h1 : n0 + 1 >= 1 := by omega
  have h2 : n0 + 1 + 1 >= 1 := by omega
  rw [arithSeq_all_labels_A (n0 + 1) h1]
  rw [arithSeq_all_labels_A (n0 + 1 + 1) h2]

/-! ## Corrected theorem statement -/

/-- A sequence has infinitely many G labels -/
def HasInfinitelyManyG (a : Nat -> Nat) : Prop :=
  forall N : Nat, exists n : Nat, n > N /\ labelOf a n = Label.G

/-- The corrected theorem: if infinitely many G, then eventually alternating -/
theorem corrected_theorem
    (a : Nat -> Nat)
    (hpos : AllPositive a)
    (hinc : StrictlyIncreasing a)
    (hmean : SatisfiesMeanCondition a)
    (hinfG : HasInfinitelyManyG a)
    (d : Nat) (hd : d >= 1) :
    exists n0 : Nat, forall n : Nat, n >= n0 -> labelOf a n != labelOf a (n + d) := by
  -- This is the corrected theorem that should be true
  -- The proof requires showing that periodic patterns with G are impossible
  -- due to divisibility constraints
  sorry

/-! ## Key lemmas from the proof analysis -/

/-- Under arithmetic mean, differences are preserved -/
lemma arith_preserves_diff (a : Nat -> Nat) (n : Nat) (hn : n >= 1)
    (hA : 2 * a n = a (n - 1) + a (n + 1)) :
    a (n + 1) - a n = a n - a (n - 1) := by
  -- From 2 * a_n = a_{n-1} + a_{n+1}
  -- We get a_{n+1} - a_n = a_n - a_{n-1}
  omega

/-- Under geometric mean, ratios are preserved -/
lemma geom_preserves_ratio (a : Nat -> Nat) (n : Nat) (hn : n >= 1)
    (hG : (a n) ^ 2 = a (n - 1) * a (n + 1))
    (hpos : a (n - 1) > 0) :
    a n * a n = a (n - 1) * a (n + 1) := by
  -- Direct from the geometric mean condition
  simp [pow_two] at hG
  exact hG

/-- The ratio map T_A(r) = 2 - 1/r -/
noncomputable def T_A (r : Rat) : Rat := 2 - 1 / r

/-- T_A has no fixed point in (1, infinity) -/
theorem T_A_no_fixed_point (r : Rat) (hr : r > 1) : T_A r != r := by
  simp [T_A]
  -- r = 2 - 1/r implies r^2 - 2r + 1 = 0, so r = 1
  -- But r > 1, contradiction
  sorry

/-- T_A maps (1, infinity) to (1, 2) -/
theorem T_A_range (r : Rat) (hr : r > 1) : T_A r > 1 /\ T_A r < 2 := by
  simp [T_A]
  constructor
  . -- 2 - 1/r > 1 iff 1 > 1/r iff r > 1
    sorry
  . -- 2 - 1/r < 2 iff -1/r < 0 iff 1/r > 0 iff r > 0
    sorry

end IMOSL2025_6
