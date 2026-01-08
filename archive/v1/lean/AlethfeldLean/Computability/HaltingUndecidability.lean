/-
  Alethfeld Proof: Undecidability of the Halting Problem
  Graph: graph-837d62-79a574 v37
  Taint status: clean

  **Theorem**: For any total program that purports to decide halting,
  there exists a "spoiler" program such that the decider is wrong
  about whether the spoiler halts on itself.

  This is the classic diagonalization argument due to Turing (1936).
-/

import Mathlib.Tactic

namespace Alethfeld.Computability

/-!
## Abstract Computation Model

We axiomatize the essential structure needed for the undecidability proof:
- A type of programs
- A halting predicate
- A total halting "decider" structure
- The diagonal construction (if_run_else_halt)
-/

/-- A TotalProgram is a program that always terminates and comes with
    a witness function providing step bounds for all inputs. -/
structure TotalProgram (Program : Type) (halts : Program → Program → Prop) where
  prog : Program
  htotal : Program → ℕ
  terminates : ∀ input, halts prog input

/-- Evaluate a total program (uses the witness to get the step bound) -/
def eval_total {Program : Type} {halts : Program → Program → Prop}
    (eval : Program → Program → ℕ → Bool)
    (candidate : TotalProgram Program halts) (input : Program) : Bool :=
  eval candidate.prog input (candidate.htotal input)

/-!
## Main Theorem

The undecidability theorem: any purported total halting decider must be wrong
on at least one input (namely, the diagonalized spoiler applied to itself).
-/

/-- **Main Theorem**: For any total halting decider, there exists a spoiler program
    such that the decider is wrong about whether spoiler halts on itself.

    Parameters:
    - `Program`: type of programs
    - `halts p x`: predicate for whether program p halts on input x
    - `eval p x n`: evaluates program p on input x for n steps, returns true if halts
    - `if_run_else_halt dec`: diagonal construction - runs forever if dec predicts halt,
       halts if dec predicts non-halt
    - `ireh_runs_of_true`: semantic axiom - if eval returns true, spoiler doesn't halt
    - `ireh_halts_of_false`: semantic axiom - if eval returns false, spoiler halts -/
theorem halting_undecidability
    {Program : Type}
    {halts : Program → Program → Prop}
    (eval : Program → Program → ℕ → Bool)
    (if_run_else_halt : Program → Program)
    (ireh_runs_of_true : ∀ (dec input : Program) (h : ℕ),
      eval dec input h = true → ¬halts (if_run_else_halt dec) input)
    (ireh_halts_of_false : ∀ (dec input : Program) (h : ℕ),
      eval dec input h = false → halts (if_run_else_halt dec) input)
    (candidate : TotalProgram Program halts) :
    ∃ spoiler : Program,
      (eval_total eval candidate spoiler = true ∧ ¬halts spoiler spoiler) ∨
      (eval_total eval candidate spoiler = false ∧ halts spoiler spoiler) := by
  -- Step 1: Define the spoiler via diagonal construction
  let spoiler := if_run_else_halt candidate.prog
  refine ⟨spoiler, ?_⟩
  -- Step 2: Case split on what the candidate predicts (Bool has two cases: false, true)
  cases h : eval_total eval candidate spoiler with
  | false =>
    -- Case: candidate predicts "doesn't halt" (returns false)
    right
    exact ⟨rfl, ireh_halts_of_false candidate.prog spoiler (candidate.htotal spoiler) h⟩
  | true =>
    -- Case: candidate predicts "halts" (returns true)
    left
    exact ⟨rfl, ireh_runs_of_true candidate.prog spoiler (candidate.htotal spoiler) h⟩

/-- Corollary: No total program can correctly decide halting for all inputs.

    A correct decider would have:
    - eval_total candidate input = true  ↔ halts input input
    - eval_total candidate input = false ↔ ¬halts input input

    This theorem shows that for any total candidate, there exists an input
    (the spoiler) on which the candidate is wrong. -/
theorem no_total_halting_decider
    {Program : Type}
    {halts : Program → Program → Prop}
    (eval : Program → Program → ℕ → Bool)
    (if_run_else_halt : Program → Program)
    (ireh_runs_of_true : ∀ (dec input : Program) (h : ℕ),
      eval dec input h = true → ¬halts (if_run_else_halt dec) input)
    (ireh_halts_of_false : ∀ (dec input : Program) (h : ℕ),
      eval dec input h = false → halts (if_run_else_halt dec) input)
    (candidate : TotalProgram Program halts) :
    ∃ input : Program,
      ¬((eval_total eval candidate input = true ↔ halts input input) ∧
        (eval_total eval candidate input = false ↔ ¬halts input input)) := by
  obtain ⟨spoiler, h⟩ := halting_undecidability eval if_run_else_halt
                          ireh_runs_of_true ireh_halts_of_false candidate
  refine ⟨spoiler, ?_⟩
  intro ⟨h_true_iff, h_false_iff⟩
  rcases h with ⟨h_eval_true, h_not_halts⟩ | ⟨h_eval_false, h_halts⟩
  · -- Case: eval = true but ¬halts
    exact h_not_halts (h_true_iff.mp h_eval_true)
  · -- Case: eval = false but halts
    exact h_false_iff.mp h_eval_false h_halts

end Alethfeld.Computability
