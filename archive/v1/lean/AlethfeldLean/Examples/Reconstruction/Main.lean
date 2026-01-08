/-
  Main Theorem: Reconstruction Conjecture for n in {3, 4, 5}

  For all simple graphs G and H on n vertices where 3 <= n <= 5:
  if D(G) = D(H), then G is isomorphic to H.
-/

import Mathlib
import AlethfeldLean.Examples.Reconstruction.Basic
import AlethfeldLean.Examples.Reconstruction.Case3
import AlethfeldLean.Examples.Reconstruction.Case4
import AlethfeldLean.Examples.Reconstruction.Case5

namespace Alethfeld.Examples.Reconstruction

/-- **Main Theorem**: The Reconstruction Conjecture holds for graphs on 3, 4, or 5 vertices.

    For n in {3, 4, 5}, if two graphs G and H have equal decks (are hypomorphic),
    then they are isomorphic.

    The proof proceeds by:
    1. Kelly's Lemma: edge count is reconstructible
    2. Degree Sequence Lemma: degree sequence is reconstructible
    3. Case analysis on n = 3, 4, 5 showing these invariants distinguish all graphs -/
theorem reconstruction_conjecture_small (n : ℕ) (hn : n ∈ ({3, 4, 5} : Set ℕ))
    (G H : SimpleGraph (Fin n))
    (hypo : Hypomorphic G H) : Nonempty (G ≃g H) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · -- Case n = 3
    exact reconstruction_3 G H hypo
  · -- Case n = 4
    exact reconstruction_4 G H hypo
  · -- Case n = 5
    exact reconstruction_5 G H hypo

/-- Alternative statement: reconstruction holds for 3 <= n <= 5 -/
theorem reconstruction_conjecture_small' (n : ℕ) (hn_lb : 3 ≤ n) (hn_ub : n ≤ 5)
    (G H : SimpleGraph (Fin n))
    (hypo : Hypomorphic G H) : Nonempty (G ≃g H) := by
  apply reconstruction_conjecture_small n _ G H hypo
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases n <;> simp

end Alethfeld.Examples.Reconstruction
