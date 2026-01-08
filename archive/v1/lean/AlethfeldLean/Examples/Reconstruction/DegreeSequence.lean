/-
  Degree Sequence Lemma: The degree sequence is reconstructible from the deck.

  Specifically, deg_G(v) = |E(G)| - |E(G - v)| for each vertex v.
-/

import Mathlib
import AlethfeldLean.Examples.Reconstruction.Basic
import AlethfeldLean.Examples.Reconstruction.KellyLemma

namespace Alethfeld.Examples.Reconstruction

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of a vertex v in G equals |E(G)| - |E(G - v)|.
    This is because G - v removes exactly the edges incident to v. -/
theorem degree_from_edge_counts (G : SimpleGraph V) (v : V) :
    vertexDegree G v = edgeCount G - edgeCount (G -ᵥ v) := by
  classical
  -- From edgeCount_vertexDeleted_eq: edgeCount (G -ᵥ v) = edgeCount G - vertexDegree G v
  have h := edgeCount_vertexDeleted_eq G v
  -- We need: deg = e - (e - deg)
  -- Since deg ≤ e, this is just Nat.sub_sub_self
  have hdeg : vertexDegree G v ≤ edgeCount G := by
    simp only [vertexDegree, edgeCount]
    exact G.degree_le_card_edgeFinset v
  omega

/-- The degree sequence is reconstructible from the deck.
    Since |E(G)| is reconstructible by Kelly's Lemma, and |E(G - v)|
    is observable from the card, we can compute the degree sequence. -/
theorem degree_sequence_reconstructible (G H : SimpleGraph V)
    (hypo : Hypomorphic G H) (hn : 3 ≤ Fintype.card V) :
    ∀ v, vertexDegree G v = vertexDegree H v := by
  intro v
  -- Use degree_from_edge_counts for both G and H
  rw [degree_from_edge_counts G v, degree_from_edge_counts H v]
  -- By Kelly's Lemma: edgeCount G = edgeCount H
  have he : edgeCount G = edgeCount H := hypomorphic_same_edge_count G H hypo hn
  -- By hypomorphism: G - v ≅ H - v, so edgeCount (G -ᵥ v) = edgeCount (H -ᵥ v)
  have hev : edgeCount (G -ᵥ v) = edgeCount (H -ᵥ v) := by
    obtain ⟨φ⟩ := hypo v
    exact iso_preserves_edge_count (G -ᵥ v) (H -ᵥ v) φ
  rw [he, hev]

end Alethfeld.Examples.Reconstruction
