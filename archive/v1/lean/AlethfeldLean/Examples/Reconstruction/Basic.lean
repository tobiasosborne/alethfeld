/-
  Basic definitions for the Reconstruction Conjecture proof.

  Defines: vertexDeletedSubgraph, deck, Hypomorphic
-/

import Mathlib

namespace Alethfeld.Examples.Reconstruction

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex-deleted subgraph G - v: the induced subgraph on V \ {v} -/
def vertexDeletedSubgraph (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w ≠ v} where
  Adj := fun ⟨a, _⟩ ⟨b, _⟩ => G.Adj a b
  symm := fun _ _ h => G.symm h
  loopless := fun ⟨a, _⟩ => G.loopless a

/-- Notation: G - v for the vertex-deleted subgraph -/
scoped notation:max G " -ᵥ " v => vertexDeletedSubgraph G v

/-- The deck of a graph G is the multiset of vertex-deleted subgraphs.
    Note: This is the "labeled" deck; the "unlabeled" deck would quotient
    by graph isomorphism, which we handle via the hypomorphism definition. -/
def deck (G : SimpleGraph V) : Multiset (Σ v : V, SimpleGraph {w : V // w ≠ v}) :=
  Finset.univ.val.map (fun v => ⟨v, G -ᵥ v⟩)

/-- Two graphs are hypomorphic if their vertex-deleted subgraphs are
    pairwise isomorphic (for corresponding vertices). -/
def Hypomorphic (G H : SimpleGraph V) : Prop :=
  ∀ v : V, Nonempty ((G -ᵥ v) ≃g (H -ᵥ v))

/-- The number of edges in a simple graph -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- The degree of a vertex -/
noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact G.degree v

end Alethfeld.Examples.Reconstruction
