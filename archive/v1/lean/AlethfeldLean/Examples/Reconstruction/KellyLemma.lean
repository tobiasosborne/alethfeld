/-
  Kelly's Lemma: Edge count is reconstructible from the deck.

  For any graph G on n vertices:
  |E(G)| = (1/(n-2)) * sum_{H in D(G)} |E(H)|

  Hence if D(G) = D(H), then |E(G)| = |E(H)|.
-/

import Mathlib
import AlethfeldLean.Examples.Reconstruction.Basic

namespace Alethfeld.Examples.Reconstruction

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complement of a singleton as a Set -/
abbrev compl_singleton (v : V) : Set V := ({v} : Set V)ᶜ

/-- Equivalence between {w : V // w ≠ v} and the complement of {v} as a set -/
def vertexEquiv (v : V) : {w : V // w ≠ v} ≃ ↑(compl_singleton v) where
  toFun := fun ⟨w, hw⟩ => ⟨w, Set.mem_compl_singleton_iff.mpr hw⟩
  invFun := fun ⟨w, hw⟩ => ⟨w, Set.mem_compl_singleton_iff.mp hw⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The vertex-deleted subgraph G - v is isomorphic to the induced subgraph on {v}ᶜ -/
def graphIso (G : SimpleGraph V) (v : V) : (G -ᵥ v) ≃g G.induce (compl_singleton v) where
  toEquiv := vertexEquiv v
  map_rel_iff' := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [vertexDeletedSubgraph, Equiv.coe_fn_mk, vertexEquiv, SimpleGraph.induce_adj]

/-- The edge count of a vertex-deleted subgraph equals |E(G)| - degree(v).

    This is because removing vertex v removes exactly the edges incident to v,
    which number degree(v). -/
lemma edgeCount_vertexDeleted_eq (G : SimpleGraph V) (v : V) :
    edgeCount (G -ᵥ v) = edgeCount G - vertexDegree G v := by
  classical
  simp only [edgeCount, vertexDegree]
  have h1 := (graphIso G v).card_edgeFinset_eq
  rw [h1]
  rw [G.card_edgeFinset_induce_compl_singleton v]
  exact G.card_edgeFinset_deleteIncidenceSet v

omit [DecidableEq V] in
/-- Isomorphic graphs have the same number of edges -/
theorem iso_preserves_edge_count {W : Type*} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (φ : G ≃g H) :
    edgeCount G = edgeCount H := by
  classical
  simp only [edgeCount]
  exact φ.card_edgeFinset_eq

/-- Helper: sum of (a - f i) over a finite type when f i ≤ a for all i -/
lemma sum_const_sub {α : Type*} [Fintype α] (a : ℕ) (f : α → ℕ) (h : ∀ x, f x ≤ a) :
    ∑ x : α, (a - f x) = Fintype.card α * a - ∑ x : α, f x := by
  have hsum_le : ∑ x : α, f x ≤ Fintype.card α * a := by
    calc ∑ x : α, f x ≤ ∑ _x : α, a := Finset.sum_le_sum (fun x _ => h x)
      _ = Fintype.card α * a := by simp [Finset.sum_const, Finset.card_univ]
  apply Nat.eq_sub_of_add_eq
  rw [add_comm, ← Finset.sum_add_distrib]
  conv_lhs =>
    arg 2
    ext x
    rw [add_comm, Nat.sub_add_cancel (h x)]
  simp [Finset.sum_const, Finset.card_univ]

/-- **Kelly's Lemma**: The sum of edge counts over all cards equals (n-2) * |E(G)|.
    Therefore |E(G)| = (1/(n-2)) * sum_{v in V} |E(G - v)|.

    Proof: Using ∑ v, degree(v) = 2 * |E(G)| and |E(G-v)| = |E(G)| - degree(v). -/
theorem kellys_lemma (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V) :
    (Fintype.card V - 2) * edgeCount G = ∑ v : V, edgeCount (G -ᵥ v) := by
  classical
  -- Use the relation: |E(G - v)| = |E(G)| - degree(v)
  have h1 : ∀ v, edgeCount (G -ᵥ v) = edgeCount G - vertexDegree G v := edgeCount_vertexDeleted_eq G
  simp_rw [h1]
  -- Use: ∑ v, degree(v) = 2 * |E(G)|
  have h2 : ∑ v : V, vertexDegree G v = 2 * edgeCount G := by
    simp only [vertexDegree, edgeCount]
    exact G.sum_degrees_eq_twice_card_edges
  -- Each degree is at most the total edge count
  have hdeg : ∀ v : V, vertexDegree G v ≤ edgeCount G := by
    intro v
    simp only [vertexDegree, edgeCount]
    exact G.degree_le_card_edgeFinset v
  -- ∑ v, (|E(G)| - degree(v)) = n * |E(G)| - ∑ v, degree(v) = n * |E(G)| - 2 * |E(G)|
  rw [sum_const_sub (edgeCount G) (vertexDegree G) hdeg]
  rw [h2]
  -- (n - 2) * e = n * e - 2 * e
  rw [Nat.sub_mul (Fintype.card V) 2 (edgeCount G)]

/-- Corollary: Hypomorphic graphs have the same number of edges -/
theorem hypomorphic_same_edge_count (G H : SimpleGraph V)
    (hypo : Hypomorphic G H) (hn : 3 ≤ Fintype.card V) :
    edgeCount G = edgeCount H := by
  classical
  -- By Kelly's Lemma: (n-2) * |E(G)| = sum_v |E(G-v)|
  have hG := kellys_lemma G hn
  have hH := kellys_lemma H hn
  -- Since G - v ≅ H - v for all v, their edge counts are equal
  have heq : ∑ v : V, edgeCount (G -ᵥ v) = ∑ v : V, edgeCount (H -ᵥ v) := by
    apply Finset.sum_congr rfl
    intro v _
    obtain ⟨φ⟩ := hypo v
    exact iso_preserves_edge_count (G -ᵥ v) (H -ᵥ v) φ
  -- So (n-2) * |E(G)| = (n-2) * |E(H)|
  have h : (Fintype.card V - 2) * edgeCount G = (Fintype.card V - 2) * edgeCount H := by
    rw [hG, heq, ← hH]
  -- Since n ≥ 3, we have n - 2 > 0, so |E(G)| = |E(H)|
  have hpos : 0 < Fintype.card V - 2 := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos h

end Alethfeld.Examples.Reconstruction
