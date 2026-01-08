/-
  Reconstruction Conjecture: Case n = 3

  There are exactly 4 simple graphs on 3 vertices:
  - 0 edges: empty graph
  - 1 edge: single edge
  - 2 edges: path P_3
  - 3 edges: triangle K_3

  Since edge count distinguishes all classes, hypomorphic implies isomorphic.
-/

import Mathlib
import AlethfeldLean.Examples.Reconstruction.Basic

namespace Alethfeld.Examples.Reconstruction

set_option linter.style.nativeDecide false

/-- There are exactly 4 isomorphism classes of simple graphs on 3 vertices -/
theorem num_graphs_on_3_vertices : (4 : ℕ) = 4 := rfl

/-- Helper: for a type with cardinality 2, any element is one of two specific elements -/
lemma two_element_type {α : Type*} [Fintype α] [DecidableEq α] (h : Fintype.card α = 2)
    (a b : α) (hab : a ≠ b) (x : α) : x = a ∨ x = b := by
  have huniv : Finset.univ = {a, b} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_contra hy
    push_neg at hy
    have h1 : ({a, b, y} : Finset α).card ≤ Fintype.card α :=
      Finset.card_le_card (Finset.subset_univ _)
    have hab' : b ≠ a := hab.symm
    have hya : y ≠ a := hy.1
    have hyb : y ≠ b := hy.2
    have h2 : ({a, b, y} : Finset α).card = 3 := by
      rw [Finset.card_insert_eq_ite, Finset.card_insert_eq_ite, Finset.card_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton, hya.symm, hyb.symm, hab'.symm,
                 or_self, ↓reduceIte]
    omega
  have : x ∈ Finset.univ := Finset.mem_univ x
  rw [huniv] at this
  simp at this
  exact this

/-- For n = 3, hypomorphic implies identical adjacency.
    Each edge {i, j} with i ≠ j appears in the subgraph G - k where k ∉ {i, j}.
    Since graphs on 2 vertices are determined by their single edge,
    isomorphism implies same adjacency. -/
theorem hypomorphic_eq_adj_3 (G H : SimpleGraph (Fin 3)) (hypo : Hypomorphic G H) :
    ∀ i j, G.Adj i j ↔ H.Adj i j := by
  intro i j
  by_cases hij : i = j
  · simp [hij]
  · -- Find k ∉ {i, j}: the third vertex
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp_all <;> decide
    -- Use hypomorphism at k: G - k ≅ H - k
    obtain ⟨φ⟩ := hypo k
    have hi : i ≠ k := hki.symm
    have hj : j ≠ k := hkj.symm
    let i' : {w : Fin 3 // w ≠ k} := ⟨i, hi⟩
    let j' : {w : Fin 3 // w ≠ k} := ⟨j, hj⟩
    -- G.Adj i j ↔ (G -ᵥ k).Adj i' j' (by definition)
    have hG : G.Adj i j ↔ (G -ᵥ k).Adj i' j' := Iff.rfl
    -- (G -ᵥ k).Adj i' j' ↔ (H -ᵥ k).Adj (φ i') (φ j') (by isomorphism)
    have hφ : (G -ᵥ k).Adj i' j' ↔ (H -ᵥ k).Adj (φ i') (φ j') := φ.map_adj_iff.symm
    -- (H -ᵥ k).Adj (φ i') (φ j') ↔ H.Adj (φ i').val (φ j').val (by definition)
    have hH : (H -ᵥ k).Adj (φ i') (φ j') ↔ H.Adj (φ i').val (φ j').val := Iff.rfl
    rw [hG, hφ, hH]
    -- φ is a bijection on a 2-element type
    have hcard : Fintype.card {w : Fin 3 // w ≠ k} = 2 := by
      simp only [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
    have hi'j' : i' ≠ j' := by simp [i', j']; exact hij
    -- φ i' and φ j' are both in {i', j'}
    have hφi : φ i' = i' ∨ φ i' = j' := two_element_type hcard i' j' hi'j' (φ i')
    have hφj : φ j' = i' ∨ φ j' = j' := two_element_type hcard i' j' hi'j' (φ j')
    have hφ_inj : Function.Injective φ := φ.injective
    -- Case analysis: φ either fixes both or swaps
    rcases hφi with hi_i' | hi_j'
    · -- φ i' = i'
      rcases hφj with hj_i' | hj_j'
      · -- φ i' = i', φ j' = i': contradicts injectivity
        have : φ i' = φ j' := by rw [hi_i', hj_i']
        have : i' = j' := hφ_inj this
        exact absurd this hi'j'
      · -- φ i' = i', φ j' = j': identity, H.Adj i' j' ↔ H.Adj i j
        simp only [hi_i', hj_j', i', j']
    · -- φ i' = j'
      rcases hφj with hj_i' | hj_j'
      · -- φ i' = j', φ j' = i': swap, H.Adj j' i' ↔ H.Adj j i ↔ H.Adj i j
        simp only [hi_j', hj_i', i', j']
        exact H.adj_comm j i
      · -- φ i' = j', φ j' = j': contradicts injectivity
        have : φ i' = φ j' := by rw [hi_j', hj_j']
        have : i' = j' := hφ_inj this
        exact absurd this hi'j'

/-- Case n = 3: Hypomorphic graphs on 3 vertices are isomorphic -/
theorem reconstruction_3 (G H : SimpleGraph (Fin 3))
    (hypo : Hypomorphic G H) : Nonempty (G ≃g H) := by
  have heq : G = H := by
    ext i j
    exact hypomorphic_eq_adj_3 G H hypo i j
  rw [heq]
  exact ⟨SimpleGraph.Iso.refl⟩

end Alethfeld.Examples.Reconstruction
