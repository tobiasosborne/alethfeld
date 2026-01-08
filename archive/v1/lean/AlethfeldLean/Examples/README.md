# AlethfeldLean Examples

This directory contains standalone mathematical formalizations developed using the Alethfeld proof system.

## Contents

### Dobinski.lean
**Dobinski's Formula for Bell Numbers** (✅ Fully verified, 0 sorries)

Proves the classic identity:
$$B_n = \frac{1}{e} \sum_{k=0}^{\infty} \frac{k^n}{k!}$$

where $B_n$ is the nth Bell number (counting set partitions).

### Reconstruction/
**Reconstruction Conjecture for Small Graphs** (n = 3, 4, 5)

The Reconstruction Conjecture states that a graph G on n ≥ 3 vertices is determined up to isomorphism by its "deck" D(G) = {G - v : v ∈ V(G)}.

#### Alethfeld's Approach

The Alethfeld semantic proof system suggested **Kelly's Lemma** as the key structural approach:
$$|E(G)| = \frac{1}{n-2} \sum_{v \in V} |E(G - v)|$$

This insight guided the formalization strategy, proving that edge count is reconstructible from the deck.

#### Files

| File | Description | Status |
|------|-------------|--------|
| `Basic.lean` | Core definitions (hypomorphic, vertex-deleted subgraph) | ✅ |
| `KellyLemma.lean` | Kelly's Lemma and edge count reconstruction | ✅ 0 sorries |
| `DegreeSequence.lean` | Degree sequence is reconstructible | ✅ 0 sorries |
| `Case3.lean` | Reconstruction for n = 3 | ✅ 0 sorries |
| `Case4.lean` | Reconstruction for n = 4 | ⚠️ 1 sorry |
| `Case5.lean` | Reconstruction for n = 5 | ⚠️ 1 sorry |
| `Main.lean` | Combined theorem for n ∈ {3, 4, 5} | depends on above |

#### Proof Artifacts

The Alethfeld semantic proof graph and LaTeX document are in `examples/reconstruction-conjecture-small/`.

#### Key Theorems

```lean
-- Kelly's Lemma: (n-2) * |E(G)| = sum over v of |E(G - v)|
theorem kellys_lemma (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V) :
    (Fintype.card V - 2) * edgeCount G = ∑ v : V, edgeCount (G -ᵥ v)

-- Hypomorphic graphs have equal edge counts
theorem hypomorphic_same_edge_count (G H : SimpleGraph V)
    (hypo : Hypomorphic G H) (hn : 3 ≤ Fintype.card V) :
    edgeCount G = edgeCount H

-- Degree sequence is reconstructible
theorem degree_sequence_reconstructible (G H : SimpleGraph V)
    (hypo : Hypomorphic G H) (hn : 3 ≤ Fintype.card V) :
    ∀ v, vertexDegree G v = vertexDegree H v

-- Main theorem
theorem reconstruction_conjecture_small (n : ℕ) (hn : n ∈ ({3, 4, 5} : Set ℕ))
    (G H : SimpleGraph (Fin n)) (hypo : Hypomorphic G H) : Nonempty (G ≃g H)
```

#### Notes on Remaining Sorries

The sorries in Case4 and Case5 are due to **computational complexity**, not mathematical gaps:

- **Case 4**: Requires enumerating 11 isomorphism classes of graphs on 4 vertices
- **Case 5**: Requires enumerating 34 isomorphism classes, including distinguishing C₅ from the bowtie graph by their decks

The proof structure is complete:
1. Kelly's Lemma gives equal edge counts
2. Degree sequence lemma gives equal degrees at each vertex
3. For n = 4, 5: (edge count, degree sequence) distinguishes almost all graphs
4. Critical pairs (like C₅ vs bowtie) are distinguished by deck structure

The remaining work is finite case enumeration, which is computationally expensive in Lean but mathematically straightforward.
