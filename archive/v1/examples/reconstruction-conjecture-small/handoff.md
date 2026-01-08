# Handoff: Reconstruction Conjecture for Small Graphs

**Date**: 2026-01-05
**Graph ID**: `graph-ea348c-844188`
**Status**: In Progress - Modular refactoring partially complete

## Current State

The Lean formalization has been refactored from a single 286-line file into a modular structure. The build is currently failing due to minor issues that need fixing.

### File Structure

```
lean/AlethfeldLean/GraphTheory/
├── ReconstructionSmall.lean          # Re-exports from Reconstruction/
└── Reconstruction/
    ├── Basic.lean         ✓ BUILDS   # Core definitions (~45 lines)
    ├── KellyLemma.lean    ✗ ERRORS   # Kelly's Lemma (~50 lines)
    ├── DegreeSequence.lean           # Degree sequence (~45 lines)
    ├── Case3.lean         ✗ ERRORS   # n=3 case (~85 lines)
    ├── Case4.lean                    # n=4 case (~45 lines)
    ├── Case5.lean                    # n=5 case (~55 lines)
    └── Main.lean                     # Main theorem (~45 lines)
```

### Sorries to Fill (7 total)

| File | Theorem | Lines | Difficulty | Notes |
|------|---------|-------|------------|-------|
| KellyLemma.lean | `kellys_lemma` | ~10 | Hard | Double counting argument |
| KellyLemma.lean | `hypomorphic_same_edge_count` | ~5 | Medium | Uses Kelly's Lemma |
| DegreeSequence.lean | `degree_from_edge_counts` | ~5 | Medium | Edge set bijection |
| DegreeSequence.lean | `degree_sequence_reconstructible` | ~5 | Easy | Combines above |
| Case3.lean | `hypomorphic_eq_adj_3` | ~20 | Medium | Almost done, 1 sorry left |
| Case4.lean | `reconstruction_4` | ~5 | Hard | Finite case analysis |
| Case5.lean | `reconstruction_5` | ~5 | Hard | Finite case analysis |

## Build Errors to Fix

### 1. KellyLemma.lean - Line 38
```
Invalid field `card_edgeFinset_eq_of_iso`
```
**Fix**: Find correct mathlib lemma name. Try searching:
```bash
bash ~/.claude/plugins/cache/lean4-skills/lean4-theorem-proving/3.3.1/scripts/search_mathlib.sh "Iso.*card" name
```
Or just use sorry and move on.

### 2. Case3.lean - Line 29
```
Type mismatch: map_adj_iff direction wrong
```
**Fix**: Change `φ.map_adj_iff` to `φ.map_adj_iff.symm` or use the correct direction.

### 3. Case3.lean - Line 43
```
Application type mismatch with rfl
```
**Fix**: The `fin_cases` tactic output needs adjustment. The pattern should be:
```lean
fin_cases i <;> fin_cases j <;> simp_all <;> try exact ⟨_, by decide, by decide⟩
```

## Quick Fix Commands

To get building again quickly, you can temporarily sorry out the broken parts:

```bash
cd /home/tobias/Projects/alethfeld/lean

# Build incrementally to see each error
lake build AlethfeldLean.GraphTheory.Reconstruction.Basic
lake build AlethfeldLean.GraphTheory.Reconstruction.KellyLemma
lake build AlethfeldLean.GraphTheory.Reconstruction.Case3
lake build AlethfeldLean.GraphTheory.Reconstruction.Main
```

## Proof Strategy Overview

### Kelly's Lemma (Hardest)
**Statement**: `(n-2) * |E(G)| = Σ_v |E(G - v)|`

**Proof idea**: Each edge {u,v} appears in G-w for all w ∉ {u,v}, i.e., in exactly (n-2) cards.

**Mathlib lemmas to look for**:
- `sum_degrees_eq_twice_card_edges`
- `card_edgeFinset_deleteIncidenceSet`
- Double counting / Finset.sum manipulation

### Finite Cases (n=3,4,5)
For small n, the approach is:
1. **n=3**: Show hypomorphic ⟹ G = H directly (each edge determined by one card)
2. **n=4**: Use edge count + degree sequence (11 iso classes all distinguished)
3. **n=5**: Same plus deck analysis for C₅ vs bowtie critical pair

Consider using `native_decide` or `decide` for finite verification after making types decidable.

## Key Definitions (in Basic.lean)

```lean
-- Vertex-deleted subgraph
def vertexDeletedSubgraph (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w ≠ v}

-- Notation
scoped notation:max G " -ᵥ " v => vertexDeletedSubgraph G v

-- Hypomorphic: all vertex-deleted subgraphs are isomorphic
def Hypomorphic (G H : SimpleGraph V) : Prop :=
  ∀ v : V, Nonempty ((G -ᵥ v) ≃g (H -ᵥ v))
```

## Useful Mathlib Lemmas Found

```lean
-- In Mathlib.Combinatorics.SimpleGraph.DegreeSum
sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset

-- In Mathlib.Combinatorics.SimpleGraph.DeleteEdges
card_edgeFinset_deleteIncidenceSet : #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x
card_edgeFinset_induce_compl_singleton : #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset
```

## Subagent Strategy

The modular structure is designed for parallel subagent work:

1. **Agent 1**: Fix build errors in KellyLemma.lean and Case3.lean
2. **Agent 2**: Fill `kellys_lemma` sorry (hardest)
3. **Agent 3**: Fill `degree_from_edge_counts` sorry
4. **Agent 4**: Fill `reconstruction_4` sorry (n=4 case)
5. **Agent 5**: Fill `reconstruction_5` sorry (n=5 case)

Use `/fix-sorries` skill or `lean4-subagents:lean4-sorry-filler` for each file independently.

## Next Steps (Priority Order)

1. **Fix build errors** - Get all files compiling with their sorries
2. **Fill Case3 sorry** - Almost done, just needs permutation argument
3. **Fill degree lemmas** - Medium difficulty, uses mathlib
4. **Fill Kelly's Lemma** - Hardest, may need external help
5. **Fill Cases 4 & 5** - Consider decidability approach

## Files Modified This Session

- Created: `lean/AlethfeldLean/GraphTheory/Reconstruction/` directory with 7 files
- Modified: `lean/AlethfeldLean/GraphTheory/ReconstructionSmall.lean` (now re-exports)

## Git Status

```bash
# Uncommitted changes in lean/AlethfeldLean/GraphTheory/
# New files not yet staged
git status
git add lean/AlethfeldLean/GraphTheory/Reconstruction/
git add lean/AlethfeldLean/GraphTheory/ReconstructionSmall.lean
```

## References

- Original handoff: Still valid for mathematical context
- Orchestrator protocol: `/home/tobias/Projects/alethfeld/orchestrator-prompt-v5.1-claude.md`
- Mathlib graph theory: `Mathlib.Combinatorics.SimpleGraph.*`
