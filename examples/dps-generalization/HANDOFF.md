# DPS Generalization Theorem - Handoff

**Date:** 2026-01-11
**Session:** Applied orchestrator-prompt-v5.1-claude.md to theorem in `prompt DPS.tex`

## Summary

Formalized a proof that symmetric extensions characterize the minimal tensor product for proper cones — a generalization of the Doherty-Parrilo-Spedalieri (DPS) theorem from quantum states to arbitrary convex cones.

## Theorem Statement

For proper cones C_A and C_B, and x ∈ C_A ⊗_max C_B:

> x has symmetric extensions to k copies for all k ≥ 1 **iff** x ∈ C_A ⊗_min C_B

## Artifacts Created

| File | Description | Status |
|------|-------------|--------|
| `proofs/dps-generalization.edn` | Semantic proof graph (37 nodes) | Verified, gitignored |
| `lean/AlethfeldLean/Examples/DPSGeneralization.lean` | Lean 4 skeleton | Committed |
| `examples/dps-generalization/proof.tex` | LaTeX proof document | Committed |
| `examples/dps-generalization/proof.pdf` | Compiled PDF (5 pages) | Generated, gitignored |

## Proof Structure

### Forward Direction (⟸): min → extensions
10 steps. Straightforward construction:
- If x = Σλᵢ(aᵢ⊗bᵢ), define yₖ = Σλᵢ(aᵢ^⊗k⊗bᵢ)
- Normalize so φ(aᵢ) = 1
- Verify symmetry and reduction properties

### Backward Direction (⟹): extensions → min
17 steps. De Finetti approach:
- Choose basis {eⱼ} from int(C_B)
- Define reduced elements x̄_{eⱼ,k} ∈ C_A^⊗k
- Show sequence is exchangeable
- Apply de Finetti theorem to get integral representation
- Reconstruct x as convex combination → x ∈ min tensor

## External Dependencies

- **de Finetti Theorem** (DOI: 10.1214/aoms/1177729952)
  - Used in step :2-bwd008
  - Registered as external-ref `ext-definetti` in EDN graph

## Lean Status

The Lean file is a **skeleton with sorries**. Key structures defined:
- `ProperCone` structure
- `minTensorProduct`, `maxTensorProduct` definitions
- `HasSymmetricExtension`, `HasAllSymmetricExtensions` predicates
- Main theorem `dps_generalization` with both directions

**To complete formalization:**
1. Flesh out `HasSymmetricExtension` definition (requires tensor power machinery)
2. Prove `min_implies_symmetric_extensions` (direct construction)
3. Prove `symmetric_extensions_implies_min` (requires de Finetti formalization)

## Graph Statistics

```
Graph ID: graph-4be308-49c58e
Version: 76
Nodes: 37 total (4 assumptions, 3 definitions, 24 claims, 2 local-assume, 2 local-discharge, 1 external-ref, 1 qed)
Status: All verified
Taint: Clean (0 tainted)
```

## Commits

1. `314cb42` - feat: Add DPS generalization theorem Lean skeleton
2. `7f45f32` - docs: Add LaTeX proof document for DPS generalization

## Next Steps

1. **Formalize de Finetti in Lean** - This is the key blocker for full formalization
2. **Extract lemmas** - The EDN graph could benefit from extracting:
   - "Generating cone has basis in interior" (step :2-bwd002)
   - "Positive functional gives cone element via bipolar" (step :2-bwd011)
3. **Verify external reference** - Run reference checker on ext-definetti

## Source Material

Original theorem from `prompt DPS.tex` — a generalization of Theorem 2 (quantum DPS) to Theorem 1 (proper cones). The proof strategy follows the quantum case from Doherty-Parrilo-Spedalieri 2004.
