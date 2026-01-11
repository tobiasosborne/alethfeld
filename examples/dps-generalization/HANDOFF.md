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
Version: 216
Nodes: 103 total (refined from 37)
  - 4 assumptions, 3 definitions
  - 90 claims (depth 2 and 3)
  - 2 local-assume, 2 local-discharge
  - 1 external-ref, 1 qed
Status: 99 verified, 4 admitted
Taint: 84 clean, 19 tainted (by admitted nodes)
Max Depth: 3 (substeps added for all depth-2 claims)
```

### Admitted Steps (requiring further mathematical work)

The following 4 substeps were admitted due to gaps in the cone preservation argument:

1. **:3-bwd005a-v3**: Contraction with basis functional $e_j^*$ and cone structure
2. **:3-bwd005b**: Cone preservation under $(id \otimes e_j^*)$
3. **:3-bwd005c**: Application of $\phi^{\otimes(k-1)}$ preserves membership
4. **:3-bwd010c-v3**: Positivity of $F_a$ from de Finetti consistency

**Root Issue**: The proof uses dual basis functionals $e_j^*$ which are not necessarily in the dual cone $\mathsf{C}_B^*$. This requires either (a) a modified argument using functionals in the dual cone, or (b) a careful analysis of how the de Finetti structure compensates for this gap.

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
