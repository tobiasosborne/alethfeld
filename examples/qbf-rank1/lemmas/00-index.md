# QBF Rank-1 Extracted Lemmas

## Lemma Decomposition Report

```
═══════════════════════════════════════════════════════════════
ALETHFELD LEMMA DECOMPOSER
═══════════════════════════════════════════════════════════════
Source Graph: qbf-rank1-entropy-influence v2
Extraction Date: 2025-12-28
═══════════════════════════════════════════════════════════════
```

## Extracted Lemmas

| ID | Name | Root Node | Nodes | Benefit | Status |
|----|------|-----------|-------|---------|--------|
| L1 | Fourier Coefficient Formula | :1-lem1 | 6 | 0.65 | extracted |
| L2 | Influence Independence | :1-thm3 | 6 | 0.72 | extracted |
| L3 | General Entropy Formula | :1-thm5 | 8 | 0.68 | extracted |
| L4 | Maximum at Magic State | :1-thm6 | 6 | 0.61 | extracted |
| L5 | Asymptotic Limit | :1-thm8 | 8 | 0.58 | extracted |

## Dependency Order

```
L1 (Fourier) ──→ L2 (Influence)
                      ↓
L1 ──→ L3 (Entropy) ←─┘
              ↓
         L4 (Maximum) ──→ L5 (Asymptotic)
```

## Files

```
lemmas/
├── 00-index.md          # This file
├── L1-fourier.edn       # Fourier coefficient formula
├── L1-fourier.lean      # Lean 4 skeleton
├── L2-influence.edn     # Influence independence theorem
├── L2-influence.lean    # Lean 4 skeleton
├── L3-entropy.edn       # General entropy formula
├── L3-entropy.lean      # Lean 4 skeleton
├── L4-maximum.edn       # Maximum at magic state
├── L4-maximum.lean      # Lean 4 skeleton
├── L5-asymptotic.edn    # Asymptotic limit
└── L5-asymptotic.lean   # Lean 4 skeleton
```

## Independence Verification

All extracted lemmas satisfy:
1. ✓ Internal dependencies within lemma boundary
2. ✓ External dependencies are only assumptions or verified nodes
3. ✓ Only root node depended on from outside
4. ✓ Local assumptions balanced with discharges (where applicable)

## Usage

Each lemma can be:
1. Independently verified by the Verifier agent
2. Formalized in Lean 4 using the skeleton
3. Referenced via `:lemma-ref` in the main proof
