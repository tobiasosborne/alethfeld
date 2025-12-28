# Pickup Prompt: L2 Sorry Elimination

## Quick Start

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
bd ready                    # See 3 issues ready to work
bd show <id>                # View issue details with proof strategy
lake build                  # Verify current state compiles
```

## Context

You're working on **Alethfeld**, a Lean 4 formalization of quantum Boolean function analysis. The L2 module (`L2Influence.lean`) proves that the **influence of rank-1 product state QBFs is universal**: I(U) = n * 2^{1-n}, independent of Bloch vectors.

## Current State

- **File**: `lean/AlethfeldLean/QBF/Rank1/L2Influence.lean`
- **Build**: Compiles successfully (3 sorry warnings)
- **Issues**: 6 open, 3 ready to work, 3 blocked by dependencies
- **Closed**: 23 of 29 issues (8 closed this session)

## Progress Summary

### Completed (8 issues closed)

| Track | Status | What was done |
|-------|--------|---------------|
| Track 4 | **COMPLETE** | `influence_decreasing` sorry eliminated |
| Track 2 helpers | **COMPLETE** | S2a, S2b, S2c all proven |
| Track 3 helpers | **COMPLETE** | S3a, S3b all proven |

### Helper Lemmas Added

```lean
-- Track 4 (all complete)
nat_le_pow_two_sub_one    -- n ≤ 2^{n-1} for n ≥ 1
influence_bound_real       -- n * 2^{1-n} ≤ 1
influence_decreasing       -- SORRY ELIMINATED

-- Track 2 helpers (all complete)
card_complement_singleton  -- |{k : Fin n // k ≠ j}| = n - 1
prod_const_two            -- ∏_{k∈α} 2 = 2^|α|
exponent_simplify         -- 2^{2-2n} * 2^{n-1} = 2^{1-n}

-- Track 3 helpers (all complete)
influence_j_eq_sum_partialSum  -- Partition influence_j by α_j value
factor_out_power               -- Factor 2^{1-n} from conditional sum
```

## The 3 Remaining Sorries

| Line | Theorem | Difficulty | Status |
|------|---------|------------|--------|
| 100 | `factorization_lemma` | **Hard** | Track 1 - CRITICAL PATH |
| 110 | `partial_sum_simplified` | Medium | Blocked by S1d |
| 160 | `influence_j_formula` | Medium | Blocked by S2d |

## Dependency Graph (Updated)

```
Track 1 (factorization_lemma) - THE CRITICAL PATH:
  S1a: MultiIndex decomposition ─┐
  S1b: Product factorization ────┼─→ S1d: factorization_lemma [SORRY]
  S1c: Sum-product interchange ──┘

Track 2 (partial_sum_simplified):
  S2a: ✅ card_complement_singleton
  S2b: ✅ prod_const_two          ──→ S2d: partial_sum_simplified [SORRY]
  S2c: ✅ exponent_simplify            (blocked by S1d)

Track 3 (influence_j_formula):
  S3a: ✅ influence_j_eq_sum_partialSum ─→ S3c: influence_j_formula [SORRY]
  S3b: ✅ factor_out_power                    (blocked by S2d)

Track 4 (influence_decreasing) - ✅ COMPLETE:
  S4a: ✅ nat_le_pow_two_sub_one
  S4b: ✅ influence_bound_real
  S4c: ✅ influence_decreasing
```

## Ready Issues (Critical Path)

Run `bd ready` to see all. **All 3 are Track 1**:

- **`alethfeld-xqg`** (S1a): MultiIndex decomposition - reindex sum over {α | α_j = ℓ}
- **`alethfeld-loh`** (S1b): Product factorization when α_j is fixed
- **`alethfeld-hy2`** (S1c): Apply Fintype.prod_sum (Fubini for finite sums)

## Recommended Approach

**Focus entirely on Track 1** - it's the only blocker now.

1. **Start with S1a** (the key insight):
   ```bash
   bd update alethfeld-xqg --status=in_progress
   # Decompose MultiIndex sum: ∑_{α} = ∑_{ℓ} ∑_{α: α_j=ℓ}
   # Key: Equiv.piSplitAt to split the function space
   ```

2. **Then S1b** (product factorization):
   ```bash
   bd update alethfeld-loh --status=in_progress
   # When α_j = ℓ is fixed, qProduct factors
   ```

3. **Then S1c** (Fubini):
   ```bash
   bd update alethfeld-hy2 --status=in_progress
   # Apply Fintype.prod_sum to swap ∑ and ∏
   ```

4. **Complete S1d** (factorization_lemma):
   - Combine S1a, S1b, S1c to eliminate the first sorry

5. **S2d and S3c follow quickly** once S1d is done - all helpers are in place.

## Key Mathlib Lemmas for Track 1

```lean
-- For S1a (MultiIndex decomposition) - THIS IS THE CRUX
Equiv.piSplitAt j          -- (Fin n → X) ≃ X × ({k // k ≠ j} → X)
Fintype.sum_equiv          -- Reindex a sum via equivalence

-- For S1b (Product factorization)
Finset.prod_erase_mul      -- Already used in qProduct_split

-- For S1c (Fubini for finite sums)
Fintype.prod_sum           -- ∏_i ∑_x f i x = ∑_f ∏_i f i (f i)
-- Or alternatively:
Finset.prod_sum            -- Similar for Finset
```

## File Location

```
lean/AlethfeldLean/QBF/Rank1/L2Influence.lean  # YOUR TARGET FILE
```

## Workflow

```bash
# Claim an issue
bd update <id> --status=in_progress

# Edit the file - add helper lemmas above the sorry
# Replace sorry with proof

# Test compilation
lake build

# When done
bd close <id> --reason="Proved theorem X using Y"
bd sync
```

## Session Close Protocol

Before ending:
```bash
git status                  # Check changes
git add <files>             # Stage code
bd sync                     # Commit beads
git commit -m "..."         # Commit code
bd sync                     # Sync again
git push                    # Push to remote
```

## Success Criteria

- All 3 remaining sorries eliminated
- `lake build` completes with no sorry warnings in L2Influence.lean
- All 29 issues closed (6 remaining)
- Changes pushed to remote

## Tips

1. **Track 1 is the only blocker** - all helper lemmas for Tracks 2 & 3 are done
2. **S1a is the crux** - once you decompose the MultiIndex sum, everything follows
3. **Use `#check` liberally** - verify lemma types before using
4. **The q_sum lemmas are key** - `BlochVector.q_sum_eq_two` and `q_nonzero_sum_eq_one` are already proven
5. **Read existing helper lemmas** - `qProduct_split` shows the pattern for product factorization

Good luck! You're close to the finish line.
