# Pickup Prompt: L4Maximum Sorry Elimination - MODULARIZATION REQUIRED

## Status: BLOCKED - Files Too Large, Need Refactoring

**Last Updated:** 2025-12-28 (Session 4)

## Problem Statement

The `ShannonLemma.lean` and `L4Maximum.lean` files have grown too large and complex to debug effectively. The current approach of trying to fix all errors in a single session has failed due to:

1. **File Size**: `ShannonLemma.lean` is ~470 lines with complex nested case analysis
2. **Cascading Errors**: Fixing one proof often breaks others due to shared dependencies
3. **Mathlib API Complexity**: Many lemma names have changed or require specific imports
4. **Context Overload**: Too many interconnected proofs to track in a single session

## Recommended Strategy: Modularization

Break the files into **small, independently compilable modules** (<200 lines each) that can be fixed one at a time.

### Proposed Module Structure

```
AlethfeldLean/QBF/Rank1/
├── L3Entropy.lean              (existing, working)
├── Shannon/
│   ├── Basic.lean              (~50 lines) - log2, entropyTerm definitions
│   ├── NegMulLogBound.lean     (~100 lines) - single-term bounds using log inequalities
│   ├── SumBound.lean           (~100 lines) - entropyTerm_sum_bound
│   ├── StrictBound.lean        (~100 lines) - strict inequality proofs
│   └── Maximum.lean            (~50 lines) - final shannon_max_uniform theorems
├── L4Maximum/
│   ├── MagicState.lean         (~80 lines) - magicBlochVector, isMagicState
│   ├── EntropyBound.lean       (~60 lines) - bloch_entropy_bound
│   └── Main.lean               (~60 lines) - max_at_magic_state theorem
└── ShannonLemma.lean           (deprecate, re-export from Shannon/)
```

### Key Mathematical Facts Needed

The proofs require these Mathlib lemmas (verify names before use!):

```lean
-- In Mathlib.Analysis.SpecialFunctions.Log.Basic:
Real.log_le_sub_one_of_pos : 0 < x → log x ≤ x - 1
Real.log_lt_sub_one_of_pos : 0 < x → x ≠ 1 → log x < x - 1
Real.one_sub_inv_le_log_of_pos : 0 < x → 1 - x⁻¹ ≤ log x

-- In Mathlib.Analysis.SpecialFunctions.Log.NegMulLog:
Real.negMulLog : ℝ → ℝ  -- defined as -x * log x
Real.strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici 0) negMulLog
```

### Core Proof Strategy

The Shannon entropy maximum theorem follows from:

1. **Single-term bound**: For p > 0:
   ```
   -p * log₂(p) ≤ p * log₂(3) + (1/3 - p) / ln(2)
   ```
   Proof: Use `log(x) ≥ 1 - 1/x` with x = 3p, then algebra.

2. **Sum bound**: Sum the single-term bounds for p1, p2, p3.
   The residual `(1/3 - p1) + (1/3 - p2) + (1/3 - p3) = 0` when p1 + p2 + p3 = 1.

3. **Strict version**: Use `log(x) > 1 - 1/x` for x ≠ 1.

## Beads Issues to Create

Create the following issues using `bd create`:

### Issue 1: Create Shannon/Basic.lean
- Extract `log2`, `entropyTerm` definitions from L3Entropy
- Add basic lemmas: `log_two_pos`, `entropyTerm_of_pos`, `entropyTerm_zero`
- Target: ~50 lines, must compile without sorry

### Issue 2: Create Shannon/NegMulLogBound.lean
- Prove `entropyTerm_le_helper` (single-term bound)
- Import NegMulLog from Mathlib
- Use `one_sub_inv_le_log_of_pos` carefully
- Target: ~100 lines

### Issue 3: Create Shannon/StrictBound.lean
- Prove `entropyTerm_lt_helper` (strict version)
- Depends on Issue 2
- Target: ~100 lines

### Issue 4: Create Shannon/SumBound.lean
- Prove `entropyTerm_sum_bound` and `neg_mul_log_concave_sum`
- Depends on Issue 2
- Target: ~100 lines

### Issue 5: Create Shannon/Maximum.lean
- Prove `shannon_max_uniform`, `shannon_max_uniform_iff`
- Depends on Issues 3, 4
- Target: ~50 lines

### Issue 6: Create L4Maximum/MagicState.lean
- Extract magic state definitions
- Prove `magic_q_one`, `magic_q_two`, `magic_q_three`, `magic_q_pos`
- Target: ~80 lines, must compile without sorry

### Issue 7: Create L4Maximum/EntropyBound.lean
- Prove `blochEntropy_magic`, `bloch_entropy_bound`
- Depends on Issue 5
- Target: ~60 lines

### Issue 8: Create L4Maximum/Main.lean
- Final theorems: `max_at_magic_state`, `max_iff_magic_state`
- Depends on Issues 6, 7
- Target: ~60 lines

## Current File Locations

- `lean/AlethfeldLean/QBF/Rank1/ShannonLemma.lean` - BROKEN, has errors
- `lean/AlethfeldLean/QBF/Rank1/L4Maximum.lean` - may have errors depending on Shannon

## Build Commands

```bash
# Test individual modules after creating them:
lake build AlethfeldLean.QBF.Rank1.Shannon.Basic
lake build AlethfeldLean.QBF.Rank1.Shannon.NegMulLogBound
# etc.
```

## Session 4 Summary (Dec 28, 2025)

**What was attempted:**
- Tried to fix all sorries in ShannonLemma.lean in one session
- Added proof using `log(x) ≥ 1 - 1/x` inequality
- Wrote large case-split proof for `entropyTerm_sum_lt`

**What failed:**
- Multiple Mathlib API mismatches (`div_le_iff`, `Real.one_sub_inv_lt_log_of_pos`)
- Proof became >400 lines with nested case analysis
- Too many interdependent goals to debug effectively

**Lesson learned:**
- Large monolithic proofs are fragile and hard to debug
- Better to have many small files that compile independently
- Each file should have a single focused goal

## Next Agent Instructions

1. **Do NOT try to fix the current ShannonLemma.lean** - it's too broken
2. Run `bd create` for each of the 8 issues above
3. Start with Issue 1 (Shannon/Basic.lean) - smallest, no dependencies
4. Verify each module compiles before moving to the next
5. Use `bd close` as each issue is completed
6. At session end: `bd sync && git push`

## Files to Eventually Delete

Once modularization is complete, delete:
- `lean/AlethfeldLean/QBF/Rank1/ShannonLemma.lean` (replaced by Shannon/)
- Or keep as re-export wrapper
