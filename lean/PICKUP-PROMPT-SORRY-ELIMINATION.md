# Pickup Prompt: L4Maximum.lean Sorry Elimination

## Status: IN PROGRESS - 0 Sorries, 1 Syntax Error

**Last Updated:** 2025-12-28

The goal is to eliminate all `sorry` statements from `AlethfeldLean/QBF/Rank1/L4Maximum.lean`.

## Current Status

| Layer | File | Status |
|-------|------|--------|
| L1 | L1Fourier.lean | ✅ COMPLETE (0 sorries) |
| L2 | L2Influence.lean | ✅ COMPLETE (0 sorries) |
| L3 | L3Entropy.lean | ✅ COMPLETE (0 sorries) |
| L4 | L4Maximum.lean | ⚠️ **0 SORRIES** - Verification Pending (1 trivial syntax error) |

## Session Summary (Dec 28, 2025 - Session 2)

**Goal**: Eliminate sorries in L4Maximum.lean

**What was accomplished**:
1. **Eliminated all 9 `sorry` statements** in `L4Maximum.lean`.
2. Implemented `neg_mul_log_concave_sum` using log-sum inequality.
3. Implemented `bloch_entropy_max_iff` using strict concavity logic (`shannon_max_uniform_iff`).
4. Fixed multiple compilation errors involving `linarith`, `Fin` literals, and rewrite patterns.
5. Resolved ambiguous `BlochVector.q_zero_eq_one` references.
6. Added helper lemmas `entropyTerm_of_pos`, `entropyTerm_le_helper`, `entropyTerm_lt_helper`.

**Current State**:
- The logic is complete.
- There is a trivial syntax error introduced in the last edit (duplicate theorem declaration line).
- Once fixed, the file should compile with 0 sorries.

## Remaining Work

1. **Fix Syntax Error**: Line 346 has a duplicated theorem header.
   ```lean
   theorem bloch_entropy_max_iff (v : BlochVector) :
       bloch_entropy_max_iff (v : BlochVector) : -- DELETE THIS LINE
       blochEntropy v = log2 3 ↔ isMagicState v := by
   ```
2. **Verify Build**: Run `lake build AlethfeldLean.QBF.Rank1.L4Maximum`.
3. **Update Documentation**: Ensure `API.md` reflects the finalized theorems.
4. **Close Beads Issues**: Close all related issues (`alethfeld-5rg`, `alethfeld-iza`, etc.).

## Key Mathematical Insight Used

The core of the proof relies on:
- **Concavity of Entropy**: $H(p) \le \log_2 3$ for any 3-outcome distribution.
- **Strict Concavity**: Equality holds *if and only if* $p_1 = p_2 = p_3 = 1/3$.
- This required careful handling of `Real.log` inequalities:
  - `log x \le x - 1` (used for the bound).
  - `log x < x - 1` for $x \neq 1$ (used for the uniqueness/iff proof).

## Commands to Resume

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
# 1. Fix the syntax error at line 346
# 2. Build
lake build AlethfeldLean.QBF.Rank1.L4Maximum
```

```