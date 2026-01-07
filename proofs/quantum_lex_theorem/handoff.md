# Quantum Entropy Increase Theorem - Handoff Document

**Date:** 2026-01-07
**Status:** In Progress - 3 compile errors + 2 axioms to remove

## Overview

This document provides a comprehensive handoff for the ongoing work on proving the Quantum Entropy Increase Theorem (Theorem 1) in Lean 4 with no sorries.

## Goal

From `ralph-prompt.md`:
- Execute the Alethfeld protocol to prove Theorem 1
- Prove all lemmas and theorem in Lean with **NO sorries** and **NO cheating axiomatizing**
- Output `<promise>COMPLETE</promise>` when done

## Current State

### Lean File Location
`/home/tobiasosborne/Projects/alethfeld/lean/AlethfeldLean/Quantum/EntropyIncrease.lean`

### Remaining Issues: 3 compile errors + 2 axioms

| Line | Issue | Status | Difficulty |
|------|-------|--------|------------|
| 879 | `pauliCoeff_diagonalObs_Z_S` - sum_congr type mismatch | Error | Medium - needs sum bijection |
| 1052 | `diagonalObs_spectralEntropy_eq` - sum_bij' mismatch | Error | Hard - needs filter bijection |
| 1115 | `diagonalObs_quantumInfluence_eq` - sum_bij' mismatch | Error | Hard - needs filter bijection |
| 1190 | `spectral_entropy_transform_axiom` | Axiom to remove | Hard |
| 1221 | `quantum_influence_transform_axiom` | Axiom to remove | Hard |

### Completed Proofs This Session

1. **`character_completeness`** (lines 378-443) - **FIXED**
   - Uses `Finset.sum_involution` for the x ≠ y case
   - Fixed type issues with explicit `interval_cases` handling

2. **`fourier_inversion`** (lines 457-489) - **FIXED**
   - Uses `character_completeness` to show only x = y term survives
   - Fixed by using `simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]`

3. **`pauliString_diag_zero_of_XY`** - was already working

4. **`pauliCoeff_diagonalObs_nonZ`** - was already working

### Core Issue: Sum Type Mismatches

The main remaining challenge is that several proofs require showing equality between:
- Sums over `Fin (2^n)` (matrix indices)
- Sums over `Fin n → Bool` (Boolean function inputs)

These are finite types of the same cardinality, related by the bijection:
```lean
fun x : Fin (2^n) => fun i : Fin n => x.val.testBit i.val
```

The current code uses `sum_congr rfl` which fails because Lean doesn't automatically see these types as the same. Need to use `Finset.sum_bij` with this explicit bijection.

## Key Definitions

### Core Types
```lean
def BoolFunc (n : ℕ) := (Fin n → Bool) → ℤ  -- Boolean function {0,1}^n → {±1}
def parityFunc {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ  -- χ_S(x)
noncomputable def fourierCoeff {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) : ℝ
noncomputable def diagonalObs {n : ℕ} (f : BoolFunc n) : QubitMat n  -- L_f
```

### Bijection (defined in code but needs lemmas)
```lean
let toBoolFunc : Fin (2^n) → (Fin n → Bool) := fun x i => x.val.testBit i.val
```

## Recommended Next Steps

### Priority 1: Fix `pauliCoeff_diagonalObs_Z_S` (line 879)

Replace `apply Finset.sum_congr rfl` with `Finset.sum_bij` using the testBit bijection.

Need to prove:
1. `toBoolFunc` is a bijection between `Fin (2^n)` and `Fin n → Bool`
2. For each `x : Fin (2^n)`, the term transformation is correct

### Priority 2: Fix `diagonalObs_spectralEntropy_eq` (line 1052)

The `sum_bij'` with `toZIndex` is failing because:
- LHS sums over `{α : Fin n → Fin 4 | ¬∃ i, α i ∈ {1, 2}}`
- RHS sums over `Finset (Fin n)`

Need to adjust the bijection arguments or restructure the proof.

### Priority 3: Fix `diagonalObs_quantumInfluence_eq` (line 1115)

Same issue as Priority 2 - `sum_bij'` arguments don't unify.

### Priority 4: Remove Axioms (lines 1190, 1221)

Replace `axiom spectral_entropy_transform_axiom` and `axiom quantum_influence_transform_axiom` with actual proofs. These encode:
- TH transformation effect on spectral entropy
- TH transformation preserves influence

These require the Kronecker power infrastructure that's partially built.

## File Structure

```
proofs/quantum_lex_theorem/
├── quantum_lex_theorem.md   # Main theorem statement
├── lemma1.edn through lemma6.edn  # EDN proof graphs
├── theorem1.edn             # Main theorem EDN
├── proof.tex                # LaTeX document
├── proof.pdf                # Compiled proof
└── handoff.md               # This file

lean/AlethfeldLean/Quantum/
├── Basic.lean               # Core quantum definitions
├── Pauli.lean               # Pauli matrices and pauliString
└── EntropyIncrease.lean     # Main theorem (~1170 lines)
```

## Mathematical Background

### Theorem 1: Quantum Entropy Increase
For a Boolean function f: {0,1}^n → {±1}, the TH transformation (T⊗ⁿ H⊗ⁿ) applied to the diagonal observable L_f satisfies:

1. **Entropy Increase**: H(TH · L_f) = H(L_f) + Inf(L_f)
2. **Influence Preservation**: Inf(TH · L_f) = Inf(L_f)

Where:
- H(·) is spectral entropy
- Inf(·) is total influence (sum of Fourier weights times subset sizes)
- L_f is the diagonal matrix with f(x) on diagonal

### Key Lemmas
1. **Diagonal Pauli Expansion**: L_f = Σ_S f̂(S) Z_S
2. **Hadamard Conjugation**: H Z H† = X
3. **T Gate Conjugation**: T X T† splits into uniform superposition
4. **T Expansion**: Maps X_S to 2^|S| terms of equal magnitude
5. **Weight Preservation**: Product unitaries preserve Pauli weight
6. **Entropy of Uniform Splitting**: Entropy increases by log(k) when splitting into k equal parts

## Technical Notes

1. The `Fin (2^n) ≃ (Fin n → Bool)` equivalence is established via testBit
2. The `toZIndex` function maps `Finset (Fin n)` to `Fin n → Fin 4` (for Z-indices)
3. All EDN proofs and LaTeX are complete; only Lean formalization remains
4. The file has ~1170 lines with substantial infrastructure already built

## Commands to Resume

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
# Build to see errors
lake build AlethfeldLean.Quantum.EntropyIncrease 2>&1 | grep "^error:"
# Check for axioms (should be 2)
grep -n "^axiom" AlethfeldLean/Quantum/EntropyIncrease.lean
# Check for sorries (should be 0)
grep -n "sorry" AlethfeldLean/Quantum/EntropyIncrease.lean
```

## Session History

### 2026-01-07 Session
- Fixed `character_completeness` proof using `interval_cases` approach
- Fixed `fourier_inversion` proof using proper sum manipulation
- Fixed various simp/ring issues throughout the file
- Identified remaining issues: 3 compile errors (sum bijection problems) + 2 axioms
