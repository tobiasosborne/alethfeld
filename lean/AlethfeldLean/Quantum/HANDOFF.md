# Quantum Entropy Increase Theorem - Lean Formalization Handoff

## Session Date: 2026-01-07

## Overview

This document provides a detailed handoff for continuing the Lean 4 formalization of the Quantum Entropy Increase Theorem. The main theorem states:

```
H(L̃_f) = H(L_f) + Inf(L_f)
```

Where `L̃_f = T⊗ⁿ H⊗ⁿ L_f (H⊗ⁿ)† (T⊗ⁿ)†` is the transformed diagonal observable.

## Current State

### Build Status
- **All files compile successfully** with `lake build`
- Only warnings (style/deprecation), no errors
- 4 sorries remain, all in `EntropyIncrease.lean`

### Sorry Count
```
AlethfeldLean/Quantum/EntropyIncrease.lean:672:      sorry  # X/Y IH case
AlethfeldLean/Quantum/EntropyIncrease.lean:727:      sorry  # I case IH
AlethfeldLean/Quantum/EntropyIncrease.lean:759:      sorry  # Trace cycling
AlethfeldLean/Quantum/EntropyIncrease.lean:778:      sorry  # pauliCoeff final
```

### Files Modified This Session
1. `AlethfeldLean/Quantum/Gates.lean` - Added T gate unitarity lemmas
2. `AlethfeldLean/Quantum/EntropyIncrease.lean` - Proof progress

## Completed Work

### 1. T Gate Unitarity (Gates.lean, lines 119-140)

Added two new lemmas:

```lean
/-- exp(-iπ/4) * exp(iπ/4) = 1 (commuted form) -/
lemma exp_neg_pi4_mul_exp_pi4 :
    Complex.exp (-Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = 1

/-- T gate is unitary: T† T = 1 -/
lemma tGate_conjTranspose_mul_tGate : tGate.conjTranspose * tGate = 1
```

These are used to prove `H† T† T H = H† H` in the identity case.

### 2. EntropyIncrease.lean Structure

The file contains the main theorem `entropy_increase_theorem` which depends on:
- `backTransformed_pauli_diag_of_tExpansion` (lines 568-727) - **Has 2 sorries**
- `pauliCoeff_transformedObs_at_expansion` (lines 741-778) - **Has 2 sorries**

## Remaining Sorries - Detailed Analysis

### Sorry 1: X/Y IH Case (Line 672)

**Location**: `backTransformed_pauli_diag_of_tExpansion`, case `0 ∈ S`

**Context**: After establishing that the single-qubit diagonal contribution is `(1/√2) * σZ_diag`, we need to apply the inductive hypothesis to the rest of the tensor product.

**Goal** (paraphrased):
```lean
(rest_diagonal) * ((1/√2) * σZ_diag) = (1/√2)^|S| * pauliZ_S S x x
```

**What's Needed**:
1. Define `S' : Finset (Fin n) := Finset.univ.filter (fun k => k.succ ∈ S)`
2. Show `(fun m => α m.succ) ∈ tExpansionPaulis S'`
3. Apply IH to get `(rest diagonal) = (1/√2)^|S'| * pauliZ_S S' ...`
4. Show `|S'| + 1 = |S|` (since 0 ∈ S)
5. Show `pauliZ_S S x x = pauliZ_S S' x.1 x.1 * σZ x.2 x.2`

**Key Lemmas Needed**:
```lean
-- Finset cardinality: |{k | k.succ ∈ S}| = |S| - 1 when 0 ∈ S
lemma finset_succ_card_eq (S : Finset (Fin (n+1))) (h0 : 0 ∈ S) :
    (Finset.univ.filter (fun k : Fin n => k.succ ∈ S)).card = S.card - 1

-- pauliZ_S Kronecker factorization
lemma pauliZ_S_factor (S : Finset (Fin (n+1))) (h0 : 0 ∈ S) (x : Fin (2^(n+1))) :
    pauliZ_S S x x = pauliZ_S S' (finPow2SuccEquiv n x).1 (finPow2SuccEquiv n x).1 *
                      σZ (finPow2SuccEquiv n x).2 (finPow2SuccEquiv n x).2
```

### Sorry 2: I Case IH (Line 727)

**Location**: `backTransformed_pauli_diag_of_tExpansion`, case `0 ∉ S`

**Context**: Similar to X/Y case but simpler. The single-qubit contribution is 1 (identity).

**Goal** (paraphrased):
```lean
(rest_diagonal) = (1/√2)^|S| * pauliZ_S S x x
```

**What's Needed**:
1. Define `S' : Finset (Fin n) := Finset.univ.filter (fun k => k.succ ∈ S)`
2. Show `(fun m => α m.succ) ∈ tExpansionPaulis S'`
3. Apply IH to get `(rest diagonal) = (1/√2)^|S'| * pauliZ_S S' ...`
4. Show `|S'| = |S|` (since 0 ∉ S, all elements are ≥ 1)
5. Show `pauliZ_S S x x = pauliZ_S S' x.1 x.1` (bit 0 doesn't contribute)

**Key Lemmas Needed**:
```lean
-- Finset cardinality: |{k | k.succ ∈ S}| = |S| when 0 ∉ S
lemma finset_succ_card_eq_of_not_mem (S : Finset (Fin (n+1))) (h0 : 0 ∉ S) :
    (Finset.univ.filter (fun k : Fin n => k.succ ∈ S)).card = S.card

-- pauliZ_S doesn't depend on bit 0 when 0 ∉ S
lemma pauliZ_S_independent_bit0 (S : Finset (Fin (n+1))) (h0 : 0 ∉ S) (x : Fin (2^(n+1))) :
    pauliZ_S S x x = pauliZ_S S' (finPow2SuccEquiv n x).1 (finPow2SuccEquiv n x).1
```

### Sorry 3: Trace Cycling (Line 759)

**Location**: `pauliCoeff_transformedObs_at_expansion`, helper `h_cycle`

**Goal**:
```lean
((pauliString α)ᴴ * (T * H * L * Hᴴ * Tᴴ)).trace =
    (Hᴴ * Tᴴ * (pauliString α)ᴴ * T * H * L).trace
```

Where T = kroneckerPow n tGate, H = kroneckerPow n hadamard, L = diagonalObs f.

**What's Needed**:
This is trace cycling: Tr(A₁A₂A₃A₄A₅A₆) = Tr(A₅A₆A₁A₂A₃A₄)

**Approach 1** - Use `Matrix.trace_mul_comm` twice:
```lean
-- Step 1: Tr(P† * rest) = Tr(rest * P†) by trace_mul_comm
-- Step 2: Tr((T H L H†) * T†) = Tr(T† * (T H L H†))
-- Step 3: Tr((T† P† T H L) * H†) = Tr(H† * (T† P† T H L))
```

**Challenge**: The associativity doesn't match well. After `simp [Matrix.mul_assoc]`, the goal becomes right-associated, but `trace_mul_comm` expects a specific grouping.

**Approach 2** - Create a dedicated helper:
```lean
lemma trace_cycle_six {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D E F : Matrix n n ℂ) :
    (A * B * C * D * E * F).trace = (E * F * A * B * C * D).trace
```

**Approach 3** - Use `Matrix.trace_mul_cycle`:
```lean
-- Matrix.trace_mul_cycle : (A * B * C).trace = (C * A * B).trace
-- Apply repeatedly to cycle by 2 positions
```

### Sorry 4: pauliCoeff Final (Line 778)

**Location**: `pauliCoeff_transformedObs_at_expansion`, final step

**Context**: After trace cycling, we have:
```lean
M = H† T† P† T H  -- back-transformed Pauli
L = diagonalObs f  -- diagonal matrix
```

**Goal**: Show that `(1/2^n) * Tr(M * L) = (1/√2)^|S| * fourierCoeff f S`

**What's Needed**:
1. For diagonal L: `Tr(M * L) = Σ_x M_xx * L_xx`
2. By `backTransformed_pauli_diag_of_tExpansion`: `M_xx = (1/√2)^|S| * pauliZ_S S x x`
3. Factor out: `Tr(M * L) = (1/√2)^|S| * Σ_x pauliZ_S S x x * L_xx`
4. The sum equals `2^n * fourierCoeff f S` by `pauliCoeff_diagonalObs_Z_S`

**Key Lemmas Needed**:
```lean
-- Trace of product with diagonal matrix
lemma trace_mul_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (d : n → ℂ) :
    (M * Matrix.diagonal d).trace = ∑ x, M x x * d x

-- Or use existing Mathlib lemma
-- Matrix.trace_mul_comm combined with diagonal properties
```

## Key Files and Locations

### EntropyIncrease.lean Structure
```
Lines 1-42:     Imports and namespace
Lines 43-80:    kroneckerPow definition
Lines 81-200:   Kronecker helper lemmas
Lines 200-400:  Gate conjugation through Kronecker
Lines 400-550:  normSq and coefficient lemmas
Lines 550-730:  backTransformed_pauli_diag_of_tExpansion (SORRIES 1,2)
Lines 730-800:  pauliCoeff_transformedObs_at_expansion (SORRIES 3,4)
Lines 800-900:  normSq_pauliCoeff and spectralDist lemmas
Lines 900+:     Main entropy increase theorem
```

### Gates.lean Key Lemmas
```
Lines 34-44:    hadamard_conjTranspose
Lines 100-140:  T gate conjugate transpose and unitarity (NEW)
Lines 140-200:  tgate_conj_X, tgate_conj_Y, tgate_conj_Z
Lines 200-270:  tgate_inv_conj_X, tgate_inv_conj_Y
Lines 270-350:  Combined H T† P T H lemmas (hadamard_tgate_inv_conj_X, etc.)
```

### Pauli.lean Key Definitions
```
σI, σX, σY, σZ : Mat2          -- Pauli matrices
σ : Fin 4 → Mat2               -- Indexed Pauli
pauliString : MultiIndex n → QubitMat n  -- n-fold tensor product
trace_pauliString              -- Tr(σ^α) = 2^n if α=0, else 0
```

### PauliDiag.lean Key Definitions
```
pauliZ_S : Finset (Fin n) → QubitMat n  -- Z-type Pauli string
pauliZ_S_diag_entry            -- Diagonal entry formula
pauliString_diag_zero_of_XY    -- Off-diagonal for X/Y components
```

## Suggested Next Steps

### Priority 1: Trace Cycling (Sorry 3)
This is the most self-contained proof. Try:
1. Create a helper lemma that handles the 6-matrix cycle
2. Use explicit `calc` with `Matrix.trace_mul_comm`
3. Be careful with associativity - may need `conv` to match patterns

### Priority 2: I Case IH (Sorry 2)
Simpler than X/Y case because 0 ∉ S:
1. The cardinality is preserved: `|S'| = |S|`
2. The pauliZ_S factorization is simpler (no σZ factor)

### Priority 3: X/Y Case IH (Sorry 1)
Similar structure to I case but with extra complexity:
1. Cardinality decreases by 1
2. Need σZ factor in the pauliZ_S decomposition

### Priority 4: pauliCoeff Final (Sorry 4)
Depends on trace cycling and diagonal properties:
1. Use `backTransformed_pauli_diag_of_tExpansion` for M_xx
2. Factor out (1/√2)^|S|
3. Connect to `pauliCoeff_diagonalObs_Z_S` from SpectralDist.lean

## Mathematical Validity

All remaining sorries correspond to mathematically valid statements that are verified in the EDN proof graph. The challenges are purely Lean proof engineering:
- Finset manipulation and cardinality arithmetic
- Matrix associativity and trace cycling
- Kronecker product factorization

## Build and Test Commands

```bash
# Build the module
lake build AlethfeldLean.Quantum.EntropyIncrease

# Count sorries
grep -r "sorry" --include="*.lean" AlethfeldLean/Quantum/ | wc -l

# Check specific file
lake build AlethfeldLean.Quantum.Gates
```

## Ralph Loop Completion Criterion

Output `<promise>COMPLETE</promise>` when:
- All 4 remaining sorries are eliminated
- `lake build` succeeds with no errors
- `grep -r "sorry"` returns 0 results in the Quantum module
