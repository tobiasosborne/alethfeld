# Quantum Module Manifest

**Package:** `AlethfeldLean.Quantum`
**Last Updated:** 2026-01-07

## Module Overview

This directory contains the quantum computing foundations for the Alethfeld project, including Pauli matrices, quantum gates, and the Quantum Entropy Increase Theorem.

## File Listing

### Core Modules

| File | Lines | Namespace | Description |
|------|-------|-----------|-------------|
| `Basic.lean` | 55 | `Alethfeld.Quantum.Basic` | Core types: `Mat2`, `QubitMat`, `MultiIndex`, index equivalences |
| `Pauli.lean` | 183 | `Alethfeld.Quantum.Pauli` | Pauli matrices σI, σX, σY, σZ, `pauliString`, trace properties |
| `Bloch.lean` | 253 | `Alethfeld.Quantum.Bloch` | Bloch sphere, `BlochVector`, expectation values |
| `BoolFunc.lean` | 351 | `Alethfeld.Quantum.BoolFunc` | Boolean functions, Fourier analysis, character orthogonality |
| `Gates.lean` | 367 | `Alethfeld.Quantum.Gates` | Hadamard/T gate definitions, conjugation theorems |
| `TExpansion.lean` | 181 | `Alethfeld.Quantum.TExpansion` | T expansion, `pauliWeight`, Shannon entropy |
| `DiagonalObs.lean` | 146 | `Alethfeld.Quantum.DiagonalObs` | `diagonalObs`, `pauliZ_S`, Pauli expansion theorem |
| `SpectralDist.lean` | 170 | `Alethfeld.Quantum.SpectralDist` | `pauliCoeff`, `spectralDist`, `spectralEntropy` |
| `ZIndexEquiv.lean` | 232 | `Alethfeld.Quantum.ZIndexEquiv` | Z-index bijection, entropy/influence equality |

### PauliDiag Submodules

| File | Lines | Namespace | Description |
|------|-------|-----------|-------------|
| `PauliDiag.lean` | 63 | `Alethfeld.Quantum.PauliDiag` | Re-exports all submodules |
| `PauliDiag/Single.lean` | 70 | `...PauliDiag.Single` | Single-qubit diagonal properties (σI, σZ off-diag) |
| `PauliDiag/Kronecker.lean` | 146 | `...PauliDiag.Kronecker` | Kronecker product diagonal, `pauliString_diag` |
| `PauliDiag/Trace.lean` | 121 | `...PauliDiag.Trace` | Trace lemmas for diagonal matrix products |
| `PauliDiag/Orthogonality.lean` | 143 | `...PauliDiag.Orthogonality` | Pauli product traces, orthogonality |
| `PauliDiag/General.lean` | 93 | `...PauliDiag.General` | General Kronecker diagonal lemmas |

### EntropyIncrease Submodules

| File | Lines | Namespace | Description |
|------|-------|-----------|-------------|
| `EntropyIncrease.lean` | 148 | `Alethfeld.Quantum.EntropyIncrease` | Main theorems, re-exports submodules |
| `EntropyIncrease/KroneckerPow.lean` | 94 | `...KroneckerPow` | `kroneckerPow n M` definition and structure |
| `EntropyIncrease/TransformDefs.lean` | 61 | `...TransformDefs` | `transformedObs f` definition |
| `EntropyIncrease/BackTransform.lean` | 150 | `...BackTransform` | Back-transformed Pauli diagonal lemmas |
| `EntropyIncrease/SourceSubset.lean` | 83 | `...SourceSubset` | `sourceSubset`, T-expansion disjointness |
| `EntropyIncrease/PauliCoeff.lean` | 100 | `...PauliCoeff` | Coefficient magnitude formulas |
| `EntropyIncrease/SpectralDistTransform.lean` | 257 | `...SpectralDistTransform` | Spectral distribution characterization |
| `EntropyIncrease/Entropy.lean` | 171 | `...Entropy` | Entropy/influence from expansion structure |

**Total:** ~3638 lines across 21 modules

## Dependency Graph

```
Mathlib
   │
   ├── Basic.lean
   │      │
   │      └── Pauli.lean
   │             │
   │             ├── Bloch.lean
   │             │
   │             ├── PauliDiag.lean ─────────────────────┐
   │             │    ├── PauliDiag/Single.lean         │
   │             │    ├── PauliDiag/Kronecker.lean      │
   │             │    ├── PauliDiag/Trace.lean          │
   │             │    ├── PauliDiag/Orthogonality.lean  │
   │             │    └── PauliDiag/General.lean        │
   │             │                                      │
   │             ├── Gates.lean                         │
   │             │                                      │
   │             └── TExpansion.lean                    │
   │                                                    │
   ├── BoolFunc.lean ───────────────────────────────────┼──→ DiagonalObs.lean
                                                        │           │
                                                        │    SpectralDist.lean
                                                        │           │
                                                        │    ZIndexEquiv.lean
                                                        │           │
                                                        └───────────┴──→ EntropyIncrease.lean
                                                                              │
                                                         ┌────────────────────┴────────────────────┐
                                                         │                                         │
                                              EntropyIncrease/KroneckerPow.lean                    │
                                              EntropyIncrease/TransformDefs.lean                   │
                                              EntropyIncrease/BackTransform.lean                   │
                                              EntropyIncrease/SourceSubset.lean                    │
                                              EntropyIncrease/PauliCoeff.lean                      │
                                              EntropyIncrease/SpectralDistTransform.lean           │
                                              EntropyIncrease/Entropy.lean                         │
```

## Key Entry Points

### For General Quantum Computing
```lean
import AlethfeldLean.Quantum.Basic
import AlethfeldLean.Quantum.Pauli
import AlethfeldLean.Quantum.Bloch
```

### For Quantum Entropy Increase Theorem
```lean
import AlethfeldLean.Quantum.EntropyIncrease
```
This imports all necessary submodules automatically.

## Main Definitions by Module

### Basic.lean
- `Mat2` — 2×2 complex matrix
- `QubitMat n` — 2ⁿ × 2ⁿ complex matrix
- `MultiIndex n` — Pauli index vector (Fin n → Fin 4)
- `finPow2SuccEquiv` — Index equivalence for Kronecker products

### Pauli.lean
- `σI`, `σX`, `σY`, `σZ` — Pauli matrices
- `σ : Fin 4 → Mat2` — Indexed Pauli selector
- `pauliString α` — Tensor product σ^α₁ ⊗ ... ⊗ σ^αₙ
- `trace_pauliString` — Trace is 2ⁿδ_{α,0}

### BoolFunc.lean
- `BoolFunc n` — Boolean function type {0,1}ⁿ → {±1}
- `parityFunc S x` — Character χ_S(x) = (-1)^|S∩x|
- `fourierCoeff f S` — Fourier coefficient f̂(S)
- `fourierEntropy f` — Classical Fourier entropy
- `totalInfluence f` — Classical total influence
- `character_completeness` — Σ_S χ_S(x)χ_S(y) = 2ⁿδ_{x,y}
- `fourier_inversion` — f(x) = Σ_S f̂(S)χ_S(x)

### Gates.lean
- `hadamard` — Hadamard gate H
- `tGate` — T gate
- `hadamard_conj_X/Y/Z` — H P H† conjugation
- `tgate_conj_I/Z/X/Y` — T P T† conjugation
- `hadamard_tgate_inv_conj_X/Y` — H T† X/Y T H conjugation

### PauliDiag Submodules
- **Single.lean**: `σI_off_diag`, `σZ_off_diag`, `σX_diag_zero`, `σZ_diag_entry`
- **Kronecker.lean**: `kronecker_diag_entry`, `pauliString_diag`, `pauliString_diag_entry`
- **Trace.lean**: `trace_mul_diagonal`, `trace_product_zero_of_zero_diag_and_diag`
- **Orthogonality.lean**: `trace_σ_mul_σ`, Pauli orthogonality relations
- **General.lean**: General Kronecker diagonal structure lemmas

### DiagonalObs.lean
- `pauliZ_S S` — Z_S Pauli string (Z at S, I elsewhere)
- `pauliX_S S` — X_S Pauli string (X at S, I elsewhere)
- `diagonalObs f` — L_f diagonal observable
- `diagonal_pauli_expansion` — L_f = Σ_S f̂(S) Z_S

### SpectralDist.lean
- `pauliCoeff A P` — Pauli coefficient (1/2ⁿ)Tr(P†A)
- `spectralDist A P` — |pauliCoeff A P|²
- `spectralEntropy A` — -Σ_P π(P) log₂ π(P)
- `quantumInfluence A` — Σ_P wt(P) · π(P)

### ZIndexEquiv.lean
- `toZIndex S` — Convert Finset to Z-type index
- `fromZIndex α` — Extract Finset from Z-type index
- `zIndexEquiv n` — Formal equivalence
- `diagonalObs_spectralEntropy_eq` — H(L_f) = H_classical(f)
- `diagonalObs_quantumInfluence_eq` — Inf(L_f) = Inf_classical(f)

### EntropyIncrease Submodules
- **KroneckerPow.lean**: `kroneckerPow n M`, `kroneckerPow_succ`, `conjugation_factors_through_kronecker`
- **TransformDefs.lean**: `transformedObs f` — T⊗ⁿ H⊗ⁿ L_f (H⊗ⁿ)† (T⊗ⁿ)†
- **BackTransform.lean**: `backTransformedIndex`, `backTransformed_pauli_diag_zero_of_Z`
- **SourceSubset.lean**: `sourceSubset`, `allTExpansionPaulis`, `tExpansionPaulis_pairwiseDisjoint`
- **PauliCoeff.lean**: `fourierCoeffSq`, `normSq_one_div_sqrt2_pow_mul`
- **SpectralDistTransform.lean**: `spectralDist_transformedObs_at_expansion`, `spectralDist_transformedObs_outside`
- **Entropy.lean**: `spectralEntropy_from_expansion`, `quantumInfluence_from_expansion`

### EntropyIncrease.lean (Main Theorems)
- `spectral_entropy_transform_thm` — H(L̃_f) = H(f) + Inf(f)
- `quantum_influence_transform_thm` — Inf(L̃_f) = Inf(f)
- `quantum_entropy_increase_theorem` — **Main theorem (complete statement)**

## Verification Status

| Module | Status | Notes |
|--------|--------|-------|
| Basic | ✅ 0 sorries | Foundational types |
| Pauli | ✅ 0 sorries | Trace properties verified |
| Bloch | ✅ 0 sorries | Expectation values verified |
| BoolFunc | ✅ 0 sorries | Character orthogonality proven |
| Gates | ✅ 0 sorries | All conjugations proven |
| TExpansion | ✅ 0 sorries | Weight preservation proven |
| DiagonalObs | ✅ 0 sorries | Pauli expansion proven |
| SpectralDist | ✅ 0 sorries | Coefficient lemmas proven |
| ZIndexEquiv | ✅ 0 sorries | Entropy equality proven |
| **PauliDiag** | ✅ 0 sorries | Split into 5 submodules |
| ├─ Single | ✅ 0 sorries | Single-qubit diagonal |
| ├─ Kronecker | ✅ 0 sorries | Kronecker diagonal |
| ├─ Trace | ✅ 0 sorries | Trace lemmas |
| ├─ Orthogonality | ✅ 0 sorries | Pauli orthogonality |
| └─ General | ✅ 0 sorries | General lemmas |
| **EntropyIncrease** | ✅ 0 sorries | **Fully verified!** |
| ├─ KroneckerPow | ✅ 0 sorries | Kronecker power |
| ├─ TransformDefs | ✅ 0 sorries | Transform definition |
| ├─ BackTransform | ✅ 0 sorries | Back-transform diagonal |
| ├─ SourceSubset | ✅ 0 sorries | T-expansion disjointness |
| ├─ PauliCoeff | ✅ 0 sorries | Coefficient formulas |
| ├─ SpectralDistTransform | ✅ 0 sorries | **All proofs complete** |
| └─ Entropy | ✅ 0 sorries | Entropy computation |

### Verification Complete

All lemmas and theorems in the Quantum Entropy Increase formalization have been fully proved.
No sorries remain. The main theorem `quantum_entropy_increase_theorem` is complete.

**Build Command:**
```bash
lake build AlethfeldLean.Quantum.EntropyIncrease
```
