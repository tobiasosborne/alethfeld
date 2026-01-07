# Quantum Module Manifest

**Package:** `AlethfeldLean.Quantum`
**Last Updated:** 2026-01-07

## Module Overview

This directory contains the quantum computing foundations for the Alethfeld project, including Pauli matrices, quantum gates, and the Quantum Entropy Increase Theorem.

## File Listing

| File | Lines | Namespace | Description |
|------|-------|-----------|-------------|
| `Basic.lean` | ~120 | `Alethfeld.Quantum.Basic` | Core types: `Mat2`, `QubitMat`, `MultiIndex`, index equivalences |
| `Pauli.lean` | ~150 | `Alethfeld.Quantum.Pauli` | Pauli matrices σI, σX, σY, σZ, `pauliString`, trace properties |
| `Bloch.lean` | ~180 | `Alethfeld.Quantum.Bloch` | Bloch sphere, `BlochVector`, expectation values |
| `BoolFunc.lean` | 260 | `Alethfeld.Quantum.BoolFunc` | Boolean functions, Fourier analysis, character orthogonality |
| `PauliDiag.lean` | 227 | `Alethfeld.Quantum.PauliDiag` | Pauli diagonal properties, `pauliString_diag` lemmas |
| `Gates.lean` | 212 | `Alethfeld.Quantum.Gates` | Hadamard/T gate definitions, conjugation theorems |
| `TExpansion.lean` | 104 | `Alethfeld.Quantum.TExpansion` | T expansion, `pauliWeight`, Shannon entropy |
| `DiagonalObs.lean` | 146 | `Alethfeld.Quantum.DiagonalObs` | `diagonalObs`, `pauliZ_S`, Pauli expansion theorem |
| `SpectralDist.lean` | 170 | `Alethfeld.Quantum.SpectralDist` | `pauliCoeff`, `spectralDist`, `spectralEntropy` |
| `ZIndexEquiv.lean` | 232 | `Alethfeld.Quantum.ZIndexEquiv` | Z-index bijection, entropy/influence equality |
| `EntropyIncrease.lean` | 203 | `Alethfeld.Quantum.EntropyIncrease` | Main theorem, `transformedObs`, axioms |

**Total:** ~2004 lines across 11 modules

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
   │             ├── PauliDiag.lean ────────┐
   │             │                          │
   │             ├── Gates.lean             │
   │             │                          │
   │             └── TExpansion.lean        │
   │                                        │
   ├── BoolFunc.lean ──────────────────────┼──→ DiagonalObs.lean
                                           │           │
                                           │    SpectralDist.lean
                                           │           │
                                           │    ZIndexEquiv.lean
                                           │           │
                                           └───────────┴──→ EntropyIncrease.lean
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

### EntropyIncrease.lean
- `kroneckerPow n M` — M⊗ⁿ Kronecker power
- `transformedObs f` — T⊗ⁿ H⊗ⁿ L_f (H⊗ⁿ)† (T⊗ⁿ)†
- `spectral_entropy_transform_axiom` — H(L̃_f) = H(f) + Inf(f) [AXIOM]
- `quantum_influence_transform_axiom` — Inf(L̃_f) = Inf(f) [AXIOM]
- `quantum_entropy_increase_theorem` — **Main theorem**

## Verification Status

| Module | Status | Notes |
|--------|--------|-------|
| Basic | ✅ 0 sorries | Foundational types |
| Pauli | ✅ 0 sorries | Trace properties verified |
| Bloch | ✅ 0 sorries | Expectation values verified |
| BoolFunc | ✅ 0 sorries | Character orthogonality proven |
| PauliDiag | ✅ 0 sorries | Diagonal lemmas proven |
| Gates | ✅ 0 sorries | All conjugations proven |
| TExpansion | ✅ 0 sorries | Weight preservation proven |
| DiagonalObs | ✅ 0 sorries | Pauli expansion proven |
| SpectralDist | ✅ 0 sorries | Coefficient lemmas proven |
| ZIndexEquiv | ✅ 0 sorries | Entropy equality proven |
| EntropyIncrease | ⚠️ 2 axioms | Transform axioms remain |

**Build Command:**
```bash
lake build AlethfeldLean.Quantum.EntropyIncrease
```
