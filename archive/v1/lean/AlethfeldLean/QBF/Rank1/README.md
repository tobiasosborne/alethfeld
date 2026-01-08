# AlethfeldLean QBF Rank-1 Module

## Overview

This module provides Lean 4 formalization of Lemma L1: the Fourier coefficient formula for rank-1 product state Quantum Boolean Functions (QBFs).

**Verification Status:** COMPLETE - All proofs verified, zero sorries.

## Mathematical Content

### The Main Result (Lemma L1)

For a rank-1 product state QBF defined by:
```
U = I - 2|ψ⟩⟨ψ|
```
where `|ψ⟩ = ⊗_k |φ_k⟩` is an n-qubit product state, the Fourier coefficient at multi-index α is:

```
Û(α) = δ_{α,0} - 2^{1-n} ∏_k r_k^{α_k}
```

where:
- `δ_{α,0}` is 1 if α is the zero multi-index, 0 otherwise
- `r_k = (1, x_k, y_k, z_k)` is the extended Bloch vector for qubit k
- `α_k ∈ {0,1,2,3}` indexes the Pauli basis {I, X, Y, Z}

### Key Components

1. **Fourier Coefficient Definition**
   ```
   Û(α) = 2^{-n} Tr(σ^α U)
   ```
   where `σ^α = σ^{α_1} ⊗ ... ⊗ σ^{α_n}` is the Pauli string.

2. **Trace of Pauli Strings**
   ```
   Tr(σ^α) = 2^n δ_{α,0}
   ```

3. **Bloch Sphere Representation**
   Each single-qubit state `|φ_k⟩` is parametrized by angles (θ_k, φ_k):
   ```
   |φ_k⟩ = cos(θ_k/2)|0⟩ + e^{iφ_k}sin(θ_k/2)|1⟩
   ```
   with Bloch vector `(sin θ_k cos φ_k, sin θ_k sin φ_k, cos θ_k)`.

4. **Expectation Values**
   ```
   ⟨φ|σ_I|φ⟩ = 1
   ⟨φ|σ_X|φ⟩ = sin θ cos φ
   ⟨φ|σ_Y|φ⟩ = sin θ sin φ
   ⟨φ|σ_Z|φ⟩ = cos θ
   ```

## File Structure

### L1Fourier.lean

The main theorem file containing:

| Definition/Theorem | Description |
|-------------------|-------------|
| `ProductState` | Structure for n-qubit product state (angles θ, φ for each qubit) |
| `fourierCoeff` | Definition of Fourier coefficient `2^{-n} Tr(σ^α U)` |
| `fourierCoeff_rank1_expand` | Linearity: `2^{-n}(Tr - 2·proj) = 2^{-n}Tr - 2^{1-n}·proj` |
| `term1_simplify` | Normalization: `2^{-n} Tr(σ^α) = δ_{α,0}` |
| `single_qubit_factor` | Each factor equals Bloch component |
| `fourierCoeff_formula` | Main formula definition |
| `fourier_coefficient_formula` | Main theorem (L1) |
| `fourier_coeff_zero` | Corollary: `Û(0) = 1 - 2^{1-n}` |
| `fourier_coeff_nonzero` | Corollary: `Û(α) = -2^{1-n} ∏_k r_k^{α_k}` for α ≠ 0 |

## Dependencies

This module depends on:

### Internal Dependencies
- `AlethfeldLean.Quantum.Basic` - Basic quantum types (`Mat2`, `QubitMat`, `MultiIndex`)
- `AlethfeldLean.Quantum.Pauli` - Pauli matrices and `pauliString` tensor products
- `AlethfeldLean.Quantum.Bloch` - Bloch sphere representation and expectation values

### Mathlib Dependencies
- `Mathlib.Algebra.BigOperators.Finprod` - Finite products
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` - Trigonometric identities
- `Mathlib.Data.Complex.Exponential` - Complex exponentials

## Key Mathlib Lemmas Used

### Complex Numbers
- `Complex.exp_mul_I` : `exp(x·I) = cos(x) + sin(x)·I`
- `Complex.normSq_eq_conj_mul_self` : `|z|² = conj(z)·z`
- `Complex.norm_exp_ofReal_mul_I` : `‖exp(r·I)‖ = 1`

### Trigonometry
- `Real.cos_sq_add_sin_sq` : `cos²(x) + sin²(x) = 1`
- `Real.cos_two_mul'` : `cos(2x) = cos²(x) - sin²(x)`
- `Real.sin_two_mul` : `sin(2x) = 2·sin(x)·cos(x)`

### Integer Powers
- `zpow_add₀` : `a^(m+n) = a^m · a^n` (for a ≠ 0)
- `zpow_natCast` : `a^(↑n : ℤ) = a^n`

## Proof Techniques

### 1. Zpow Algebra (L1Fourier.lean)

The key algebraic manipulation showing `2^{-n} · 2 = 2^{1-n}`:
```lean
have : (2 : ℂ)^(-(n : ℤ) + 1) = (2 : ℂ)^(-(n : ℤ)) * (2 : ℂ)^(1 : ℤ) := zpow_add₀ h2ne _ _
```

### 2. Complex Exponential Conjugation (Bloch.lean)

Helper lemmas for Bloch sphere calculations:
- `exp_mul_conj_exp_eq_one` : `exp(iφ) · conj(exp(iφ)) = 1`
- `exp_add_exp_conj` : `exp(iφ) + conj(exp(iφ)) = 2cos(φ)`
- `exp_conj_sub_exp` : `conj(exp(iφ)) - exp(iφ) = -2i·sin(φ)`

### 3. Calc Blocks

Structured proofs using Lean's `calc` syntax for readable step-by-step derivations.

## Building

```bash
cd /path/to/alethfeld/lean
lake build AlethfeldLean.QBF.Rank1.L1Fourier
```

## Verification

```bash
# Check for any remaining sorries
lake build 2>&1 | grep -c "declaration uses 'sorry'"
# Expected output: 0
```

## Related Work

This formalization is part of the Alethfeld proof verification system, which uses:
- Semantic graphs for proof representation
- Subagent-based proof development (Prover, Verifier, etc.)
- Automatic Lean 4 skeleton generation

## Authors

- Alethfeld Proof Orchestrator
- Claude Code (formalization assistance)

## Date

Completed: 2025-12-28
