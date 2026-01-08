# L2 Lean Implementation Plan

## Overview

**Lemma L2: Influence Independence**

For any rank-1 product state QBF on $n$ qubits:
$$I(U) = n \cdot 2^{1-n}$$

This is independent of the choice of Bloch vectors.

## Dependencies

- `AlethfeldLean.Quantum.Bloch` (BlochVector, blochProduct)
- `AlethfeldLean.Quantum.Pauli` (σ matrices, trace properties)
- `AlethfeldLean.QBF.Rank1.L1Fourier` (fourierCoeff_formula)

## Implementation Steps

### Phase 1: Extend Bloch Infrastructure

**Issue L2-01: Define squared Bloch components (q^(m))**

File: `AlethfeldLean/Quantum/Bloch.lean` (extend existing)

```lean
/-- Squared Bloch components: q^(0)=1, q^(1)=x², q^(2)=y², q^(3)=z² -/
def BlochVector.q (v : BlochVector) : Fin 4 → ℝ
  | 0 => 1
  | 1 => v.x^2
  | 2 => v.y^2
  | 3 => v.z^2
```

**Issue L2-02: Prove q-sum equals 2**

Key theorem for L2: the sum of all q components equals 2.

```lean
theorem BlochVector.q_sum_eq_two (v : BlochVector) :
    (v.q 0) + (v.q 1) + (v.q 2) + (v.q 3) = 2
```

Proof uses: q^(0)=1 and x²+y²+z²=1 (from BlochVector.norm_sq)

**Issue L2-03: Prove q-sum over {1,2,3} equals 1**

```lean
theorem BlochVector.q_nonzero_sum_eq_one (v : BlochVector) :
    (v.q 1) + (v.q 2) + (v.q 3) = 1
```

This is the core identity for proving I_j = 2^(1-n).

### Phase 2: Define Influence Infrastructure

**Issue L2-04: Create L2Influence.lean module**

Create new file: `AlethfeldLean/QBF/Rank1/L2Influence.lean`

Module structure:
- Imports L1Fourier and Bloch
- Opens appropriate namespaces
- Defines influence types

**Issue L2-05: Define probability p_α from L1 corollary**

```lean
/-- Probability for multi-index α ≠ 0: p_α = 2^{2-2n} ∏_k q_k^{α_k} -/
noncomputable def probability {n : ℕ} (bloch : Fin n → BlochVector) (α : MultiIndex n) : ℝ :=
  (2 : ℝ)^(2 - 2*n) * ∏ k, (bloch k).q (α k)
```

**Issue L2-06: Define single-qubit influence I_j**

```lean
/-- Influence of qubit j: sum over α with α_j ≠ 0 -/
noncomputable def influence_j {n : ℕ} (bloch : Fin n → BlochVector) (j : Fin n) : ℝ :=
  ∑ α : MultiIndex n, if α j ≠ 0 then probability bloch α else 0
```

**Issue L2-07: Define total influence I**

```lean
/-- Total influence: sum over all qubits -/
noncomputable def totalInfluence {n : ℕ} (bloch : Fin n → BlochVector) : ℝ :=
  ∑ j, influence_j bloch j
```

### Phase 3: Core Proof Steps

**Issue L2-08: Prove factorization lemma**

When α_j = ℓ is fixed, the product factors:

```lean
theorem probability_factorization {n : ℕ} (bloch : Fin n → BlochVector)
    (j : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    ∑ α : {α : MultiIndex n // α j = ℓ}, probability bloch α
    = (2 : ℝ)^(2 - 2*n) * (bloch j).q ℓ * ∏ k : {k // k ≠ j}, ∑ m : Fin 4, (bloch k).q m
```

**Issue L2-09: Apply q-sum simplification**

Using L2-02 (q_sum_eq_two):

```lean
theorem partial_sum_simplify {n : ℕ} (bloch : Fin n → BlochVector) (j : Fin n) (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    ∑ α : {α : MultiIndex n // α j = ℓ}, probability bloch α
    = (2 : ℝ)^(1 - n) * (bloch j).q ℓ
```

**Issue L2-10: Prove single-qubit influence formula**

```lean
theorem influence_j_formula {n : ℕ} (bloch : Fin n → BlochVector) (j : Fin n) :
    influence_j bloch j = (2 : ℝ)^(1 - n)
```

Uses: L2-09 and L2-03 (q_nonzero_sum_eq_one)

### Phase 4: Main Theorem

**Issue L2-11: Prove total influence theorem (L2)**

```lean
/-- Main theorem L2: Total influence is n * 2^{1-n} -/
theorem total_influence_formula {n : ℕ} (bloch : Fin n → BlochVector) :
    totalInfluence bloch = n * (2 : ℝ)^(1 - n)
```

**Issue L2-12: Prove universality corollary**

The influence is independent of Bloch vectors:

```lean
theorem influence_independent_of_bloch {n : ℕ} (bloch₁ bloch₂ : Fin n → BlochVector) :
    totalInfluence bloch₁ = totalInfluence bloch₂
```

### Phase 5: Integration and Testing

**Issue L2-13: Add L2Influence to module exports**

Update `AlethfeldLean.lean` to include the new module.

**Issue L2-14: Update API.md documentation**

Add L2 theorems to the API reference.

**Issue L2-15: Create test file for L2**

Create `test_l2_influence.lean` with concrete examples.

## Execution Order

1. L2-01 → L2-02 → L2-03 (Bloch extensions)
2. L2-04 (create module)
3. L2-05 → L2-06 → L2-07 (definitions)
4. L2-08 → L2-09 → L2-10 (core proofs)
5. L2-11 → L2-12 (main theorem)
6. L2-13 → L2-14 → L2-15 (integration)

## Notes

- Similar structure to L1Fourier.lean
- May need intermediate lemmas for sum manipulation
- Finite sums over MultiIndex may require Fintype instances
- Consider using `sorry` for complex steps initially, then fill in
