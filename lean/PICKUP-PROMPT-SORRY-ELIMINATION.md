# Pickup Prompt: AlethfeldLean Formalization

## Current Status

| Layer | File | Status |
|-------|------|--------|
| L1 | L1Fourier.lean | ✅ COMPLETE (0 sorries) |
| L2 | L2Influence.lean | ✅ COMPLETE (0 sorries) |
| L3 | L3Entropy.lean | ✅ COMPLETE (0 sorries) |

**Last Updated:** 2025-12-28

## Project Location

```
/home/tobiasosborne/Projects/alethfeld/lean/
```

## Build Command

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
lake build
```

## Issue Tracking

This project uses **beads** for issue tracking:

```bash
bd ready              # Find available work
bd list --status=open # All open issues
bd show <id>          # View issue details
```

---

## L3 Entropy Formula — IN PROGRESS

**Goal:** Prove the General Entropy Formula for Rank-1 Product State QBFs:
$$S = -p_0 \log_2 p_0 + (2n-2)(1-p_0) + 2^{1-n} \sum_k f_k$$

where $f_k = H(x_k^2, y_k^2, z_k^2)$ is the Bloch entropy.

### File: `AlethfeldLean/QBF/Rank1/L3Entropy.lean`

### Completed (10 issues closed)

1. **Skeleton created** (`alethfeld-013`)
   - Imports from L2Influence
   - Namespace `Alethfeld.QBF.Rank1.L3Entropy`

2. **Shannon entropy definitions** (`alethfeld-9bm`)
   - `log2` - binary logarithm
   - `log2_zpow`, `log2_two`, `log2_one`, `log2_mul`, `log2_prod` - helper lemmas
   - `entropyTerm` - Shannon entropy term with 0·log(0)=0 convention
   - `blochEntropy` - entropy of Bloch vector components

3. **Probability definitions** (`alethfeld-ban`)
   - `p_zero n` = (1 - 2^{1-n})²
   - `fourierWeight` - alias to L2's probability function
   - `totalEntropy` - total Shannon entropy S(U)

4. **L3-step1: Log decomposition** (`alethfeld-uho`)
   - `fourierWeight_nonneg`, `qProduct_pos`, `fourierWeight_pos_of_qProduct_pos`
   - `log2_fourierWeight` - logarithm decomposition
   - `log_decomposition` - main result: -p_α log₂ p_α = p_α(2n-2) - p_α Σ_k log₂ q_k^{α_k}

5. **L3-step2: First sum formula** (`alethfeld-x4n`)
   - `first_sum_formula` - Σ_{α≠0} p_α(2n-2) = (2n-2)(1-p₀)

6. **L3-step3: Zero case helpers** (`alethfeld-yy4`)
   - `BlochVector.q_zero_eq_one` - q^{(0)} = 1
   - `log2_q_zero` - log₂(q^{(0)}) = 0
   - `log2_q_of_alpha_zero` - log₂(q^{α}) = 0 when α = 0
   - `sum_log2_q_eq_sum_nonzero` - sum only over non-zero α_k contributions

7. **L3-step5: Qubit log contribution** (`alethfeld-680`)
   - `sum_prob_fixed_j`, `log_contribution_fixed_ell` - helper lemmas
   - `sum_log_contributions`, `blochEntropy_eq_sum` - entropy helpers
   - `sum_partition_by_j` - partitioning by qubit index
   - `qubit_log_contribution` - main result: -Σ_{α: α_j≠0} p_α log₂ q_j^{α_j} = 2^{1-n} f_j

8. **L3-step6: Entropy sum factorization** (`alethfeld-esk`)
   - `totalBlochEntropy` - sum of Bloch entropies over all qubits
   - `entropy_sum_factorization` - sum of qubit contributions = 2^{1-n} * totalBlochEntropy

9. **L3-qed: Main entropy formula** (`alethfeld-7j9`)
   - `entropyTerm_pos`, `entropy_sum_decomposition` - helper lemmas
   - `entropy_formula` - **MAIN THEOREM**: S(U) = entropyTerm(p₀) + (2n-2)(1-p₀) + 2^{1-n} Σₖ fₖ

10. **sum_fourier_weights (Parseval)** (`alethfeld-5zy`)
    - `zeroMultiIndex`, `qProduct_zero`, `fourierWeight_zero` - zero index helpers
    - `sum_qProduct` - Fubini theorem: Σ_α ∏_k q_k^{α_k} = 2^n
    - `sum_all_fourier_weights` - total sum = 2^{2-n}
    - `multiIndex_eq_zero_iff`, `not_exists_ne_zero_iff` - zero characterization
    - `one_minus_p_zero` - algebraic identity
    - `sum_fourier_weights` - **FINAL LEMMA**: Σ_{α≠0} p_α = 1 - p₀

### Remaining Work (1 issue open)

| Issue ID | Title | Status |
|----------|-------|--------|
| `alethfeld-xi1` | entropy_nonneg corollary | Ready (optional) |

### ✅ L3 VERIFICATION COMPLETE

All sorries eliminated! The L3 entropy formula is fully verified:

```
lake build 2>&1 | grep -c "declaration uses 'sorry'"
0
```

---

## L2 Influence Independence — COMPLETE

**File:** `AlethfeldLean/QBF/Rank1/L2Influence.lean`

**Main Result:** For any rank-1 product state QBF on n qubits:
$$I(U) = n \cdot 2^{1-n}$$

This is INDEPENDENT of the choice of Bloch vectors.

### Key Theorems Proven

- `influence_j_formula`: I_j = 2^{1-n}
- `total_influence_formula`: I(U) = n * 2^{1-n}
- `influence_independent_of_bloch`: I(bloch₁) = I(bloch₂)
- `influence_decreasing`: I(U) ≤ 1 for n ≥ 1

### Helper Lemmas Used in L3

- `probability bloch α` - Fourier weight 2^{2-2n} ∏_k q_k^{α_k}
- `qProduct bloch α` - Product of squared Bloch components
- `BlochVector.q m` - Extended Bloch components (q^{(0)}=1, q^{(1)}=x², etc.)
- `BlochVector.q_nonneg` - q values are non-negative
- `BlochVector.q_sum_eq_two` - q^{(0)} + q^{(1)} + q^{(2)} + q^{(3)} = 2

---

## L1 Fourier Formula — COMPLETE

**File:** `AlethfeldLean/QBF/Rank1/L1Fourier.lean`

**Main Result:** For U = I - 2|ψ⟩⟨ψ| where |ψ⟩ is a product state:
$$\hat{U}(\alpha) = \delta_{\alpha,0} - 2^{1-n} \prod_k r_k^{\alpha_k}$$

---

## Key Mathlib Lemmas for L3

### Logarithms
- `Real.log_prod` : log(∏ f) = Σ log(f) for positive f
- `Real.log_zpow` : log(a^k) = k * log(a)
- `Real.log_mul` : log(xy) = log(x) + log(y)
- `Real.log_one` : log(1) = 0
- `Real.log_pos` : 1 < x → 0 < log(x)

### Zpow (Integer Powers)
- `zpow_add₀` : a^(m+n) = a^m * a^n (for a ≠ 0)
- `zpow_pos` : 0 < a → 0 < a^k

### Sums/Products
- `Finset.sum_div` : (Σ f) / c = Σ (f / c)
- `Finset.prod_pos` : (∀ x, 0 < f x) → 0 < ∏ f
- `Finset.prod_nonneg` : (∀ x, 0 ≤ f x) → 0 ≤ ∏ f

---

## Verification

```bash
# Check for sorries
lake build 2>&1 | grep "declaration uses 'sorry'"
# Expected: 1 sorry in L3Entropy.lean (sum_fourier_weights)

# Full build
lake build
# Build completed successfully (2070 jobs).
```
