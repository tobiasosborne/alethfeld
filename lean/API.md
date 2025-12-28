# Alethfeld Lean Library API Reference

This document serves as a guide for **Prover** and **Formalizer** agents using the Alethfeld Lean 4 library. It details the module structure, key definitions, main theorems, and usage patterns.

## 1. Project Overview & Status

*   **Package Name**: `AlethfeldLean`
*   **Dependency**: `mathlib` (v4.26.0)
*   **Verification Status**: **COMPLETE** (As of Dec 2025)
    *   L1 (Fourier): ✅ 0 sorries
    *   L2 (Influence): ✅ 0 sorries
    *   L3 (Entropy): ✅ 0 sorries
    *   ShannonMax: ✅ Verified (0 sorries)
    *   L4Maximum: ✅ Verified (0 sorries)
*   **Build Command**:
    ```bash
    lake build
    ```

## 2. Module Hierarchy

The library is organized under the `AlethfeldLean` namespace.

*   **`AlethfeldLean`** (Root)
    *   **`Quantum`** (Core definitions)
        *   `Basic`: Fundamental types (`Mat2`, `QubitMat`) and index tools.
        *   `Pauli`: Pauli matrices, strings, and trace properties.
        *   `Bloch`: Bloch sphere representations and expectation values.
    *   **`QBF`** (Quantum Boolean Functions)
        *   `Rank1`
            *   `L1Fourier`: Fourier analysis of rank-1 product state QBFs (Lemma L1).
            *   `L2Influence`: Influence independence theorem (Lemma L2).
            *   `L3Entropy`: General entropy formula (Lemma L3).
            *   `ShannonMax`: Maximum entropy for 3-outcome distributions.
            *   `L4Maximum`: Maximum entropy-influence ratio at magic state (Lemma L4).

## 3. Key Types and Definitions

### Basic Types (`AlethfeldLean.Quantum.Basic`)

| Type | Definition | Description |
| :--- | :--- | :--- |
| `Mat2` | `Matrix (Fin 2) (Fin 2) ℂ` | 2x2 complex matrix (single-qubit operator). |
| `QubitMat n` | `Matrix (Fin (2^n)) (Fin (2^n)) ℂ` | $2^n \times 2^n$ matrix ($n$-qubit operator). |
| `MultiIndex n` | `Fin n → Fin 4` | Vector of Pauli indices $\alpha \in \{0,1,2,3\}^n$. |
| `multiIndexDelta α` | `if α = 0 then 1 else 0` | Kronecker delta $\delta_{\alpha, 0}$. |

### Pauli Operators (`AlethfeldLean.Quantum.Pauli`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `σ j` | `Fin 4 → Mat2` | Pauli matrices: $I, X, Y, Z$ for $j=0,1,2,3$. |
| `pauliString α` | `MultiIndex n → QubitMat n` | Tensor product $\sigma^{\alpha_1} \otimes \dots \otimes \sigma^{\alpha_n}$. |

### Bloch Sphere (`AlethfeldLean.Quantum.Bloch`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `BlochVector` | `Structure {x, y, z : ℝ}` | Normalized vector ($x^2+y^2+z^2=1$). |
| `BlochVector.r` | `Fin 4 → ℝ` | Extended components: $r^{(0)}=1, r^{(1)}=x, \dots$ |
| `blochState θ φ` | `ℝ → ℝ → QubitState` | State vector $\cos(\theta/2)|0\rangle + e^{i\phi}\sin(\theta/2)|1\rangle$. |
| `blochProduct` | `(Fin n → BlochVector) → MultiIndex n → ℝ` | Product $\prod_k r_k^{(\alpha_k)}$. |

### QBF Structures (`AlethfeldLean.QBF.Rank1.L1Fourier`)

| Symbol | Description |
| :--- | :--- |
| `ProductState n` | Structure holding angles `θ` and `φ` for $n$ qubits. |
| `fourierCoeff U α` | $\hat{U}(\alpha) = 2^{-n} \text{Tr}(\sigma^\alpha U)$. |

### Influence (`AlethfeldLean.QBF.Rank1.L2Influence`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `qProduct bloch α` | $\prod_k q_k^{(\alpha_k)}$ | Product of squared Bloch components. |
| `probability bloch α` | $2^{2-2n} \cdot \text{qProduct}$ | Fourier weight for multi-index $\alpha$. |
| `influence_j bloch j` | $\sum_{\alpha: \alpha_j \neq 0} p_\alpha$ | Influence of qubit $j$. |
| `totalInfluence bloch` | $\sum_j I_j$ | Total influence. |
| `partialSum bloch j ℓ` | $\sum_{\alpha: \alpha_j = \ell} p_\alpha$ | Partial sum for fixed $\alpha_j = \ell$. |

### Entropy (`AlethfeldLean.QBF.Rank1.L3Entropy`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `log2 x` | $\ln(x) / \ln(2)$ | Binary logarithm. |
| `entropyTerm p` | $-p \log_2 p$ (or 0 if $p=0$) | Shannon entropy term. |
| `blochEntropy v` | $H(x^2, y^2, z^2)$ | Entropy of Bloch vector components. |
| `p_zero n` | $(1 - 2^{1-n})^2$ | Fourier weight of zero index. |
| `fourierWeight bloch α` | `probability bloch α` | Alias for Fourier weight. |
| `totalEntropy bloch` | $\sum_\alpha -p_\alpha \log_2 p_\alpha$ | Total Shannon entropy $S(U)$. |
| `totalBlochEntropy bloch` | $\sum_k f_k$ | Sum of Bloch entropies over all qubits. |

### Shannon Maximum (`AlethfeldLean.QBF.Rank1.ShannonMax`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `ProbDist3` | `Structure {p : Fin 3 → ℝ}` | Probability distribution on 3 outcomes. |
| `uniformDist` | `(1/3, 1/3, 1/3)` | Uniform distribution on 3 outcomes. |
| `shannonEntropy p` | $-\sum p_i \log_2 p_i$ | Shannon entropy with $0 \log 0 = 0$ convention. |
| `klDivergence p q` | $\sum p_i \ln(p_i/q_i)$ | Kullback-Leibler divergence. |

### L4 Maximum (`AlethfeldLean.QBF.Rank1.L4Maximum`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `isMagicState v` | `v.q 1 = 1/3 ∧ v.q 2 = 1/3 ∧ v.q 3 = 1/3` | Predicate for magic state. |
| `magicBlochVector` | $(1/\sqrt{3}, 1/\sqrt{3}, 1/\sqrt{3})$ | The magic Bloch vector. |
| `magicProductState` | `fun _ => magicBlochVector` | Product state with all qubits magic. |
| `blochToProbDist3 v` | `{p := fun i => v.q (i+1)}` | Convert Bloch vector to ProbDist3. |

## 4. Main Theorems

These are the primary verified results available for use in higher-level proofs.

### Trace Properties (`AlethfeldLean.Quantum.Pauli`)

*   **`trace_pauliString {n} (α)`**:
    $$\text{Tr}(\sigma^\alpha) = \begin{cases} 2^n & \text{if } \alpha = 0 \\ 0 & \text{otherwise} \end{cases}$$ 
    *Usage*: Simplifying traces of Pauli strings.

### Expectation Values (`AlethfeldLean.Quantum.Bloch`)

*   **`expectation_σ (θ φ) (j)`**:
    $$\langle \psi | \sigma_j | \psi \rangle = r^{(j)}$$ 
    *Usage*: Converting quantum expectations to algebraic Bloch components.

### Fourier Analysis (`AlethfeldLean.QBF.Rank1.L1Fourier`)

*   **`fourier_coefficient_formula (ψ : ProductState n) (α)`** (Lemma L1):
    For $U = I - 2|\psi\rangle\langle\psi|$:
    $$\hat{U}(\alpha) = \delta_{\alpha,0} - 2^{1-n} \prod_{k=0}^{n-1} r_k^{(\alpha_k)}$$ 
    *Usage*: Closed-form expression for Fourier coefficients of rank-1 QBFs.

### Influence Independence (`AlethfeldLean.QBF.Rank1.L2Influence`)

*   **`influence_j_formula (bloch) (j)`** (Lemma L2a):
    $$I_j = 2^{1-n}$$ 
    *Usage*: Single-qubit influence is constant, independent of Bloch vector.

*   **`total_influence_formula (bloch)`** (Lemma L2b):
    $$I(U) = n \cdot 2^{1-n}$$ 
    *Usage*: Total influence depends only on number of qubits.

*   **`influence_independent_of_bloch (bloch₁ bloch₂)`**:
    $$I(\text{bloch}_1) = I(\text{bloch}_2)$$ 
    *Usage*: Influence is universal across all product states.

*   **`influence_decreasing (bloch) (hn : n ≥ 1)`**:
    $$I(U) \leq 1$$ 
    *Usage*: Influence bound for rank-1 QBFs.

### Entropy Formula (`AlethfeldLean.QBF.Rank1.L3Entropy`)

*   **`sum_fourier_weights (bloch)`** (Parseval):
    $$\sum_{\alpha \neq 0} p_\alpha = 1 - p_0$$ 
    *Usage*: Probability normalization (Fourier weights sum to 1).

*   **`first_sum_formula (bloch)`**:
    $$\sum_{\alpha \neq 0} p_\alpha (2n-2) = (2n-2)(1-p_0)$$ 
    *Usage*: First sum in entropy decomposition.

*   **`qubit_log_contribution (bloch) (j)`**:
    $$-\sum_{\alpha: \alpha_j \neq 0} p_\alpha \log_2 q_j^{(\alpha_j)} = 2^{1-n} f_j$$ 
    *Usage*: Log contribution from qubit $j$ equals scaled Bloch entropy.

*   **`entropy_sum_factorization (bloch)`**:
    $$\sum_j \text{(log contributions from } j\text{)} = 2^{1-n} \sum_k f_k$$ 
    *Usage*: Sum over qubits factors out the power of 2.

*   **`entropy_formula (bloch)`** (Lemma L3 - Main Theorem):
    $$S(U) = -p_0 \log_2 p_0 + (2n-2)(1-p_0) + 2^{1-n} \sum_k f_k$$ 
    where $f_k = H(x_k^2, y_k^2, z_k^2)$ is the Bloch entropy.
    *Usage*: **Main result** - closed-form entropy for rank-1 product state QBFs.

*   **`entropy_nonneg (bloch) (hn : n ≥ 1)`**:
    $$S(U) \geq 0$$
    *Usage*: Proof that entropy is always non-negative for these systems.

### Shannon Maximum Entropy (`AlethfeldLean.QBF.Rank1.ShannonMax`)

*   **`shannon_maximum_entropy_full`**:
    Combined theorem: $H(p) \geq 0$, $H(p) \leq \log_2 3$, and $H(p) = \log_2 3$ iff $p = \text{uniform}$.
    *Usage*: Fundamental maximality property of the uniform distribution.

*   **`entropy_le_log2_three (p)`**:
    $$H(p) \leq \log_2 3$$
    *Usage*: Proof that $\log_2 3$ is the universal upper bound for 3 outcomes.

*   **`entropy_eq_max_iff_uniform (p)`**:
    $$H(p) = \log_2 3 \iff p = (1/3, 1/3, 1/3)$$
    *Usage*: Unique maximizer characterization.

### L4 Maximum at Magic State (`AlethfeldLean.QBF.Rank1.L4Maximum`)

*   **`blochEntropy_le_log2_three (v)`**:
    $$f(v) = H(x^2, y^2, z^2) \leq \log_2 3$$
    *Usage*: Bloch entropy is bounded by $\log_2 3$ for any Bloch vector.

*   **`blochEntropy_eq_max_iff_magic (v) (hq)`** (Lemma L4 - Equality):
    $$f(v) = \log_2 3 \iff (x^2, y^2, z^2) = (1/3, 1/3, 1/3)$$
    *Usage*: Equality holds iff $v$ is in the magic state.

*   **`blochEntropy_magic`**:
    $$f(\text{magicBlochVector}) = \log_2 3$$
    *Usage*: The magic Bloch vector achieves maximum Bloch entropy.

*   **`totalBlochEntropy_le_magic (bloch) (hq)`**:
    $$\sum_k f_k \leq n \cdot \log_2 3$$
    *Usage*: Total Bloch entropy is maximized by the magic product state.

*   **`totalBlochEntropy_eq_max_iff (bloch) (hq)`**:
    $$\sum_k f_k = n \cdot \log_2 3 \iff \forall k, \text{isMagicState}(\text{bloch}_k)$$
    *Usage*: Equality holds iff all qubits are in the magic state.

*   **`l4_maximum_entropy (v) (hq)`** (Lemma L4 - Main Theorem):
    Combined bound and equality: $f(v) \leq \log_2 3$ with equality iff magic state.
    *Usage*: **Main result** - Bloch entropy is uniquely maximized at the magic state.

*   **`l4_maximum_total_entropy (bloch) (hq)`** (Lemma L4 - Corollary):
    Total entropy bound: $\sum_k f_k \leq n \cdot \log_2 3$ with equality iff all magic.
    *Usage*: Product state version of the maximum entropy result.

## 5. Agent Guidelines

### For the **Prover** Agent

*   **Referencing**: When proposing steps, explicitly cite these results.
    *   *Example*: "By `trace_pauliString` from `AlethfeldLean.Quantum.Pauli`, the trace vanishes for $\alpha \neq 0$."
*   **Structure**: Treat `AlethfeldLean.Quantum` as the axiomatic base. Do not try to re-prove properties of Pauli matrices; assume them.
*   **Abstraction**: Work with `MultiIndex` and `BlochVector` rather than raw matrices whenever possible.

### For the **Formalizer** Agent

*   **Imports**: Always start files with:
    ```lean
    import AlethfeldLean.Quantum.Basic
    import AlethfeldLean.Quantum.Pauli
    import AlethfeldLean.Quantum.Bloch
    -- Add QBF modules as needed
    ```
*   **Namespaces**: Use `open` to make definitions accessible:
    ```lean
    open Complex Real
    open Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch
    ```
*   **Mathlib Usage**: You have full access to `Mathlib`. Frequently used lemmas include:
    *   **Complex**: `Complex.normSq_eq_conj_mul_self`, `Complex.exp_mul_I`, `Complex.conj_ofReal`
    *   **Trig**: `Real.cos_sq_add_sin_sq`, `Real.sin_two_mul`, `Real.cos_two_mul'`
    *   **Matrix**: `Matrix.trace_kronecker`
    *   **Algebra**: `zpow_add₀`, `zpow_neg`

## 6. Example Usage

```lean
import AlethfeldLean.Quantum.Bloch
import AlethfeldLean.Quantum.Pauli

open Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch

-- Example: Proving expectation of X is the x-component of Bloch vector
example (θ φ : ℝ) :
  let ψ := blochState θ φ
  expectation ψ σX = (blochVectorOfAngles θ φ).x := by
  -- This is exactly theorem expectation_σX, already proven in library
  exact expectation_σX θ φ
```