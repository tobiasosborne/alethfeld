# Alethfeld Lean Library API Reference

This document serves as a guide for **Prover** and **Formalizer** agents using the Alethfeld Lean 4 library. It details the module structure, key definitions, main theorems, and usage patterns.

## 1. Module Hierarchy

The library is organized under the `AlethfeldLean` namespace.

*   **`AlethfeldLean`** (Root)
    *   **`Quantum`** (Core definitions)
        *   `Basic`: Fundamental types (`Mat2`, `QubitMat`) and index tools.
        *   `Pauli`: Pauli matrices, strings, and trace properties.
        *   `Bloch`: Bloch sphere representations, expectation values, and squared components.
    *   **`QBF`** (Quantum Boolean Functions)
        *   `Rank1`
            *   `L1Fourier`: Fourier analysis of rank-1 product state QBFs (Lemma L1).
            *   `L2Influence`: Influence independence for rank-1 product state QBFs (Lemma L2).

## 2. Key Types and Definitions

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

### Squared Bloch Components (`AlethfeldLean.Quantum.Bloch`)

| Symbol | Definition | Description |
| :--- | :--- | :--- |
| `BlochVector.q` | `Fin 4 → ℝ` | Squared components: $q^{(0)}=1, q^{(1)}=x^2, q^{(2)}=y^2, q^{(3)}=z^2$ |

### QBF Structures (`AlethfeldLean.QBF.Rank1.L1Fourier`)

| Symbol | Description |
| :--- | :--- |
| `ProductState n` | Structure holding angles `θ` and `φ` for $n$ qubits. |
| `fourierCoeff U α` | $\hat{U}(\alpha) = 2^{-n} \text{Tr}(\sigma^\alpha U)$. |

### Influence Functions (`AlethfeldLean.QBF.Rank1.L2Influence`)

| Symbol | Description |
| :--- | :--- |
| `qProduct bloch α` | Product $\prod_k q_k^{(\alpha_k)}$ of squared Bloch components. |
| `probability bloch α` | Fourier weight $p_\alpha = 2^{2-2n} \prod_k q_k^{(\alpha_k)}$. |
| `influence_j bloch j` | Influence of qubit $j$: $I_j = \sum_{\alpha: \alpha_j \neq 0} p_\alpha$. |
| `totalInfluence bloch` | Total influence: $I = \sum_j I_j$. |

## 3. Main Theorems

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

### Bloch Component Identities (`AlethfeldLean.Quantum.Bloch`)

*   **`BlochVector.q_sum_eq_two (v)`**:
    $$q^{(0)} + q^{(1)} + q^{(2)} + q^{(3)} = 1 + x^2 + y^2 + z^2 = 2$$
    *Usage*: Key identity for factorizing influence sums.

*   **`BlochVector.q_nonzero_sum_eq_one (v)`**:
    $$q^{(1)} + q^{(2)} + q^{(3)} = x^2 + y^2 + z^2 = 1$$
    *Usage*: Direct consequence of Bloch vector normalization.

### Influence Independence (`AlethfeldLean.QBF.Rank1.L2Influence`)

*   **`total_influence_formula (bloch)`** (Lemma L2):
    For any rank-1 product state QBF:
    $$I(U) = n \cdot 2^{1-n}$$
    *Usage*: Total influence depends only on qubit count, not on Bloch vectors.

*   **`influence_independent_of_bloch (bloch₁ bloch₂)`**:
    $$I(\text{bloch}_1) = I(\text{bloch}_2)$$
    *Usage*: Proves influence is a universal property of rank-1 QBFs.

*   **`influence_pos (bloch) (hn : n ≥ 1)`**:
    $$I(U) > 0$$
    *Usage*: Influence is strictly positive for any non-trivial system.

## 4. Agent Guidelines

### For the **Prover** Agent

*   **referencing**: When proposing steps, explicitly cite these results.
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
*   **Type Coercion**: Be careful with `ℂ` (Complex) vs `ℝ` (Real).
    *   `BlochVector` components are `ℝ`.
    *   Matrices are over `ℂ`.
    *   Use `↑` (coe) or `Complex.ofReal` when mixing them.
*   **Mathlib**: This library depends on Mathlib. You have full access to `Mathlib.Data.Matrix`, `Mathlib.Analysis.InnerProductSpace`, etc.

## 5. Example Usage

```lean
import AlethfeldLean.Quantum.Bloch
import AlethfeldLean.Quantum.Pauli

open Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch

example (θ φ : ℝ) :
  let ψ := blochState θ φ
  expectation ψ σX = (blochVectorOfAngles θ φ).x := by
  -- This is exactly theorem expectation_σX
  exact expectation_σX θ φ
```
