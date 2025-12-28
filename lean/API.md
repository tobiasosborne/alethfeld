# Alethfeld Lean Library API Reference

This document serves as a guide for **Prover** and **Formalizer** agents using the Alethfeld Lean 4 library. It details the module structure, key definitions, main theorems, and usage patterns.

## 1. Project Overview & Status

*   **Package Name**: `AlethfeldLean`
*   **Dependency**: `mathlib` (v4.26.0)
*   **Verification Status**: **COMPLETE** (As of Dec 2025)
    *   All core lemmas in `Pauli.lean`, `Bloch.lean`, and `L1Fourier.lean` are fully proven without `sorry`.
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