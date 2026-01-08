# Lean 4 Integration

The ultimate goal of Alethfeld is to produce verified code in the **Lean 4** theorem prover.

## The Gap Between NLP and Formalization

Large Language Models are good at "Natural Language Proofs" (NLP) but struggle with the strict syntax and tactic state of formal provers. Alethfeld bridges this by using the **Semantic Graph** as an intermediate representation.

1.  **Semantic Graph**: Captures the *logical* structure (dependencies, steps, reasons) without getting bogged down in syntax errors.
2.  **Formalization**: Translates that verified structure into a code skeleton.

## The Translation Process

The **Formalizer Agent** reads the EDN graph and produces a `.lean` file.

### 1. Symbol Mapping
Symbols in the graph (e.g., `:sym-U` with type `Unitary operator`) need to be mapped to Lean types.
-   `Unitary operator` → `Matrix (Fin d) (Fin d) ℂ` + `Unitary` predicate.
-   `Real 4-vector` → `Fin 4 → ℝ`.

*Note: This mapping is currently heuristic and often requires human refinement.*

### 2. Structure Preservation
The hierarchical structure of the Lamport proof maps naturally to Lean's `have` blocks or `section`s.

```lean
theorem main_theorem : ... := by
  -- Step <1>1
  have h1 : ... := by
    sorry -- Justification: :definition-expansion

  -- Step <1>2
  have h2 : ... := by
    -- Uses h1
    sorry -- Justification: :algebraic-rewrite

  exact h2
```

### 3. Handling `sorry`
Alethfeld is **honest**. It does not pretend to write full tactics if it cannot.
-   **Clean Steps**: If the AI is confident, it might try `simp`, `rw`, or `ring`.
-   **Complex Steps**: It defaults to `sorry`, leaving a comment with the logical justification from the graph.
-   **Goal**: The result is a *compilable* file where the human user can fill in the `sorry` gaps, focusing on *tactics* rather than *structure*.

## The `AlethfeldLean` Library

The project includes a support library in `lean/AlethfeldLean/`.
-   **`Quantum/`**: Definitions for quantum information (matrices, Kronecker products, Bloch spheres).
-   **`QBF/`**: Specific definitions for Quantum Boolean Functions.

When generating code, the Formalizer assumes this library is available.

## Example Output

See `lean/AlethfeldLean/QBF/Rank1/L1Fourier.lean` for an example of a generated file (potentially refined by a human) corresponding to the QBF proof.
