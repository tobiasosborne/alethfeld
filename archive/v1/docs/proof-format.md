# The Proof Format

Alethfeld uses a strict, machine-readable format for proofs, combining **Leslie Lamport's hierarchical structuring** with **EDN (Extensible Data Notation)**.

## Why EDN?
EDN is a subset of Clojure syntax used as a data transfer format. It supports:
-   **Keywords** (`:key`) for efficient keys.
-   **Sets** (`#{:a :b}`) for dependencies.
-   **Extensibility** via tagged elements (though Alethfeld mostly uses standard types).
-   **Readability**: It supports comments and is less verbose than JSON for mixed data.

## The Semantic Graph Schema

The core artifact is a **Semantic Graph**, where nodes represent proof steps and edges represent dependencies.

```clojure
{:graph-id "uuid"
 :theorem {:statement "..."}
 :nodes
 { :1-node-id
   {:id :1-node-id
    :type :claim             ; :assumption, :definition, :claim, :qed, etc.
    :statement "LaTeX string"
    :dependencies #{:0-assumption-1 :1-prev-step}
    :justification :modus-ponens
    :status :verified        ; :proposed, :verified, :rejected, :admitted
    :taint :clean            ; :clean, :tainted, :self-admitted
    :depth 1                 ; Hierarchical depth (1 = top level)
    :parent nil
   }
 }
}
```

## Lamport Hierarchical Structure

Proofs are structured as trees.

*   **Level 1**: The main high-level steps of the proof.
*   **Level 2**: Sub-proofs justifying a complex Level 1 step.
*   **Level 3**: Further breakdown.

**Example:**

> **Theorem**: If $x$ is even, $x+1$ is odd.
>
> **<1>1**. Assume $x$ is even.
> **<1>2**. There exists $k$ such that $x = 2k$.
>     **Justification**: Definition of even integers.
> **<1>3**. $x + 1 = 2k + 1$.
>     **Justification**: Algebra on <1>2.
> **<1>4**. Q.E.D.
>     **Justification**: Definition of odd integers (form $2m+1$).

In the graph, node `<1>3` would have `parent: <1>2` (or be a sibling depending on how the sub-proof is structured). Alethfeld enforces that a step is proven *either* by an atomic justification (like `:algebraic-rewrite`) *or* by a complete set of sub-steps ending in a QED.

## Justification Rules

The Prover must select from a fixed set of justification keywords. This constraints the search space and makes checking easier.

-   `:assumption` / `:local-assumption`
-   `:definition-expansion`
-   `:substitution`
-   `:modus-ponens`
-   `:algebraic-rewrite`
-   `:case-split`
-   `:induction-base` / `:induction-step`
-   `:contradiction`
-   `:lemma-application`
-   `:admitted` (The "Gap" - marks the step as unproven but accepted for now)

## Taint Tracking

A critical feature is **Taint Propagation**.
-   If a step is `:admitted`, it is **Self-Admitted**.
-   Any step that depends on an admitted step becomes **Tainted**.
-   The final theorem is only `:clean` if the path to QED is free of taint.

This allows the system to produce "partial proofs" that are honest about their gaps.
