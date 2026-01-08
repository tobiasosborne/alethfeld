# History of Alethfeld

This document tracks the evolution of the Alethfeld project, from its inception as a conversation about AI failure modes to its current state as a hybrid LLM-Formal Verification system.

## Inception: The "Garbage In" Problem (Dec 26, 2025)

The project began on December 26, 2025, born from a question posed to Claude: *"What would help you prove theorems more reliably?"*

Early experiments focused on a "Random Purification" proof. These initial runs revealed a critical failure mode: **Garbage In, Garbage Out**.
- The system was given a theorem statement with a subtle error (brackets in the wrong place).
- The "Prover" agent successfully "proved" the incorrect statement.
- The "Verifier" agent accepted the proof because the logic within the proof was consistent with the (flawed) premises.

This failure defined the project's core philosophy: **Adversarial Verification**. A proof is not just a text generation task; it is a game played between a Prover (who wants to be right) and a Verifier (who assumes the Prover is wrong).

## The QBF & Lean Sprint (Dec 27–29, 2025)

To test the system on real mathematics, the project pivoted to Quantum Boolean Functions (QBF), specifically results concerning Rank-1 product states.

### Key Milestones:
- **Dec 27**: Adoption of the **Lamport Structured Proof** format (TLA+ style) to force explicit reasoning.
- **Dec 28**: Integration of **Lean 4**. It became clear that LLM verification alone was insufficient. The system was re-architected to output Lean 4 code, using formal verification as the ultimate arbiter.
- **The "Sorry" Elimination**: A concentrated effort (Dec 28-29) successfully formalized and proved a chain of lemmas without any `sorry` (admitted steps):
    - **L1 (Fourier)**: Closed-form Fourier coefficients.
    - **L2 (Influence)**: Independence of influence from Bloch vectors.
    - **L3 (Entropy)**: General entropy formula.
    - **Shannon Maximum**: Proof that uniform distribution maximizes entropy.

This period proved that the "LLM Draft -> Lean Verify" pipeline was viable for non-trivial research mathematics.

## Tooling & Architecture Maturity (Dec 29–30, 2025)

As the complexity of proofs grew, the initial ad-hoc scripts broke down. This phase focused on building robust infrastructure.

### The CLI Revolution
- **Dec 30**: The `alethfeld` CLI tool was built from scratch to replace scattered scripts.
- **Features**: Semantic graph operations (`add-node`, `extract-lemma`), taint tracking, and automated status updates.
- **Performance**: Compilation to a native Uberjar resulted in a 67% speedup.
- **Orchestrator v5**: A major update to the prompt protocol, introducing stricter constraints and better separation of agent concerns.

### Validation
- Introduction of **Malli** schemas for strict EDN validation.
- Refactoring of the `validate-graph` tool.
- Creation of the `docs/` hierarchy and comprehensive architecture documentation.

## Adversarial Robustness & BrokenMath (Dec 31, 2025)

The most recent phase has focused on **robustness against falsehoods**. Can the system detect when it is being lied to?

### The BrokenMath Benchmark
The system was tested against the [BrokenMath](https://github.com/insait-institute/broken-math) dataset—problems designed to trick LLMs.

1.  **Divisor Sum of 9!**:
    - *Prompt*: "Prove the sum is 105."
    - *Result*: Alethfeld detected the error, found the correct sum (66), and formalized the proof in Lean.

2.  **HMMT Feb 2025 Problem 3**:
    - *Prompt*: "Find the minimum value..."
    - *Result*: During Lean formalization, the system discovered a counterexample that violated the proved "theorem," revealing the original problem statement (or the standard interpretation of it) was false.

This marked a qualitative shift: the system was no longer just *verifying proofs* but *discovering truth*, using Lean 4 not just as a check, but as a tool for exploration and error detection.

---

## Timeline Summary

| Date | Phase | Key Achievement |
|------|-------|-----------------|
| **Dec 26** | Inception | Discovery of "Garbage In" failure mode. |
| **Dec 27** | Structure | Adoption of Lamport hierarchical format. |
| **Dec 28** | Formalization | Lean 4 integration; QBF Rank-1 theorems proved. |
| **Dec 29** | Expansion | Master Theorem for QBF; L5 Asymptotic results. |
| **Dec 30** | Engineering | `alethfeld` CLI release; Orchestrator v5; Performance work. |
| **Dec 31** | Robustness | BrokenMath benchmarks; detection of false theorems via Lean. |
