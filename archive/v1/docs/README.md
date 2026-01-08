# Alethfeld Documentation

Welcome to the documentation for **Alethfeld**, a system for developing rigorous, machine-checked mathematical proofs using adversarial AI agents.

## Table of Contents

1. **[Architecture & Concepts](architecture.md)**
   - Learn about the multi-agent system (Adviser, Prover, Verifier).
   - Understand the "Truth Field" philosophy.
   - See how the components interact.

2. **[Getting Started & Usage](usage.md)**
   - Prerequisites (Lean 4, LLM CLI).
   - How to run the orchestrator.
   - Directory structure of a generated proof.

3. **[The Proof Format](proof-format.md)**
   - Understanding the Lamport-style hierarchical notation.
   - The EDN (Extensible Data Notation) semantic graph.
   - Node types, justification rules, and schemas.

4. **[Lean 4 Formalization](lean-integration.md)**
   - How Alethfeld bridges semantic graphs to formal code.
   - The `AlethfeldLean` library structure.
   - Handling `sorry` (admitted steps) and taint tracking.

5. **[CLI Tools Reference](cli-reference.md)**
   - Detailed command reference for the main `alethfeld` CLI.
   - [ANSI Visualization Tool](ansi-viz.md) - Terminal-based proof graph viewer.

## Quick Links

- **Project Root**: See the top-level [README](../README.md) for a quick start.
- **Orchestrator Protocol**: See [orchestrator-prompt-v5.1-claude.md](../orchestrator-prompt-v5.1-claude.md) (stable) or [orchestrator-prompt-v5_2-claude.md](../orchestrator-prompt-v5_2-claude.md) (experimental).
- **Examples**: Check [examples/qbf-rank1](../examples/qbf-rank1) for a complete derivation of the Entropy-Influence bound.
