# Alethfeld: Rigorous Proofs via Adversarial AI Agents

**Alethfeld** is a system for developing mathematical proofs with machine-checked rigour. It coordinates multiple AI agents—each with a specific role—to produce proofs that are structured, verified, and traceable.

The name combines *aletheia* (Greek: truth, disclosure) with *feld* (German: field)—a field where truth is cultivated through structured adversarial refinement.

## Origin

This system emerged from a simple question posed to Claude: *"What would help you prove theorems more reliably?"*

The answer was surprisingly specific:

1. **Structured notation** — not free-form prose, but hierarchical steps with explicit dependencies
2. **Lamport's proof style** — the hierarchical format developed by Leslie Lamport for TLA+
3. **Adversarial verification** — a separate agent whose job is to find errors
4. **Explicit citations** — no "well known" or "standard result," only traceable references

Alethfeld implements these suggestions. The prompts, the format, and the workflow all derive from what the model identified as its own failure modes and what would help it avoid them.

## Project Structure

- **`cli/`**: The primary CLI tool for all semantic proof graph operations.
- **`docs/`**: Documentation, architecture, and historical records.
- **`examples/`**: Curated, verified proof examples (EDN, LaTeX, Lean).
- **`lean/`**: The Lean 4 formal verification library and environment.
- **`proofs/`**: Your local sandbox. Git-ignored; use this for your own experiments.
- **`scripts/`**: Utility scripts for maintenance, validation, and refactoring.

## The Problem

Large language models can do mathematics. They can also hallucinate, skip steps, cite theorems that don't exist, and produce proofs that look convincing but collapse under scrutiny.

For working mathematicians, this makes LLMs a frustrating tool: occasionally brilliant, frequently unreliable, always requiring manual verification of every claim.

## The Approach

Alethfeld doesn't try to make a single AI "smarter." Instead, it separates concerns:

| Agent | Role |
|-------|------|
| **Adviser** | Evaluates proof strategies before work begins. Identifies doomed approaches early. |
| **Prover** | Writes proofs in Lamport structured notation. Every step has an explicit justification. |
| **Verifier** | Adversarially checks each step. Assumes the Prover is wrong until convinced otherwise. |
| **Lemma Decomposer** | Identifies extractable independent subproofs. |
| **Reference Checker** | Validates citations. Confirms that cited theorems exist and say what is claimed. |
| **Formalizer** | Converts verified proofs to Lean 4. |
| **Orchestrator** | Manages the workflow. Tracks iterations. Knows when to escalate to a human. |

The Prover and Verifier operate in a loop: the Prover asserts a step, the Verifier challenges it, the Prover revises. This continues until the Verifier accepts or iteration limits are reached.

This adversarial structure catches errors that a single model would miss.

## Current Status (January 2026)

### Orchestrator Protocol

Two versions are available:

| Version | Status | Description |
|---------|--------|-------------|
| **v5.1** | Stable | Anti-sycophancy protocols, domain restriction checks, theorem audit phase |
| **v5.2** | Experimental | Explicit state machine, exhaustive CLI signatures, LaTeX template |

**v5.1 (Stable)** — Based on BrokenMath benchmark failure analysis:
- Anti-sycophancy protocols for adversarial verification
- Domain restriction checks for implicit assumptions
- Optimization completeness requirements
- Theorem audit phase for unknown sources

**v5.2 (Experimental)** — Additional clarity improvements:
- Explicit state machine with 30+ defined transitions (§VI)
- Exhaustive CLI reference with documented non-existent flags (§IX)
- External LaTeX template (`latex-template.tex`)
- Subagent dispatch protocol

**Model-specific prompts:**
- [`orchestrator-prompt-v5.1-claude.md`](orchestrator-prompt-v5.1-claude.md) — Stable, optimized for Claude Code
- [`orchestrator-prompt-v5_2-claude.md`](orchestrator-prompt-v5_2-claude.md) — Experimental, explicit control flow
- [`orchestrator-prompt-v5.1-gemini.md`](orchestrator-prompt-v5.1-gemini.md) — Gemini CLI (experimental)
- [`orchestrator-prompt-v5.1-codex.md`](orchestrator-prompt-v5.1-codex.md) — Codex CLI (experimental)

*Note: The Gemini and Codex prompts are experimental. Results with these tools have been suboptimal compared to Claude Code.*

### Verified Results

The system has been successfully used to derive and formalize several non-trivial results:

**Fully Verified (0 sorries in Lean 4):**
- **QBF Rank-1 Master Theorem**: Entropy-influence bound for rank-1 quantum Boolean functions
- **Quantum Entropy Increase Theorem**: TH-transformation increases entropy by exactly the influence (~3800 lines Lean 4)
- **Halting Undecidability**: Classic diagonalization argument (0 axioms)
- **Kelly's Lemma**: Edge count reconstruction from graph decks
- **Dobinski's Formula**: Bell numbers via infinite series
- **Shannon Maximum Entropy**: Uniform distribution uniqueness

See `lean/API.md` for full documentation of the Lean library.

### Error Detection: BrokenMath Benchmark

Alethfeld has been tested against problems from the [BrokenMath](https://github.com/insait-institute/broken-math) benchmark—a dataset of mathematical problems with subtle errors.

- **Divisor Sum Problem**: Detected that the claimed sum (105) is incorrect; proved the correct sum is **66** with full Lean 4 formalization.

- **HMMT Feb 2025 Problem 3**: Discovered during Lean formalization that the claimed minimum (576) is actually the **maximum**. Found counterexample: `(x, y, z) = (1/4, 1/8, 1/18)` gives `xyz = 1/576 < 576`.

This demonstrates that the adversarial verification approach catches not just proof errors, but also errors in problem statements.

## Lamport Structured Proofs

At the heart of Alethfeld is Leslie Lamport's hierarchical proof notation, originally developed for specifying and verifying concurrent systems in TLA+.

The key insight: most proof errors hide in "obvious" steps. By forcing every inference to be explicit and small, errors have nowhere to hide.

A Lamport-style proof has:

- **Hierarchical numbering**: Top-level steps are ⟨1⟩1, ⟨1⟩2, etc. Substeps that justify ⟨1⟩2 are numbered ⟨2⟩1, ⟨2⟩2, and so on.
- **Explicit dependencies**: Each step lists exactly which prior steps and assumptions it uses.
- **Named inference rules**: Not "therefore" but "by modus ponens from ⟨1⟩2 and ⟨1⟩3."
- **Scope tracking**: Assumptions introduced for sub-proofs are explicitly discharged.

This format is unusually well-suited to LLM-based proving:

1. **Errors are localised.** When the Verifier challenges a step, the Prover knows exactly what to fix.
2. **Dependencies are auditable.** You can trace any claim back to its foundations.
3. **The hierarchy manages complexity.** Top-level structure is established first, then refined.

## Why EDN?

Proofs are represented in [EDN](https://github.com/edn-format/edn) (Extensible Data Notation), a data format from the Clojure ecosystem.

**For schema validation:** EDN works seamlessly with [Malli](https://github.com/metosin/malli), a data-driven schema library. The proof format has a formal schema—steps can be validated, transformed, and analysed programmatically.

**For readability:** EDN is more readable than JSON (commas optional, keywords are first-class, comments allowed) while remaining machine-parseable.

**For extensibility:** New fields can be added without breaking existing tooling. Proofs are data, not strings.

## What It Produces

Given a theorem statement, Alethfeld outputs:

1. **Structured proof (EDN)** — Machine-readable, schema-validated, with explicit justifications
2. **LaTeX document** — Publication-ready, with proper citations and Lamport-style formatting
3. **Lean 4 code** — Formal verification target (admitted steps marked with `sorry`)

## How It Works

```
┌─────────────────────────────────────────────────────────────────┐
│                         ORCHESTRATOR                            │
│  Manages state, enforces iteration limits, handles escalation   │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌───────────────┐
│   ADVISER     │  ◄── "Is this approach viable?"
│               │  ──► Strategy evaluation, skeleton review
└───────────────┘
        │
        ▼
┌───────────────┐
│    PROVER     │  ◄── "Prove this theorem"
│               │  ──► Lamport-structured EDN proof
└───────────────┘
        │
        ▼
┌───────────────┐     ┌───────────────┐
│   VERIFIER    │ ◄──►│    PROVER     │  Adversarial loop
│               │     │  (revisions)  │  (max 7 rounds/step)
└───────────────┘     └───────────────┘
        │
        ▼
┌───────────────┐
│  REF CHECKER  │  ◄── "Does this citation exist?"
│               │  ──► Verified bibliography
└───────────────┘
        │
        ▼
┌───────────────┐     ┌───────────────┐
│   LaTeX-er    │     │  Formalizer   │
│               │     │               │
└───────────────┘     └───────────────┘
        │                    │
        ▼                    ▼
   paper.tex            proof.lean
```

### Iteration Limits

The system won't spin forever:

- **7 rounds** per step for Prover-Verifier negotiation
- **50 rounds** total across all steps
- **5 attempts** to fix a skeleton
- **3 Adviser consultations** for stuck diagnosis

When limits are reached, the step is escalated to the human with full context: what was tried, what failed, what the Adviser suggests.

### Proof Obligations

Sometimes a step requires a lemma that would derail the main proof. The Prover can mark such steps as "admitted"—explicitly acknowledging a gap. These become tracked proof obligations, reported at the end.

This is honest: the proof is valid *if* the obligations hold. No hidden assumptions.

## For Mathematicians

**What this is:**
- A tool for accelerating proof development
- A structured format that forces explicit reasoning
- An adversarial check that catches sloppy steps
- A path toward formal verification

**What this is not:**
- A replacement for mathematical understanding
- A guarantee of correctness (the Verifier is an LLM, not a proof assistant)
- A way to prove theorems you don't understand

The output is a *candidate* proof. For research mathematics, you still need to read it, understand it, and verify the admitted steps. But the Lamport structure makes verification tractable: each step is small, its dependencies are explicit, and its justification is named.

For ultimate confidence, the Lean 4 output can be fed to a genuine proof assistant. The `sorry` markers show exactly where human work is needed.

## For Engineers

**Requirements:**
- An AI coding assistant CLI: Claude Code, Gemini CLI, or Codex CLI
- ~100 turns for a moderately complex proof
- **Recommended for Claude Code:** Install the [Lean LSP MCP server](https://github.com/oOo0oOo/lean-lsp-mcp) for direct Lean 4 type checking and goal state inspection

**Usage:**
```bash
# For Claude Code (stable)
cat orchestrator-prompt-v5.1-claude.md | claude

# For Claude Code (experimental - v5.2)
cat orchestrator-prompt-v5_2-claude.md | claude

# For Gemini CLI
cat orchestrator-prompt-v5.1-gemini.md | gemini

# For Codex CLI
cat orchestrator-prompt-v5.1-codex.md | codex
```

Then provide a theorem:
```
Prove: The composition of two continuous functions is continuous.
Use the ε-δ definition.
```

The orchestrator will:
1. Create workspace directories
2. Consult the Adviser on strategy
3. Request a skeleton from the Prover
4. Expand and verify each step
5. Check all external references
6. Generate LaTeX and Lean output

**Customisation:**

The agent prompts are in the orchestrator file. You can:
- Adjust iteration limits
- Add domain-specific inference rules
- Modify the LaTeX template (v5.2: use `latex-template.tex`)
- Change the proof notation style
- Add Malli schemas for stricter validation

## Tools

### alethfeld CLI

The primary CLI tool for all semantic proof graph operations. Located in [`cli/`](cli/).

**Quick Start (Compiled - Recommended):**
```bash
cd cli
./scripts/alethfeld <command> [options]
```

**Development (Slow CLI):**
```bash
cd cli
clojure -M:run <command> [options]
```

**Commands:**
- `init` — Initialize a new proof graph from a theorem
- `add-node` — Add nodes (claims, assumptions, definitions)
- `update-status` — Update verification status (verified/rejected/admitted)
- `replace-node` — Replace rejected nodes with revisions
- `delete-node` — Archive leaf nodes
- `extract-lemma` — Extract verified subgraphs as independent lemmas
- `external-ref` — Manage literature citations
- `validate` — Schema and semantic validation
- `stats` — Display graph statistics
- `recompute` — Recalculate taint propagation

**Example workflow:**
```bash
cd cli

# Initialize a proof
./scripts/alethfeld init "For all continuous f,g: (g \circ f) is continuous"

# Add a claim
./scripts/alethfeld add-node proof.edn step1.edn

# Verify it
./scripts/alethfeld update-status proof.edn :1-abc123 verified

# Extract as lemma
./scripts/alethfeld extract-lemma proof.edn --name "Composition" --root :1-abc123 --nodes :1-abc123
```

See [`cli/README.md`](cli/README.md) and [docs/cli-reference.md](docs/cli-reference.md) for complete documentation.

### ansi-viz

A lightweight terminal-based visualization tool for proof graphs. Located in [`scripts/ansi-viz.clj`](scripts/ansi-viz.clj).

**Usage:**
```bash
./scripts/ansi-viz.clj <proof-graph.edn>
```

See [docs/ansi-viz.md](docs/ansi-viz.md) for details.

## Version History

| Version | Date | Key Changes |
|---------|------|-------------|
| v5.0 | Nov 2024 | Initial structured protocol |
| v5.1 | Dec 2024 | Anti-sycophancy, domain checks, theorem audit |
| v5.2 | Jan 2025 | Explicit state machine, CLI docs, LaTeX template |

See [`CHANGELOG-v5.2.md`](CHANGELOG-v5.2.md) for detailed migration guide.

## Contributing

This is an active research project. If you're interested in:
- Testing on theorems from your field
- Improving the agent prompts
- Adding Malli schemas for validation
- Connecting to proof assistants
- Building tooling around the EDN format

...contributions are welcome.

## License

MIT

## Acknowledgments

- **Leslie Lamport** for hierarchical structured proofs and the TLA+ proof style
- **Anthropic's Claude** for identifying its own failure modes and suggesting this approach
- The **Clojure community** for EDN and Malli
