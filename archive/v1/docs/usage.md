# Getting Started & Usage

## Prerequisites

1.  **OS**: Linux or macOS recommended.
2.  **Lean 4**: Install via [elan](https://github.com/leanprover/elan).
    ```bash
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
3.  **Claude CLI / LLM Context**: Currently, Alethfeld is designed as a prompt-driven system. You need a way to feed the `orchestrator-prompt-v5.md` and the project context to an LLM (like Claude 3.5 Sonnet or another capable model).
    *   *Note: In the future, this will be a standalone Python/CLI tool.*

## Setup

1.  Clone the repository:
    ```bash
    git clone https://github.com/tobiasosborne/alethfeld.git
    cd alethfeld
    ```
2.  Initialize the Lean project (if not already done):
    ```bash
    cd lean
    lake build
    ```

## Running a Proof Session

### Automated Agentic Mode (Recommended)

Alethfeld is best run using an agentic interface (like Claude Code or similar) that has file-system access.

1.  **Initialize**: Run the `orchestrator-prompt-v5.md` with the theorem statement.
    ```bash
    # If using a CLI that supports file redirection
    cat orchestrator-prompt-v5.md | your-llm-tool
    ```
2.  **State Theorem**: "Initialize the graph for the following theorem: [Your Theorem Here]".
3.  **Observation**: The agent will coordinate the sub-agents (Adviser, Prover, Verifier, etc.) to build the `proof.edn` graph and generate Lean code.

### Interactive Mode (Manual)

If you don't have an agentic CLI, you can manually copy-paste the orchestrator prompt into a standard LLM chat (e.g., Claude.ai).

1.  **Prepare the Context**: Paste the full content of `orchestrator-prompt-v5.md`.
2.  **Load Project State**: Provide any existing relevant files (e.g., `lean/API.md` for context).
3.  **Iterate**: Manually act as the "Orchestrator" by passing outputs between different chat sessions or keeping it all in one context-heavy thread.

## Directory Structure

A typical project structure looks like this:

```text
.
├── lean/                   # The formal Verification target
│   ├── lakefile.toml
│   └── AlethfeldLean/      # Source files (verified lemmas)
├── examples/               # Completed proofs
│   └── my-proof/
│       ├── proof.edn       # The semantic graph (Source of Truth)
│       ├── proof.tex       # Readable LaTeX version
│       └── proof.lean      # Generated Lean skeleton
└── docs/                   # Documentation
```
