# Alethfeld CLI v0.1.0

Semantic proof graph operations with context emission (implementing spec v2.3).

## Status

**In Development** - This is the next-generation CLI implementing the v2.3 specification.

For the current stable CLI, see [`cli-legacy/`](../cli-legacy/).

## New Features (v2.3 spec)

- **Context emission**: `context` command emits phase-specific prompt fragments
- **Next suggestions**: `next` command suggests optimal next action
- **Self-documenting**: `help` and `schema` commands provide on-demand documentation
- **FSM workflow**: State machine with enforced phase transitions
- **Triple-verifier**: Multi-verifier voting system
- **Subgraphs**: Split and merge independent subproofs
- **Checkpoints**: Save and restore graph state

## Quick Start

```bash
# Run via Clojure CLI (development)
clojure -M:run --help
clojure -M:run --version

# Run tests
clojure -M:test
```

## Directory Structure

```
cli/
├── src/alethfeld/
│   ├── core.clj           # CLI entry point
│   ├── version.clj        # Version info
│   ├── schema/            # Malli schemas
│   ├── ops/               # Graph operations
│   ├── commands/          # CLI command handlers
│   ├── fsm/               # State machine
│   └── context/           # Context emission
├── test/alethfeld/        # Tests
├── resources/templates/   # Phase templates (markdown)
└── deps.edn
```

## Implementation Progress

See beads issues with prefix `Phase` for tracking:
- Phase 0: Setup and migration
- Phase 1: FSM foundation
- Phase 2: Context emission
- Phase 3: CLI commands
- Phase 4: Advanced operations
- Phase 5: Migration and integration
- Phase 6: Testing and build

## Specification

See [`cli-requirements-v2.3.md`](../cli-requirements-v2.3.md) for the full specification.
