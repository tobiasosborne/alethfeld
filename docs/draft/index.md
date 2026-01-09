# Alethfeld Documentation

Alethfeld v0.1 — A CLI tool for collaborative proof verification using AI agent swarms.

## Overview

Alethfeld manages a directed acyclic graph of proof steps called *motes*. Autonomous agents query for work, perform specialized verification tasks, and commit results to git. The system provides ACID semantics through git-backed transactions.

**Key characteristics:**
- Git as database — every mutation is an atomic commit
- Schema-first — Malli validation gates all persistence
- Role-based dispatch — taint flags route work to specialists
- Session enforcement — agents bind to motes with role permissions

## Documents

| Document | Description |
|----------|-------------|
| [Architecture](architecture.md) | System layers, data flow, concurrency model |
| [Data Model](data-model.md) | Motes, proposals, jobs, sessions, schemas |
| [Modules](modules.md) | Source code reference by namespace |
| [Transactions](transactions.md) | ACID operations, git integration, locking |
| [Agent Workflow](agent-workflow.md) | Roles, jobs, sessions, quorum rules |
| [Testing](testing.md) | Test organization, conventions, categories |
| [Glossary](glossary.md) | Quick reference for terms and concepts |

## Quick Start

```bash
# Initialize repository
af init

# Create root mote
af create 1 "Main theorem statement" --agent proposer-1

# Get work as verifier
af ready --agent verifier-1 --role verifier --format json

# Cast verification vote
af vote 1 --for --agent verifier-1

# Complete session
af done --agent verifier-1
```

## Repository Structure

```
.alethfeld/
├── config.edn      # Project configuration
├── motes/          # Approved motes (hierarchical)
├── proposed/       # Pending proposals
├── archive/        # Rejected proposals
└── sessions/       # Active and completed sessions
```

## Source Organization

```
src/alethfeld/
├── schema.clj      # Malli schemas
├── id.clj          # Hierarchical ID operations
├── mote.clj        # Mote construction/transformation
├── io.clj          # EDN file I/O
├── path.clj        # Path derivation
├── store.clj       # Mote CRUD
├── dag.clj         # Graph validation
├── tx.clj          # Transaction layer
├── git.clj         # Git operations
├── job.clj         # Work dispatch
├── session.clj     # Session management
├── verify.clj      # Voting workflow
├── proposal.clj    # Decomposition workflow
├── prompt.clj      # Agent prompts
├── cli.clj         # CLI entry point
├── cmd.clj         # Command implementations
└── errors.clj      # Error handling
```

## Further Reading

- `docs/PRD.md` — Product requirements
- `docs/TECH-SPEC.md` — Technical specification
- `docs/IMPLEMENTATION-PLAN.md` — Development roadmap
