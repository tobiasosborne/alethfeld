# Alethfeld Development Guide

## Critical: Ignore Archive

**NEVER reference `./archive/` directory.** It contains deprecated v1 code with different schemas and specifications. All current work follows:
- `docs/TECH-SPEC.md` - The authoritative specification
- `docs/IMPLEMENTATION-PLAN.md` - The implementation steps

## Session Handoff

**IMPORTANT:** Always read `handoff.md` at the start of each session. Update it before ending your session with current state, blockers, and next steps.

## Project Overview

Alethfeld v0.1 - CLI tool for collaborative proof verification.

## Issue Tracking

This project uses **bd (beads)** for issue tracking.
Run `bd prime` for workflow context.

**Quick reference:**
- `bd ready` - Find unblocked work
- `bd create "Title" --type task --priority 2` - Create issue
- `bd close <id>` - Complete work
- `bd sync` - Sync with git (run at session end)

For full workflow details: `bd prime`

## Build & Test

```bash
# Run CLI (after setup)
clj -M:run

# Run tests
clj -M:test
```

## Architecture

- **Language:** Clojure
- **Approach:** Test-driven, purely functional where possible
- **Persistence:** Git-backed EDN files

## Key Files

- `docs/PRD.md` - Product requirements
- `docs/TECH-SPEC.md` - Technical specification
- `docs/IMPLEMENTATION-PLAN.md` - Development steps

## Conventions

- One mote per EDN file
- Malli for schema validation
- Git commit per CLI operation (ACID)

## Test Conventions

- Test files live in `test/` mirroring `src/` structure
- Namespace naming: `alethfeld.foo` → `alethfeld.foo-test`
- Use `clojure.test` with `deftest`, `testing`, `is`
- Run all tests: `clj -M:test`
- Test runner: cognitect-labs/test-runner
