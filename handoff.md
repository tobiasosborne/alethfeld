# Alethfeld Session Handoff

**Last updated:** 2026-01-08
**Last session:** v0.1 bootstrap and Step 0.1 complete

## Current State

### Repository Structure
- **Branch:** `main` (v2 development, hidden from public)
- **Default branch on GitHub:** `legacy` (v1, public-facing)
- v1 code archived in `archive/v1/`

### Project Status
Alethfeld v0.1 is a complete rewrite. We're building a CLI tool (`af`) for collaborative proof verification with AI agent swarms.

### Completed This Session
1. Created `legacy` branch and set as GitHub default (preserves stars)
2. Archived all v1 files to `archive/v1/`
3. Set up new project structure with plan docs in `docs/`
4. Registered 28 implementation steps as beads issues with dependencies
5. **Completed Step 0.1: Repository & Build Structure**
   - Created `deps.edn` with dependencies (malli, data.json, babashka/process, babashka/fs)
   - Created `build.clj` for uberjar compilation
   - Created `src/alethfeld/cli.clj` entry point
   - Verified `clj -M:run` works

### Current Issue
None in progress.

## Next Steps

**Next ready issue:** `alethfeld-rfud` (Step 0.2: Test Infrastructure)

This involves:
- Set up `test/` directory structure mirroring `src/`
- Add `cognitect/test-runner` to deps.edn (already done)
- Create test runner alias `:test` (already done)
- Create first dummy test to verify infrastructure
- Document test conventions in CLAUDE.md
- Deliverable: `clj -M:test` runs and passes

## Key Files

| File | Purpose |
|------|---------|
| `docs/PRD.md` | Product requirements |
| `docs/TECH-SPEC.md` | Technical specification (schemas, CLI spec) |
| `docs/IMPLEMENTATION-PLAN.md` | 28 steps across 7 phases |
| `deps.edn` | Clojure dependencies |
| `src/alethfeld/cli.clj` | CLI entry point |

## Blockers

None.

## Commands Reference

```bash
# Run CLI
clj -M:run

# Run tests (after Step 0.2)
clj -M:test

# Build uberjar
clj -T:build uber

# Check ready issues
bd ready

# View issue
bd show <id>
```
