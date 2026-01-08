# Alethfeld Session Handoff

**Last updated:** 2026-01-08
**Last session:** Completed Step 2.3 DAG Validation, cleaned up 24 invalid issues from archived v1 spec

## Current State

### Repository Structure
- **Branch:** `main` (v2 development, hidden from public)
- **Default branch on GitHub:** `legacy` (v1, public-facing)
- v1 code archived in `archive/v1/`

### Project Status
Alethfeld v0.1 is a complete rewrite. Building a CLI tool (`af`) for collaborative proof verification with AI agent swarms.

### Completed Steps
| Step | Description | Tests |
|------|-------------|-------|
| 0.2 | Test Infrastructure | 2 |
| 1.1 | Schema Definitions | 22 (104 assertions) |
| 1.2 | Mote Constructors | 11 |
| 1.3 | Mote Transformations | 14 |
| 2.1 | ID Operations | 13 |
| 2.2 | Path Derivation | 13 |
| 2.3 | DAG Validation | 22 |

**Total:** 78 tests, 454 assertions - all passing

### Current Issue
None in progress.

## Next Steps

**Next ready issue:** `alethfeld-8g9a` (Step 3.1: Role Derivation + Tests)

This involves:
- Create `job.clj` with job selection functions
- Functions: mote->role, workable?, matches-filter?
- Write comprehensive tests

## Key Files

| File | Purpose |
|------|---------|
| `src/alethfeld/schema.clj` | Malli schemas |
| `src/alethfeld/mote.clj` | Mote constructors & transformations |
| `src/alethfeld/id.clj` | MoteId parsing & navigation |
| `src/alethfeld/path.clj` | File path derivation |
| `src/alethfeld/dag.clj` | DAG validation functions |
| `test/alethfeld/` | All tests |

## Blockers

None.

## Commands

```bash
clj -M:run     # Run CLI
clj -M:test    # Run tests
bd ready       # Check ready issues
bd show <id>   # View issue
```
