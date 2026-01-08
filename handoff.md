# Alethfeld Session Handoff

**Last updated:** 2026-01-08
**Last session:** Step 3.1 Role Derivation

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
| 1.1 | Schema Definitions | 22 (111 assertions) |
| 1.2 | Mote Constructors | 11 |
| 1.3 | Mote Transformations | 14 |
| 2.1 | ID Operations | 13 |
| 2.2 | Path Derivation | 13 |
| 2.3 | DAG Validation | 22 |
| 3.1 | Role Derivation | 21 (77 assertions) |

**Total:** 99 tests, 538 assertions - all passing

### Recent Work (this session)
- Completed `alethfeld-8g9a`: Step 3.1 Role Derivation + Tests
- Created `src/alethfeld/job.clj` with:
  - `mote->roles`: Returns set of roles based on taint flags
  - `mote->role`: Returns primary role (priority-ordered)
  - `workable?`: Checks if mote needs work
  - `matches-filter?`: Filters motes by role/difficulty/priority

### Current Issue
None in progress.

## Next Steps

**Next ready issue:** `alethfeld-xm4r` (Step 3.2: Job Selection Algorithm + Tests)

This involves:
- `select-jobs`: filter + sort + take N
- `priority-rank`: priority -> numeric rank for sorting
- `job-comparator`: sort by priority, then difficulty
- `build-job`: mote + context -> Job record
- Comprehensive tests for selection algorithm

### Code Review Issues (from previous session)
| Issue | Priority | Description |
|-------|----------|-------------|
| `alethfeld-9b04` | P2 | Add comment to find-cycles DFS algorithm |
| `alethfeld-kvcp` | P2 | Make validation error collection consistent |
| `alethfeld-gp1q` | P2 | Fix flaky generate-id-test |
| `alethfeld-ann3` | P3 | Make now function injectable for test determinism |
| `alethfeld-x982` | P3 | Add property-based tests for ID/path operations |

## Key Files

| File | Purpose |
|------|---------|
| `src/alethfeld/schema.clj` | Malli schemas |
| `src/alethfeld/mote.clj` | Mote constructors & transformations |
| `src/alethfeld/id.clj` | MoteId parsing & navigation |
| `src/alethfeld/path.clj` | File path derivation |
| `src/alethfeld/dag.clj` | DAG validation functions |
| `src/alethfeld/job.clj` | Role derivation & filtering |
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
