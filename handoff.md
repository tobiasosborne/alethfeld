# Alethfeld Session Handoff

**Last updated:** 2026-01-08
**Last session:** Step 3.1 + 3.2 Job Selection

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
| 3.2 | Job Selection Algorithm | 23 (58 assertions) |

**Total:** 122 tests, 596 assertions - all passing

### Recent Work (this session)
- Completed `alethfeld-8g9a`: Step 3.1 Role Derivation + Tests
- Completed `alethfeld-xm4r`: Step 3.2 Job Selection Algorithm + Tests
- `src/alethfeld/job.clj` now includes:
  - Role derivation: `mote->roles`, `mote->role`
  - Workability: `workable?`
  - Filtering: `matches-filter?`
  - Sorting: `priority->rank`, `job-comparator`
  - Job building: `build-job`
  - Job selection: `select-jobs`

### Current Issue
None in progress.

## Next Steps

**Next ready issue:** `alethfeld-djwx` (Step 3.3: Prompt Rendering + Tests)

This involves:
- Create `src/alethfeld/prompt.clj`
- Define prompt templates as data
- `render-prompt`: role + mote + context → prompt string
- `format-assumptions`, `format-definitions`, `format-vote-summary`
- Comprehensive tests for prompt rendering

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
| `src/alethfeld/job.clj` | Role derivation, filtering, job selection |
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
