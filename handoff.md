# Alethfeld Session Handoff

**Last updated:** 2026-01-09
**Last session:** Step C.4 - Cross-References / Dependencies
**Session status:** COMPLETED SUCCESSFULLY

---

## Quick Status Check

Run these to verify project health:
```bash
clj -M:test                    # Should pass 971 tests, 2634 assertions
git status                     # Should be clean
bd stats                       # Check open/closed counts
```

---

## Current State

### Repository Structure
- **Branch:** `main` (v2 development, hidden from public)
- **Default branch on GitHub:** `legacy` (v1, public-facing)
- **Latest commit:** `654d3a3` - feat: Step C.4 - Cross-References / Dependencies
- v1 code archived in `archive/v1/`

### Project Status
| Phase | Status | Progress |
|-------|--------|----------|
| Phase A | Session & Role Enforcement | **100% COMPLETE** (8/8 steps) |
| Phase B | Essential UX Improvements | **100% COMPLETE** (4/4 steps) |
| Phase C | Quality/Safety Features | **80% COMPLETE** (4/5 steps) |

### Test Health
- **Total tests:** 971
- **Total assertions:** 2,634
- **Status:** ALL PASSING
- **Known flaky tests:**
  - 3 concurrency tests (marked `^:flaky`, test isolation issues)

---

## This Session: Step C.4 Cross-References / Dependencies

### What Was Implemented

Added `af add-dep` command to express mote dependencies (mote X depends on mote Y).

### Command Syntax
```bash
af add-dep <id> --depends-on <mote-id> [--reason "..."] --session TOKEN
```

### Files Modified

| File | Changes |
|------|---------|
| `src/alethfeld/schema.clj` | Added `Dependency` schema and `:depends-on` field to Mote |
| `src/alethfeld/mote.clj` | Added `add-dep` function and `:depends-on` support in `make-mote` |
| `src/alethfeld/cmd.clj` | Added `cmd-add-dep!` function with validation |
| `src/alethfeld/cli.clj` | Added `add-dep` command definition |
| `src/alethfeld/dag.clj` | Updated `find-cycles` and `validate-refs` for dependencies |
| `src/alethfeld/verify.clj` | Added `unverified-dependencies` check, blocks voting |
| `src/alethfeld/errors.clj` | Added `:unverified-dependencies` error formatter |
| `test/alethfeld/dag_test.clj` | Added 11 dependency tests (cycles, refs) |
| `test/alethfeld/mote_test.clj` | Added 3 `add-dep` tests |
| `test/alethfeld/verify_test.clj` | Added 6 dependency verification tests |

### Implementation Details

**Schema:**
```clojure
(def Dependency
  [:map
   [:ref MoteId]
   [:reason {:optional true} :string]])

;; In Mote schema:
[:depends-on {:optional true} [:vector Dependency]]
```

**Core Logic (`cmd-add-dep!`):**
1. Validate mote ID provided
2. Validate dependency target provided
3. Check mote cannot depend on itself
4. Validate session
5. Load mote and dependency target (both must exist)
6. Check for duplicate dependency
7. Add dependency and commit

**DAG Validation:**
- `find-cycles` now includes dependency edges (in addition to assumption refs)
- `validate-refs` now checks both assumption refs AND dependency refs
- Each broken ref includes `:ref-type` (`:assumption` or `:dependency`)

**Verification Blocking:**
- Cannot vote on a mote if any of its dependencies are not `:verified`
- `unverified-dependencies` function returns list of unverified deps
- Throws `:unverified-dependencies` error with list of blocking deps

### Tests Added

| Test | Purpose |
|------|---------|
| `find-cycles-with-dependencies-test` | 5 tests for cycle detection with deps |
| `validate-refs-with-dependencies-test` | 5 tests for ref validation with deps |
| `add-dep-test` | 3 tests for mote/add-dep function |
| `unverified-dependencies-test` | 4 tests for dependency status checking |
| `vote-blocked-by-unverified-dependencies-test` | 2 tests for voting blocked |
| `vote-blocked-error-details-test` | 1 test for error message content |

---

## Phase C Progress

| Step | Issue | Status | Description |
|------|-------|--------|-------------|
| C.1 | `alethfeld-2hdf` | **DONE** | Batch Voting (`af vote-all`) |
| C.2 | `alethfeld-t52o` | **DONE** | Auto-Propagation (`--propagate` flag) |
| C.3 | `alethfeld-hc3w` | **DONE** | Proposal Withdrawal (`af withdraw`) |
| C.4 | `alethfeld-pu9n` | **DONE** | Cross-References / Dependencies (`af add-dep`) |
| C.5 | - | pending | Atomic Markers on Creation |

---

## Next Steps: C.5 Atomic Markers on Creation

### Step C.5: Atomic Markers on Creation

**Goal:** Mark claims as atomic at proposal time.

**Implementation plan from IMPLEMENTATION-PLAN.md:**
- Add `--atomic` flag to `af propose`:
  ```bash
  af propose 1 --claim "Simple fact" --atomic --agent proposer-1 --session <token>
  ```
- When `--atomic` specified:
  - Do NOT add `:needs-decomposition` taint
  - Add `:needs-verification` taint instead
- Can mix: some claims atomic, some not

---

## Bonus: Fixed Flaky Test

Also fixed `alethfeld-gp1q` (flaky generate-id-test):
- Changed timestamp format from `HHmmss` to `HHmmssSSS` (added milliseconds)
- Reduces collision probability from ~7% to near zero when generating 100 IDs

---

## Ready Work Queue

Run `bd ready` to see available issues. Current unblocked work includes:
- Phase C step: C.5 (Atomic Markers on Creation)
- Various bug fixes and enhancements
- Documentation tasks

---

## Architecture Reference

### Key Namespaces

| Namespace | Purpose |
|-----------|---------|
| `alethfeld.cli` | CLI entry point, argument parsing, command definitions |
| `alethfeld.cmd` | Command implementations (cmd-*! functions) |
| `alethfeld.proposal` | Proposal workflow: create, approve, reject, withdraw |
| `alethfeld.verify` | Verification voting, quorum logic, propagation |
| `alethfeld.session` | Session management, role enforcement |
| `alethfeld.mote` | Mote constructors and transformations |
| `alethfeld.store` | File I/O, mote persistence |
| `alethfeld.tx` | Transaction layer, atomic writes |
| `alethfeld.errors` | Human-readable error formatting |

### Directory Structure

```
.alethfeld/
├── config.edn           # Project configuration
├── motes/               # Active motes (fixed, verified, etc.)
│   └── 1/               # Ancestor directories
│       └── 1.2.edn
├── proposed/            # Pending proposals
│   └── 1.1.edn
├── archive/             # Rejected/withdrawn motes
│   └── 1/
│       └── 1.2.edn
└── sessions/
    ├── active/          # Current sessions
    └── completed/       # Ended sessions (audit trail)
```

### Mote Lifecycle

```
proposed → fixed → verified
    ↓         ↓        ↓
rejected  contested  refuted
    ↓
 archived
```

### Session-Based Commands

All mutation commands require `--session TOKEN`:
- `propose`, `approve`, `reject`, `withdraw`
- `vote`, `vote-all`
- `taint`, `add-ref`, `add-assumption`, `add-definition`, `add-dep`
- `claim`, `unclaim`, `done`

Sessionless commands (read-only):
- `init`, `show`, `ready`, `tree`, `status`, `check`, `log`, `config`, `help`

---

## Common Workflows

### Starting Work
```bash
bd ready                              # Find available work
bd show <issue-id>                    # Review issue details
bd update <issue-id> --status=in_progress  # Claim it
```

### Completing Work
```bash
clj -M:test                           # Run all tests
bd close <issue-id>                   # Close the issue
git add . && git commit -m "..."      # Commit changes
git push                              # Push to remote
```

### Solo Development (quorum=1)
```bash
af config set proposal-quorum 1
af config set vote-quorum 1
```

---

## Troubleshooting

### Tests Failing
```bash
# Run specific namespace
clj -M:test --namespace alethfeld.proposal-test

# Check for test isolation issues
clj -M:test --namespace alethfeld.concurrency-test
```

### Beads Issues
```bash
bd doctor                             # Check for sync problems
bd sync --status                      # Check sync status
```

### Git Issues
```bash
git status                            # Check for uncommitted changes
git log --oneline -5                  # Check recent commits
git diff HEAD~1                       # See last commit changes
```

---

## Known Issues

1. **Concurrency tests flaky** (`alethfeld-???`)
   - 3 tests in `concurrency_test.clj` marked `^:flaky`
   - Cause: Test fixture isolation issues
   - Impact: Occasional CI failures, not production bugs

2. **Flaky generate-id-test** (`alethfeld-gp1q`)
   - Occasional UUID collision in 100 UUIDs
   - Very rare, statistically expected

---

## Key Documents

| Document | Purpose |
|----------|---------|
| `docs/IMPLEMENTATION-PLAN.md` | Full v0.2 spec with all step details |
| `docs/TECH-SPEC.md` | v0.1 technical specification |
| `docs/PRD.md` | Product requirements document |
| `CLAUDE.md` | Development conventions |

---

## Environment

- **Language:** Clojure
- **Build tool:** deps.edn with aliases
- **Test runner:** cognitect-labs/test-runner
- **Schema validation:** Malli
- **File format:** EDN
- **VCS:** Git-backed (every CLI operation commits)
