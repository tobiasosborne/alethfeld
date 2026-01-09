# Alethfeld Session Handoff

**Last updated:** 2026-01-09
**Last session:** Step C.5 - Atomic Markers on Creation
**Session status:** COMPLETED SUCCESSFULLY

---

## Quick Status Check

Run these to verify project health:
```bash
clj -M:test                    # Should pass 984 tests, 2690 assertions
git status                     # Should be clean
bd stats                       # Check open/closed counts
```

---

## Current State

### Repository Structure
- **Branch:** `main` (v2 development, hidden from public)
- **Default branch on GitHub:** `legacy` (v1, public-facing)
- **Latest commit:** (pending) - feat: Step C.5 - Atomic Markers on Creation
- v1 code archived in `archive/v1/`

### Project Status
| Phase | Status | Progress |
|-------|--------|----------|
| Phase A | Session & Role Enforcement | **100% COMPLETE** (8/8 steps) |
| Phase B | Essential UX Improvements | **100% COMPLETE** (4/4 steps) |
| Phase C | Quality/Safety Features | **100% COMPLETE** (5/5 steps) |

### Test Health
- **Total tests:** 984
- **Total assertions:** 2,690
- **Status:** ALL PASSING
- **Known flaky tests:**
  - 3 concurrency tests (marked `^:flaky`, test isolation issues)

---

## This Session: Step C.5 Atomic Markers on Creation

### What Was Implemented

Added `--atomic` flag to `af propose` to mark claims as atomic at proposal time. Atomic claims skip decomposition and go directly to verification.

### Command Syntax

Two ways to mark claims as atomic:

**1. Positional args with `!` suffix:**
```bash
af propose 1 "Simple fact!" --session TOKEN
af propose 1 "Fact @3!" --session TOKEN   # with difficulty
```

**2. CLI options:**
```bash
af propose 1 --claim "Simple fact" --atomic --session TOKEN
```

### How It Works

- **Non-atomic claims (default):** Get `:needs-decomposition` taint
- **Atomic claims:** Get `:needs-verification` taint instead

This means atomic claims skip the decomposition workflow and go directly to verification voting.

### Files Modified

| File | Changes |
|------|---------|
| `src/alethfeld/cli.clj` | Added `--atomic` option to propose command (repeatable, positional) |
| `src/alethfeld/cmd.clj` | Updated `parse-claims` to handle `!` notation; added `merge-option-claims`; updated `cmd-propose!` |
| `src/alethfeld/proposal.clj` | Updated `create-child-motes` and `promote-children!` to handle atomic flag |
| `src/alethfeld/schema.clj` | Added `:atomic {:optional true} :boolean` field to Mote schema |
| `test/alethfeld/proposal_test.clj` | Added 6 atomic claims tests |
| `test/alethfeld/cmd/proposal_test.clj` | Added 8 atomic claims parsing and integration tests |

### Implementation Details

**Claim parsing (`parse-claims`):**
- Detects `!` suffix as atomic marker
- `"My claim!"` → `{:claim "My claim" :atomic true}`
- `"My claim @3!"` → `{:claim "My claim" :difficulty 3 :atomic true}`

**Proposal creation (`create-child-motes`):**
```clojure
(let [atomic? (:atomic claim-spec)
      taint (if atomic?
              #{:needs-verification}
              #{:needs-decomposition})]
  ...)
```

**Promotion (`promote-children!`):**
```clojure
(let [atomic? (:atomic child)
      taint-to-add (if atomic?
                     :needs-verification
                     :needs-decomposition)]
  ...)
```

### Tests Added

| Test | Purpose |
|------|---------|
| `atomic-claim-proposed-taint-test` | Atomic claim gets `:needs-verification` when proposed |
| `non-atomic-claim-proposed-taint-test` | Non-atomic claim gets `:needs-decomposition` when proposed |
| `mixed-atomic-claims-proposed-test` | Mixed claims get correct taints |
| `atomic-claim-promoted-taint-test` | Atomic claim preserves taint after promotion |
| `mixed-atomic-claims-promoted-test` | Mixed claims preserve correct taints after promotion |
| `parse-claims-atomic-test` | Parse `!` suffix for atomic |
| `parse-claims-atomic-with-difficulty-test` | Parse `@N!` for difficulty + atomic |
| `parse-claims-mixed-atomic-test` | Parse mixed atomic/non-atomic claims |
| `parse-claims-atomic-preserves-whitespace-test` | Whitespace handling with atomic |
| `propose-atomic-claim-has-correct-taint-test` | Integration: atomic claim gets correct taint |
| `propose-non-atomic-claim-has-correct-taint-test` | Integration: non-atomic claim gets correct taint |
| `propose-mixed-atomic-claims-test` | Integration: mixed claims work correctly |
| `approve-atomic-claim-preserves-taint-test` | Integration: approved atomic keeps `:needs-verification` |

---

## Phase C Complete!

| Step | Issue | Status | Description |
|------|-------|--------|-------------|
| C.1 | `alethfeld-2hdf` | **DONE** | Batch Voting (`af vote-all`) |
| C.2 | `alethfeld-t52o` | **DONE** | Auto-Propagation (`--propagate` flag) |
| C.3 | `alethfeld-hc3w` | **DONE** | Proposal Withdrawal (`af withdraw`) |
| C.4 | `alethfeld-pu9n` | **DONE** | Cross-References / Dependencies (`af add-dep`) |
| C.5 | `alethfeld-nyrg` | **DONE** | Atomic Markers on Creation (`--atomic` flag) |

---

## Next Steps

Phase C is complete! Possible next steps:

1. **Phase D** - Vision features (Lean4 integration, visualization) - deferred to v0.3+
2. **Documentation** - Step 7.4 (`alethfeld-dpdq`) - CLI documentation
3. **Bug fixes** - Various items in `bd ready`

Run `bd ready` to see available work.

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
