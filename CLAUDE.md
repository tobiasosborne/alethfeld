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

### Let Binding Style Guide

- Prefer `some->` or `some->>` over deeply nested `when-let` chains
- Use `as->` when threading needs intermediate bindings
- Destructure maps with `{:keys [a b c]}` when accessing multiple keys
- Use threading macros (`->`, `->>`) for sequential transformations
- Keep `let` bindings flat; avoid nesting lets inside lets
- Extract complex bindings into named helper functions

## Test Conventions

- Test files live in `test/` mirroring `src/` structure
- Namespace naming: `alethfeld.foo` → `alethfeld.foo-test`
- Use `clojure.test` with `deftest`, `testing`, `is`
- Run all tests: `clj -M:test`
- Test runner: cognitect-labs/test-runner

## Known Limitations

### Transaction Race Window

There is a small window (~<100ms) between validation passing and git commit completing where changes are written to disk but not yet recorded in git. See `src/alethfeld/tx.clj` `with-validation` docstring.

**If process crashes during this window:**
- Files on disk are validated and consistent
- Git history does not reflect the changes
- Concurrent agents using `git pull` will not see the changes

**Why this is acceptable for v0.1:**
- Window is typically <100ms for normal operations
- Validated changes are not rolled back (data integrity preserved)
- Manual recovery is straightforward: `git add . && git commit -m 'recovery'`
- Concurrent access is serialized via per-repository locks

**Potential future mitigations:**
- Validate against git index instead of working tree
- Add startup recovery to detect uncommitted validated changes

### FileLock Limitations

The multi-agent safety layer uses OS-level file locks (`java.nio.channels.FileLock`):

- **NFS**: Advisory locks may not work reliably on NFS mounts
- **Same machine only**: FileLock coordinates processes on same machine
- **Git sync required**: Distributed agents must coordinate via git pull/push
- **Windows**: Exclusive locks (no concurrent readers), may differ from POSIX

## Multi-Agent Safety

Alethfeld prevents race conditions in multi-agent deployments via 4 layers:

### Layer 1: OS FileLock (Cross-Process)

`tx.clj` uses a dual-lock strategy:
- **ReentrantLock**: Thread safety within same JVM
- **FileLock**: Cross-process mutex on `.alethfeld/lock`
- Lock wait feedback: "Waiting for repository lock..." after 200ms

### Layer 2: Atomic Claim Flow

`cmd/ready.clj` uses `claim-job-atomic!`:
- Re-checks claim status inside the lock
- Retries on conflict with next candidate
- Session created only after successful claim

### Layer 3: Atomic Reservations

`session.clj` uses `create-reservation-atomic!`:
- Lock file per mote: `.alethfeld/sessions/reservations/lock-{mote-id}.edn`
- `CREATE_NEW` semantics for atomic file creation
- Automatic expiration (default 60 seconds)

### Layer 4: Reservation Filtering

`job.clj` `select-jobs` accepts `:active-reservations`:
- Reserved motes excluded from job candidates
- Prevents duplicate claims during reservation window
