# Alethfeld v0.1 - Master Code Review Report

**Date:** 2026-01-08
**Reviewers:** Three independent AI agents (Linus-style, Code Quality, Test Suite)
**Codebase:** ~5,000 LOC source, ~10,300 LOC tests (15 source files, 24 test files)
**Test Results:** 739 tests, 1904 assertions, 0 failures

---

## Executive Summary

| Aspect | Grade | Summary |
|--------|-------|---------|
| **Architecture** | A- | Clean separation of concerns, pure functions, sound design |
| **Code Quality** | B+ | Good Clojure idioms, minor duplication, some modules too large |
| **Test Coverage** | B | Comprehensive happy paths, missing concurrency/error recovery |
| **Reliability** | B- | Transaction gaps, missing claim timeout, race condition risks |
| **Overall** | **B+** | Production-ready for single-agent use; needs work for multi-agent |

**Bottom Line:** Solid engineering with knowable problems. Safe to ship for small-to-medium proofs with single-agent workflows. Address critical issues before deploying multi-agent concurrent scenarios.

---

## Critical Issues (Must Fix)

### 1. Claim Timeout Not Implemented
**Severity:** HIGH | **All reviewers flagged**

The config specifies `claim-timeout-minutes: 30` but no code enforces it. Two agents could deadlock on the same mote indefinitely.

**Files:**
- `src/alethfeld/store.clj:184` - Config defined
- `src/alethfeld/mote.clj:250-256` - `set-claimed-by` sets timestamp but nothing checks it

**Fix:** Add `check-claim-expired?` function and integrate into `job/workable?`

---

### 2. Job Selection NPE Path
**Severity:** HIGH | **Linus review**

`job-comparator` in `job.clj:159-167` will NPE if a mote has an invalid priority (not in the priority-rank map). Schema validation should prevent this, but motes loaded from disk aren't validated.

**Root cause:** `store/load-mote` (line 61-75) returns motes without schema validation.

**Fix:** Validate motes on load:
```clojure
(when-let [data (io/read-edn file-path)]
  (when (s/valid? s/Mote data) data))
```

---

### 3. Ready Command Bypasses Transaction Layer
**Severity:** HIGH | **Code Quality review**

`cmd-ready` (cmd.clj:232-294) saves motes directly and commits, bypassing `tx/atomic-write!`. This violates ACID semantics - if git commit fails after mote saves, files are left inconsistent.

**Fix:** Wrap claim operations in `tx/atomic-write!`

---

### 4. Transaction Window Race Condition
**Severity:** MEDIUM-HIGH | **Linus review**

In `tx.clj:99-152`, there's a gap between DAG validation passing (line 135) and git commit completing (line 145). If git crashes in between:
- Files are validated and written
- Git hasn't recorded them
- Concurrent agents may see inconsistent state

**Fix:** Document this window explicitly OR validate the git index instead of working tree

---

### 5. No Concurrency Tests
**Severity:** MEDIUM-HIGH | **Test review**

Zero tests for concurrent access: simultaneous claims, voting races, file write conflicts. The system assumes single-threaded access per repo.

**Fix:** Add concurrency test suite covering:
- Two agents claiming same mote
- Vote arriving as quorum is checked
- File write races

---

## Moderate Issues

### 6. cmd.clj is Too Large (1,160 lines)
**All reviewers flagged**

Contains all command handlers. Makes navigation difficult and testing harder.

**Recommendation:** Split into `cmd/init.clj`, `cmd/create.clj`, etc. or by domain.

---

### 7. Duplicated Validation Logic
**Code Quality review**

8+ command functions repeat:
```clojure
(when-not id (throw (ex-info "Mote ID is required" ...)))
(when-not (store/repo-exists? repo-path) (throw ...))
```

**Fix:** Extract `ensure-repo!` and `ensure-id!` helper functions.

---

### 8. Quorum Logic in Two Places
**Code Quality review**

`proposal.clj:18-42` and `verify.clj:19-52` have similar but different quorum implementations.

**Fix:** Extract common patterns to `quorum.clj` module.

---

### 9. Status Transition Not Validated
**Linus review**

Schema allows any valid status, but doesn't enforce the state machine:
```
proposed → fixed → verified/refuted/contested
        → rejected
```

Nothing prevents invalid transitions like `verified → proposed`.

**Fix:** Add `valid-status-transition?` function and call in `set-status`.

---

### 10. Taint vs Status Confusion
**Linus & Code Quality reviews**

System uses both `:status` (lifecycle) and `:taint` (work flags). The mapping is implicit and scattered across `job.clj`, `proposal.clj`, and `verify.clj`.

**Consider:** Derive taints from status to reduce state explosion.

---

## Minor Issues

### 11. Prompt Rendering Bug
`prompt.clj:86` has mismatched parentheses in `format-proposed-children`. Never called in practice (dead code path).

### 12. DAG Cycle Detection Double-Appends
`dag.clj:111` returns cycle path with neighbor appended twice. Functional but confusing.

### 13. ID Generation Flaky for Tests
`mote.clj:9-15` - `generate-id` uses timestamp + random. Tests can collide. Make injectable.

### 14. Git Error Handling Inconsistent
Some operations use `:check false`, requiring manual exit code checking. Use exceptions consistently.

### 15. Dead Code
`job.clj:204` has TODO placeholder that's never reached.

---

## What's Done Right

### Architecture
- **Schema-first approach** with Malli - makes refactoring safe
- **Pure functions** for core logic (DAG, job selection, ID manipulation)
- **Clean separation**: schema → mote → dag → job → store → git → tx → cmd
- **Git as source of truth** - clever use of git's ACID semantics

### Code Quality
- **Functional programming** done correctly
- **Immutable data** everywhere it matters
- **Clear module responsibilities**
- **Good docstrings** explaining intent

### Testing
- **739 tests, 100% pass rate**
- **Excellent fixtures** with proper cleanup
- **Good boundary testing** for happy paths
- **Integration tests** for full workflows

---

## Test Coverage Gaps

| Gap | Priority | Description |
|-----|----------|-------------|
| **Concurrency** | Critical | Zero tests for parallel agents |
| **Error Recovery** | High | Git failures, corrupted files, partial writes |
| **cmd.clj Errors** | High | Large module relies on integration tests |
| **Boundary Stress** | Medium | Large motes, deep nesting (20+ levels) |
| **State Transitions** | Medium | Invalid transitions not tested |
| **CLI Parsing** | Low | Argument edge cases, help text |

### Recommended New Test Files
1. `test/alethfeld/concurrency_test.clj` - Parallel access scenarios
2. `test/alethfeld/recovery_test.clj` - Error/corruption handling
3. `test/alethfeld/cmd/error_test.clj` - Command error paths
4. `test/alethfeld/stress_test.clj` - Large data, deep nesting

---

## Efficiency Concerns

### Load-All-Motes Called Multiple Times
`store/load-all-motes` reads every mote from disk. Called in cmd-create, cmd-ready, cmd-check. O(n) file reads per command.

**Impact:** Low for <1000 motes. Consider caching for larger proofs.

### Snapshot-Based Rollback
`tx.clj` loads all motes into memory before transactions. 10,000 motes × 2KB = 20MB memory.

**Alternative:** Use `git reset --hard HEAD` for rollback instead of in-memory snapshots.

---

## Recommended Action Plan

### Phase 1: Critical Fixes (Before Multi-Agent Use)
1. ✅ Implement claim timeout checking
2. ✅ Add mote validation on load
3. ✅ Fix cmd-ready to use transaction layer
4. ✅ Add concurrency test suite
5. ✅ Document transaction semantics

### Phase 2: Code Health (Next Release)
1. Split cmd.clj into submodules
2. Extract common validation helpers
3. Consolidate quorum logic
4. Add status transition validation
5. Expand error path tests

### Phase 3: Polish (Ongoing)
1. Remove dead code (TODO in job.clj)
2. Make ID generation injectable
3. Add stress tests for scale
4. Improve error messages
5. CLI/help text tests

---

## Issue Tracking

The following beads issues should be created:

| ID | Title | Priority | Type |
|----|-------|----------|------|
| - | Implement claim timeout enforcement | P1 | bug |
| - | Add mote schema validation on load | P1 | bug |
| - | Fix cmd-ready to use tx/atomic-write | P1 | bug |
| - | Add concurrency test suite | P1 | task |
| - | Document transaction window semantics | P2 | docs |
| - | Split cmd.clj into submodules | P2 | refactor |
| - | Extract validation helpers (ensure-repo!, ensure-id!) | P2 | refactor |
| - | Consolidate quorum logic | P2 | refactor |
| - | Add status transition validation | P2 | feature |
| - | Expand command error path tests | P2 | task |
| - | Add stress/boundary tests | P3 | task |
| - | Fix flaky ID generation for tests | P3 | bug |

---

## Conclusion

Alethfeld demonstrates **solid software engineering**. The architecture is sound, the code is functional and idiomatic, and the test suite is comprehensive for happy paths.

**Ship it** for single-agent proof verification on small-to-medium proofs.

**Before multi-agent deployment:**
- Fix claim timeout (deadlock risk)
- Fix transaction layer usage (ACID violation)
- Add concurrency tests (unknown unknowns)

The codebase will scale well with the Phase 2 refactoring. The identified issues are all fixable without major architectural changes.

**Grade: B+** - Good foundation with room for refinement.

---

*Generated by three independent AI code review agents on 2026-01-08*
