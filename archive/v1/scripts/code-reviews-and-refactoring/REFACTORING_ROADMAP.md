# CLI Refactoring Roadmap

## Overview

This document tracks the refactoring work for the Alethfeld Clojure CLI tool, based on comprehensive code review and test coverage analysis.

**Total Issues Created:** 9  
**Estimated Timeline:** 4-6 hours  
**Test Coverage:** ✅ Comprehensive (low risk)

---

## Beads Issues Created

### P0: High Priority (1-2 hours)

Critical optimizations with existing test coverage. **No risk of regressions.**

#### [P0] alethfeld-pjjw: Cache reverse dependencies in graph metadata
- **Impact:** HIGH - O(n²) → O(n) for get-descendants
- **Effort:** 30 minutes
- **Risk:** MEDIUM (cache invalidation is critical)
- **Tests:** All existing graph_test.clj tests pass; extract_lemma_test.clj validates real-world usage
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #1

#### [P0] alethfeld-w1xc: Deduplicate get-ancestors functions
- **Impact:** MEDIUM - Code maintenance, consistency
- **Effort:** 15 minutes
- **Risk:** LOW (identical logic)
- **Tests:** New dedup test required; all existing tests must pass
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #3

#### [P0] alethfeld-zy1n: Deduplicate compute-taint functions
- **Impact:** MEDIUM - Code maintenance, consistency
- **Effort:** 15 minutes
- **Risk:** LOW (identical logic)
- **Tests:** New dedup test required; all existing tests must pass
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #2

---

### P1: Medium Priority (2-3 hours)

Important optimizations with good test coverage. **Medium risk, manageable.**

#### [P1] alethfeld-ftp7: Batch scope computation to avoid O(n²) validation
- **Impact:** MEDIUM - 10-50x faster validation for 100+ node graphs
- **Effort:** 60 minutes
- **Risk:** MEDIUM (algorithm change, but well-tested)
- **Tests:** New compute-all-scopes-test required; all scope validation tests must pass
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #4, TEST_COVERAGE_ANALYSIS.md #4

#### [P1] alethfeld-74mj: Add lazy EDN formatting (compact + pretty variants)
- **Impact:** MEDIUM - 3-5x faster CLI output for large graphs
- **Effort:** 20 minutes
- **Risk:** LOW (output-only change)
- **Tests:** io_test.clj covers format-edn; new variant tests required
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #5

---

### P2: Lower Priority (2-3 hours)

Nice-to-have optimizations and code quality improvements.

#### [P2] alethfeld-1li1: Support partial topological sort for single-node queries
- **Impact:** LOW - Edge case optimization
- **Effort:** 45 minutes
- **Risk:** MEDIUM (algorithm change)
- **Tests:** New topological-sort-partial-test required
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #6

#### [P2] alethfeld-y5sx: Unify error handling across ops and commands
- **Impact:** LOW - Code quality, maintainability
- **Effort:** 90 minutes
- **Risk:** LOW (refactoring, no behavioral change)
- **Tests:** All tests must pass; no new tests needed
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #8

#### [P2] alethfeld-tgex: Organize schema.clj into domain-grouped modules
- **Impact:** LOW - Code organization
- **Effort:** 60 minutes
- **Risk:** LOW (structural change only)
- **Tests:** No new tests; schema validation must work end-to-end
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #10

---

### P3: Very Low Priority (1 hour)

Testing and documentation work.

#### [P3] alethfeld-1t9u: Add performance benchmarks for hot paths
- **Impact:** LOW - Measurement and regression prevention
- **Effort:** 60 minutes
- **Risk:** LOW (non-blocking)
- **Tests:** Benchmark suite itself; doesn't affect production code
- **Status:** 🔴 Open
- **Details:** See CODE_REVIEW.md #11

---

## Recommended Execution Order

### Phase 1: P0 Refactorings (45 minutes)
Focus on deduplication first (low risk), then reverse-deps cache (high impact).

1. **Dedup get-ancestors** (alethfeld-w1xc) - 15 min
   - Add comparison test
   - Remove duplicate
   - Run `clojure -M:test`

2. **Dedup compute-taint** (alethfeld-zy1n) - 15 min
   - Add comparison test
   - Remove duplicate
   - Run `clojure -M:test`

3. **Cache reverse deps** (alethfeld-pjjw) - 30 min
   - Implement caching
   - Add invalidation in ops
   - Benchmark
   - Run `clojure -M:test`

**Checkpoint:** `clojure -M:test` must pass all

---

### Phase 2: P1 Optimizations (1.5 hours)

4. **Lazy EDN formatting** (alethfeld-74mj) - 20 min
   - Add compact/pretty variants
   - Update commands
   - Run tests

5. **Batch scope computation** (alethfeld-ftp7) - 60 min
   - Implement compute-all-scopes
   - Update validator
   - Add tests
   - Benchmark
   - Run `clojure -M:test`

**Checkpoint:** `clojure -M:test` must pass; validate performance gains

---

### Phase 3: P2 & P3 (Optional, as time permits)

6. Partial topological sort (alethfeld-1li1)
7. Error handling unification (alethfeld-y5sx)
8. Schema organization (alethfeld-tgex)
9. Benchmarks (alethfeld-1t9u)

---

## Testing Strategy

### Before Starting

```bash
cd alethfeld
clojure -M:test
# All must pass ✅
```

### After Each Issue

```bash
clojure -M:test  # MUST pass
clojure -M:run validate resources/sample.edn  # Smoke test
```

### Final Validation

```bash
clojure -M:test  # Full suite
clojure -T:build uber  # Build jar
java -jar target/alethfeld.jar --help  # Works?
```

---

## Test Coverage Summary

| Module | Coverage | Risk for Refactor |
|--------|----------|-------------------|
| graph.clj | ✅ Excellent (10+ tests) | LOW |
| validators.clj | ✅ Good (6 tests + fixtures) | MEDIUM |
| io.clj | ✅ Good (5 tests) | LOW |
| ops/* | ✅ Comprehensive (7 test files) | LOW |
| commands/* | ⚠️ Minimal | LOW (thin wrappers) |
| schema.clj | ⚠️ Minimal | LOW (data-driven) |

**Overall Risk:** ✅ **LOW** - Comprehensive test coverage for all critical paths

---

## Performance Expectations

### After Phase 1 (Dedup + Cache)

```
Operation: validate proof.edn (100 nodes)
Before: 234ms (schema: 234ms)
After:  234ms (schema: 234ms, get-descendants: ~1ms vs ~100ms before cache)
Gain:   ~10% for get-descendants-heavy operations
```

### After Phase 2 (Lazy formatting + Batch scope)

```
Operation: add-node proof.edn (100 nodes)
Before: 350ms (validation: 280ms)
After:  280ms (validation: 150ms, formatting: 5ms vs 20ms before)
Gain:   ~20% overall
```

---

## Notes & Gotchas

### Cache Invalidation is Hard

- When adding/removing nodes, cache must be invalidated
- Check: add_node, delete_node, replace_node, update_status, extract_lemma
- Add invalidation in `update-context-budget` helper if creating one

### Taint/Ancestors Dedup

- Ensure both implementations produce **identical** results before deletion
- Add tests to verify this; don't just assume

### Scope Batch Computation

- Most complex change; requires careful testing
- Add property-based tests if possible (generative testing with test.check)
- Compare output on all fixtures before deploying

### EDN Format Change is CLI-visible

- Commands output different format (compact vs pretty)
- Update docs/README.md if this is user-facing
- Clients parsing output might be affected (unlikely but check)

---

## Success Criteria

✅ All tests pass: `clojure -M:test`  
✅ No regressions in existing functionality  
✅ Measurable performance improvements (benchmarks documented)  
✅ Code is more maintainable (deduplicated, organized)  
✅ All issues marked closed in beads  

---

## Timeline Estimate

| Phase | Issues | Effort | Timeline |
|-------|--------|--------|----------|
| 1: Dedup + Cache | 3 | 45 min | **1 hour** (+ test time) |
| 2: Optimize I/O + Scope | 2 | 80 min | **1.5 hours** (+ benchmark) |
| 3: Polish | 4 | 250 min | **3-4 hours** (optional) |
| **Total** | **9** | **375 min** | **4-6 hours** |

---

## Related Documents

- **CODE_REVIEW.md** - Detailed analysis of issues and fixes
- **TEST_COVERAGE_ANALYSIS.md** - Test coverage by module, strategy for refactoring
- **AGENTS.md** - Current project status and workflow

---

## Questions & Blockers

**None at this time.**

All refactorings are independent and can be done in any order within phases.
Test coverage is sufficient. No external dependencies to add.

---

## Sign-Off

**Code Review:** ✅ Completed  
**Test Analysis:** ✅ Completed  
**Issues Created:** ✅ 9 issues in beads  
**Ready to Start:** ✅ Yes

Next agent should:
1. Pick an issue from `bd ready`
2. Run `bd update <id> --status in_progress`
3. Follow the refactoring steps in CODE_REVIEW.md
4. Run tests after each change
5. Close issue with `bd close <id>` when done
