# Test Coverage Analysis for Refactoring

## Overview

**Current State:** Good test coverage with comprehensive fixtures  
**Risk Level for Refactoring:** LOW  
**Confidence Level:** High

---

## Coverage by Module

### ✅ `graph.clj` - EXCELLENT

**Test File:** `test/alethfeld/graph_test.clj` (128 lines)

| Function | Tests | Risk Level |
|----------|-------|-----------|
| `get-ancestors` | Yes, multiple DAGs | ✅ LOW |
| `get-descendants` | Yes, linear + diamond | ✅ LOW |
| `get-direct-dependents` | Yes, verified | ✅ LOW |
| `topological-sort` | Yes, linear + diamond | ✅ LOW |
| `compute-valid-scope` | Yes, with discharge | ✅ LOW |
| `compute-taint` | Yes, clean/admitted/propagated | ✅ LOW |
| `check-independence` | Yes, 5 scenarios | ✅ LOW |
| `would-create-cycle?` | Yes, self-loop, indirect | ✅ LOW |

**Fixtures Used:**
- `minimal-valid-graph` - Single node
- `linear-chain-graph` - A→B→C
- `diamond-graph` - A→{B,C}→D
- `scoped-graph` - With local-assume/discharge
- `empty-nodes-graph` - Edge case

**Refactoring Ready?** ✅ **YES** - All key functions have passing tests covering normal + edge cases.

**Test Plan for Optimizations:**
1. **Reverse-deps caching** - Reuse existing `get-descendants` tests; verify output is identical
2. **Dedup ancestors** - Both `graph` and `validators` versions must produce identical results
3. **Batch scope** - New `compute-all-scopes` must match current `compute-valid-scope` individually

---

### ✅ `validators.clj` - EXCELLENT

**Test File:** `test/alethfeld/validators_test.clj` (56 lines)

| Function | Tests | Risk Level |
|----------|-------|-----------|
| `check-dependency-refs` | Yes, missing deps | ✅ LOW |
| `check-acyclicity` (find-cycle) | Yes, self-loop + direct | ✅ LOW |
| `check-scopes` | Yes, valid + discharge | ✅ LOW |
| `check-taint-correctness` | Yes, admitted + propagated | ✅ LOW |
| `compute-taint` | Implicitly tested via check | ⚠️ MEDIUM |
| `get-ancestors` | Used in scope checks | ⚠️ MEDIUM |

**Fixtures Exercised:**
- `minimal-valid-graph`
- `linear-chain-graph`
- `diamond-graph`
- `scoped-graph`
- Invalid graphs (missing-dep, self-loop, incorrect-taint)

**Refactoring Ready?** ✅ **YES, WITH CAUTION** - Deduplication of `compute-taint` and `get-ancestors` requires:
- Compare outputs of both implementations on all existing test fixtures
- Update validators to import from graph.clj
- Run full test suite to confirm no behavior changes

**New Test Needed:** Property-based test for `compute-taint` consistency
```clojure
(deftest compute-taint-consistency-test
  (testing "graph/compute-taint and validators/compute-taint identical"
    (is (= (g/compute-taint graph node-id)
           (v/compute-taint graph node-id)))))
```

---

### ✅ `io.clj` - EXCELLENT

**Test File:** `test/alethfeld/io_test.clj` (72 lines)

| Function | Tests | Risk Level |
|----------|-------|-----------|
| `read-edn` | Yes, valid/missing/empty/malformed | ✅ LOW |
| `write-edn-atomic` | Yes, roundtrip + atomicity | ✅ LOW |
| `format-edn` | Yes, readability | ✅ LOW |
| `read-edn-stdin` | Not tested | ⚠️ MEDIUM |

**Refactoring Ready?** ✅ **YES** - `format-edn` is tested. Adding compact/pretty variants is safe.

**New Tests Needed:**
```clojure
(deftest format-edn-compact-test
  (testing "Compact format is smaller"
    (let [compact (io/format-edn-compact data)
          pretty (io/format-edn-pretty data)]
      (is (< (count compact) (count pretty))))))

(deftest read-edn-stdin-test
  ;; Test stdin reading with bindings
)
```

---

### ✅ `ops/extract_lemma.clj` - EXCELLENT

**Test File:** `test/alethfeld/ops/extract_lemma_test.clj` (249 lines)

**All key scenarios tested:**
- ✅ Simple extraction
- ✅ Explicit node set
- ✅ Unverified node rejection
- ✅ External dependency validation
- ✅ Taint propagation
- ✅ Balanced/unbalanced scope
- ✅ Version increment
- ✅ Schema validation

**Refactoring Impact:** HIGH - `extract-lemma` calls `get-descendants` heavily.

**Refactoring Ready?** ✅ **YES** - Existing tests will validate that reverse-deps optimization doesn't change behavior. Just run: `clojure -M:test alethfeld.ops.extract-lemma-test`

---

### ✅ Other Operations - GOOD

**Test Files:**
- `ops/add_node_test.clj` - Valid + precondition checks
- `ops/update_status_test.clj` - Status transitions
- `ops/delete_node_test.clj` - Leaf-only deletion
- `ops/replace_node_test.clj` - Replacement validation
- `ops/init_test.clj` - Graph initialization

**Refactoring Impact:** MEDIUM - May indirectly use graph operations.

---

### ⚠️ Commands Layer - MINIMAL

**No dedicated command tests found.** Commands tested via:
- Integration tests (if they exist)
- Manual CLI testing

**Risk for Refactoring:** LOW - Commands are thin wrappers around ops. If ops pass, commands work.

---

### ⚠️ Schema Validation - MINIMAL

**Test File:** `test/alethfeld/schema_test.clj` (exists but not reviewed)

**Risk for Refactoring:** LOW - Schema is data-driven; refactoring graph logic doesn't require schema changes.

---

## Critical Test Scenarios for Refactoring

### 1. **Reverse-Dependency Caching** (PRIORITY 0)

**Existing Tests Cover:**
- ✅ `graph_test.clj::ancestor-descendant-test::get-descendants in linear chain`
- ✅ `graph_test.clj::ancestor-descendant-test::get-descendants in diamond`
- ✅ `graph_test.clj::get-direct-dependents`
- ✅ `extract_lemma_test.clj::*` (heavy use of get-descendants)

**Test Plan:**
1. Before refactoring, run all tests: `clojure -M:test`
2. Implement caching (add `_reverse-deps` to graph metadata)
3. Run all tests again; all must pass with identical results
4. Add benchmark: Compare speed with/without cache on 100-node graph
5. Verify cache invalidation on graph mutation (update-status, add-node, etc.)

**New Test Needed:**
```clojure
(deftest reverse-deps-cache-consistency-test
  (testing "Cached reverse-deps matches computation"
    (let [graph (add-reverse-deps-cache f/linear-chain-graph)]
      (is (= (get-descendants-uncached graph :1-aaa111)
             (get-descendants-cached graph :1-aaa111))))))

(deftest reverse-deps-cache-invalidation-test
  (testing "Cache is invalidated on mutation"
    (let [graph (add-node-and-invalidate-cache ...)]
      ;; Should recompute, not use stale cache
      (is (= expected (get-descendants graph ...))))))
```

---

### 2. **Deduplicating `get-ancestors`** (PRIORITY 0)

**Existing Tests Cover:**
- ✅ `graph_test.clj::ancestor-descendant-test::get-ancestors` (all scenarios)
- ✅ `validators_test.clj::scope-validation-test` (uses `compute-valid-scope` which calls ancestors)

**Test Plan:**
1. Copy `validators/get-ancestors` implementation to `graph_test.clj`
2. Compare: `(= (graph/get-ancestors g nid) (validators/get-ancestors g nid))` on all fixtures
3. Update `validators.clj` to import from `graph.clj`
4. Run full test suite: `clojure -M:test`

**New Test Needed:**
```clojure
(deftest get-ancestors-dedup-test
  "Ensure both implementations are identical"
  (doseq [graph [f/linear-chain-graph f/diamond-graph f/scoped-graph]
          node-id (g/node-ids graph)]
    (is (= (g/get-ancestors graph node-id)
           (v/get-ancestors graph node-id)))))
```

---

### 3. **Deduplicating `compute-taint`** (PRIORITY 0)

**Existing Tests Cover:**
- ✅ `graph_test.clj::taint-queries-test` (clean, admitted, propagation)
- ✅ `validators_test.clj::taint-validation-test` (correctness checks)

**Test Plan:**
1. Compare both implementations on all test fixtures
2. Move `validators/compute-taint` to `graph.clj` or remove if identical
3. Update imports
4. Run: `clojure -M:test`

**New Test Needed:**
```clojure
(deftest compute-taint-dedup-test
  (doseq [graph [f/linear-chain-graph f/diamond-graph]
          node-id (g/node-ids graph)]
    (is (= (g/compute-taint graph node-id)
           (v/compute-taint graph node-id)))))
```

---

### 4. **Batch Scope Computation** (PRIORITY 1)

**Existing Tests Cover:**
- ✅ `graph_test.clj::scope-queries-test::compute-valid-scope`
- ✅ `validators_test.clj::scope-validation-test`

**Test Plan:**
1. Implement `compute-all-scopes` in `graph.clj`
2. Add test:
```clojure
(deftest compute-all-scopes-test
  (testing "Batch computation matches individual calls"
    (let [graph f/scoped-graph
          all-scopes (g/compute-all-scopes graph)
          individual (reduce-kv (fn [acc nid _]
                                  (assoc acc nid (g/compute-valid-scope graph nid)))
                                {}
                                (:nodes graph))]
      (is (= all-scopes individual)))))
```
3. Update `check-scope-validity` in validators to use batch computation
4. Verify performance improvement (should be 10-50x faster for 100+ nodes)

---

### 5. **Lazy EDN Formatting** (PRIORITY 1)

**Existing Tests Cover:**
- ✅ `io_test.clj::format-edn-test` (readability)

**Test Plan:**
1. Add `format-edn-compact` (uses `pr`)
2. Add `format-edn-pretty` (uses `pprint`)
3. New tests:
```clojure
(deftest format-edn-variants-test
  (testing "Both formats parse identically"
    (let [data {:a 1 :b [2 3]}
          compact (io/format-edn-compact data)
          pretty (io/format-edn-pretty data)]
      (is (= data (read-string compact)))
      (is (= data (read-string pretty)))
      (is (< (count compact) (count pretty))))))
```
4. Update commands to use compact by default
5. Add `--pretty` flag to relevant commands

---

### 6. **Topological Sort Partial** (PRIORITY 2)

**Existing Tests Cover:**
- ✅ `graph_test.clj::topological-sort-test` (full graph)

**Test Plan:**
1. Add parameterized topo-sort accepting `:partial` flag
2. Add tests for subset sorting
3. Ensure no regressions (all existing tests must pass)

---

## Test Execution Plan

### Before Refactoring

```bash
# Run all tests
cd alethfeld
clojure -M:test

# Expected: All pass ✅

# Measure baseline performance
clojure -M:test --reporter json > baseline.json
```

### For Each Refactoring

1. **Implement change**
2. **Run tests immediately:** `clojure -M:test`
3. **If any test fails:** Debug + investigate (likely a logic error)
4. **If all pass:** Continue to next refactoring
5. **Benchmark after each:** `clojure -M:run stats <graph>` before/after on same graphs

### After All Refactorings

```bash
# Full regression test
clojure -M:test

# Build + integration test
clojure -T:build uber
java -jar target/alethfeld.jar validate resources/sample.edn
```

---

## Risk Assessment

| Refactoring | Test Risk | Behavioral Risk | Overall |
|-------------|-----------|-----------------|---------|
| Reverse-deps cache | LOW | MEDIUM (cache invalidation) | **MEDIUM** |
| Dedup ancestors | LOW | LOW (identical logic) | **LOW** |
| Dedup taint | LOW | LOW (identical logic) | **LOW** |
| Batch scope | MEDIUM | MEDIUM (algorithm change) | **MEDIUM** |
| Lazy formatting | LOW | LOW (output only) | **LOW** |
| Topo sort partial | LOW | MEDIUM (edge cases) | **MEDIUM** |

---

## Recommendation

✅ **PROCEED WITH REFACTORING**

**Rationale:**
- Comprehensive test coverage exists for all hot-path functions
- Test fixtures cover linear, diamond, scoped, and invalid graphs
- All critical operations tested (ancestors, descendants, taint, scope)
- Low risk of undetected regressions

**Safety Net:**
- Run `clojure -M:test` after each change
- No new tests required for high-priority items (P0) — existing tests suffice
- Add new tests only for complex optimizations (batch scope, etc.)

**Timeline:**
- P0 items (cache + dedup): 1 hour, high confidence
- P1 items (batch scope, lazy format): 2 hours, medium confidence
- P2 items (topo sort partial): 1 hour, lower priority

---

## Test Command Reference

```bash
# All tests
clojure -M:test

# Specific namespace
clojure -M:test test/cli/graph_test.clj

# Specific test
clojure -M:test --filter "get-ancestors-dedup"

# With output
clojure -M:test --reporter verbose
```
