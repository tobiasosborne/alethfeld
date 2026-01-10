# Alethfeld UX Issues Implementation Plan

**Date:** 2026-01-10
**Based on:** UX reviews from sqrt(2) and Dobinski proofs

---

## Executive Summary

Two independent UX reviews identified critical issues with Alethfeld v0.2.0:
1. Three broken commands (`af claim`, `af sessions`, `af workflow`)
2. Non-deterministic job assignment (can't request specific motes)
3. Long session tokens (73 characters)
4. Multi-agent race conditions during parallel subagent work

This plan addresses all issues in priority order.

---

## Issue Analysis

### Critical Bugs (Must Fix)

| Bug | Command | Error | Impact |
|-----|---------|-------|--------|
| B1 | `af claim` | ClassCastException | Core functionality broken |
| B2 | `af sessions` | AssertionError (distinct short-opts) | Can't list active sessions |
| B3 | `af workflow` | Resource loading fails | No workflow documentation |

### High-Priority UX Issues

| Issue | Problem | User Impact |
|-------|---------|-------------|
| U1 | Non-deterministic job assignment | Parallel agents get wrong motes |
| U2 | Long session tokens (73 chars) | Error-prone, tedious to copy |
| U3 | No mote targeting | Can't orchestrate parallel agents |

---

## Implementation Plan

### Phase 1: Fix Broken Commands (Critical)

#### 1.1 Fix `af claim` (ClassCastException)

**Location:** `src/alethfeld/cli.clj:486-496`

**Root Cause:** The `deprecated-agent-option` function returns a vector that may cause nested vector structure in options list.

**Fix:** Ensure proper flattening of options list.

```clojure
;; Current (line 495):
(deprecated-agent-option "Agent name")

;; If nested, wrap with vec or use into:
;; The issue may actually be elsewhere in how options are processed
```

**Files to check:**
- `src/alethfeld/cli.clj` - command definition
- `src/alethfeld/cmd/claim.clj` - implementation (if exists)

**Verification:** `af claim 1 --name test --role verifier` should not throw

---

#### 1.2 Fix `af sessions` (AssertionError)

**Location:** `src/alethfeld/cli.clj:591-593`

**Root Cause:** `-v` short option for `--verbose` conflicts with global `-v` for `--version`.

**Fix:** Remove or change the short option:

```clojure
;; Current:
"sessions" {:options [["-v" "--verbose" "Show additional session details"]]}

;; Fixed:
"sessions" {:options [[nil "--verbose" "Show additional session details"]]}
```

**Verification:** `af sessions` should list active sessions without error

---

#### 1.3 Fix `af workflow` (FileNotFoundException)

**Location:** `src/alethfeld/cmd/workflow.clj:19-23`

**Root Cause:** `io/resource` returns `nil` for files not on classpath; `slurp nil` throws NPE which is caught, but fallback path may fail if CWD isn't project root.

**Fix:** Use repo-relative path with proper base:

```clojure
;; Current:
(slurp (io/resource workflow-path))

;; Fixed - use alethfeld context:
(let [repo-path (:repo-path context)
      workflow-path (str repo-path "/prompts/workflow.md")]
  (slurp workflow-path))
```

**Alternative:** Add `resources/` to classpath and move prompts there.

**Verification:** `af workflow` should display workflow documentation

---

### Phase 2: Session Token UX (High Priority)

#### 2.1 Document Existing Aliases

The codebase already supports:
- `@current` / `@last` aliases (resolve to most recent session)
- `AF_SESSION` environment variable
- Auto-inference when agent has exactly 1 session

**Action:** Document these in help output and error messages.

**Files:**
- `src/alethfeld/cmd/core.clj` - error message templates
- `prompts/*.md` - role prompts should mention @current

---

#### 2.2 Short Session Display

Display only first 8 characters of session ID with `...` in outputs.

**Example:**
```
Session: 4329b7a5... (use @current in commands)
```

**Files:**
- `src/alethfeld/cmd/core.clj` - output formatting

---

### Phase 3: Mote Targeting (High Priority)

#### 3.1 Add `--mote` Flag to `af ready`

**Location:** `src/alethfeld/cli.clj` (ready command options)

**New Option:**
```clojure
["-m" "--mote ID" "Request specific mote (optional)"]
```

**Implementation in `src/alethfeld/cmd/ready.clj`:**
1. If `--mote` provided, validate mote exists and is workable
2. If mote is already claimed, suggest alternatives:
   ```
   Mote 1.3 is claimed by 'agent-x'.

   Alternative motes needing verifier work:
     [1] mote 1.4 | p1 | d2
     [2] mote 1.5 | p2 | d1

   Claim: af ready --name <you> --mote 1.4
   ```
3. Filter job candidates to only that mote
4. Derive role from mote's taint flags
5. Proceed with normal claim flow

**Changes to `src/alethfeld/job.clj`:**
Add `:mote-id` option to `select-jobs`:
```clojure
(when-let [target-mote (:mote-id options)]
  (filter #(= target-mote (:id %)) candidates))
```

**Verification:** `af ready --name agent --mote 1.3` claims mote 1.3

---

#### 3.2 Enhanced Job Listing

When listing jobs without claiming, show mote IDs prominently:

```
Available jobs:
  [1] mote 1.2 | verifier | p0 | d2
  [2] mote 1.3 | advisor | p1 | d1

Claim: af ready --name <you> --mote 1.2
```

**Files:**
- `src/alethfeld/cmd/ready.clj` - list output formatting

---

### Phase 4: Multi-Agent Safety (Medium Priority)

The current reservation system (Layer 3-4) already prevents race conditions, but the UX around it is poor.

#### 4.1 Improve Reservation Workflow Documentation

Add to `af ready --help`:
```
For orchestrators coordinating multiple agents:
  af ready --reserve --role verifier  # Reserve without claiming
  af ready --name X --claim-reservation TOKEN  # Agent claims reservation
```

#### 4.2 Session Cleanup on Startup

Ensure `af ready` calls `cleanup-stale-sessions!` before listing.

**Location:** `src/alethfeld/cmd/ready.clj`

---

## Files to Modify

| File | Changes | Priority |
|------|---------|----------|
| `src/alethfeld/cli.clj` | Fix B2 (sessions -v), add --mote to ready | Critical |
| `src/alethfeld/cmd/workflow.clj` | Fix B3 (path resolution) | Critical |
| `src/alethfeld/cmd/claim.clj` or equivalent | Fix B1 (ClassCastException) | Critical |
| `src/alethfeld/cmd/ready.clj` | Add --mote handling, improve list output | High |
| `src/alethfeld/job.clj` | Add :mote-id filter option | High |
| `src/alethfeld/cmd/core.clj` | Document @current alias in outputs | Medium |
| `prompts/*.md` | Mention @current in role prompts | Low |

---

## Verification Plan

### Bug Fixes

```bash
# B1: af claim should work
af claim 1 --name test --role verifier

# B2: af sessions should work
af sessions
af sessions --verbose

# B3: af workflow should work
af workflow
```

### UX Improvements

```bash
# Mote targeting
af ready                           # List available jobs with mote IDs
af ready --name agent --mote 1.3   # Claim specific mote

# Session aliases (already implemented, verify works)
export AF_SESSION=@current
af vote 1.1 --for
```

### Multi-Agent Test

1. Initialize proof: `af init && af create --root --claim "Test"`
2. Spawn 3 parallel agents with different `--mote` targets
3. Verify no race conditions or duplicate claims

---

## Estimated Scope

| Phase | Effort | Lines Changed |
|-------|--------|---------------|
| Phase 1 (Bugs) | ~1 hour | ~30 lines |
| Phase 2 (Session UX) | ~30 min | ~20 lines |
| Phase 3 (Mote Targeting) | ~2 hours | ~80 lines |
| Phase 4 (Docs) | ~30 min | ~40 lines |
| **Total** | **~4 hours** | **~170 lines** |

---

## User Decisions

1. **Priority order:** Fix all 3 bugs first, then move to UX improvements
2. **Mote targeting semantics:** If `--mote X` is claimed, show error but suggest alternative motes with same role

---

## Implementation Order

### Step 1: Fix `af sessions` (5 min)
- Edit `cli.clj:593` - change `-v` to `nil`
- Test: `af sessions` works

### Step 2: Fix `af workflow` (15 min)
- Edit `cmd/workflow.clj:19-23` - use context repo-path for file resolution
- Test: `af workflow` displays documentation

### Step 3: Fix `af claim` (30 min)
- Investigate exact cause of ClassCastException
- Fix options vector structure or implementation
- Test: `af claim 1 --name test --role verifier` works

### Step 4: Add `--mote` flag to ready (1-2 hours)
- Add option to `cli.clj` ready command
- Add `:mote-id` filter to `job.clj` select-jobs
- Implement mote validation and alternative suggestions in `cmd/ready.clj`
- Test: `af ready --name agent --mote 1.3` claims mote 1.3

### Step 5: Document session aliases (30 min)
- Update prompts to mention `@current`
- Add hints to error messages about `AF_SESSION`
- Test: Help and error messages show session shortcuts

---

## Success Criteria

After implementation:
- All 3 broken commands work (`af claim`, `af sessions`, `af workflow`)
- Agents can request specific motes: `af ready --name X --mote 1.3`
- When requested mote is claimed, tool suggests alternatives
- Session aliases are documented in relevant outputs
