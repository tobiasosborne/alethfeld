# Alethfeld Session Handoff

**Last updated:** 2026-01-09
**Last session:** v0.2 Workflow Refactoring - Planning Session
**Session status:** PLANNING COMPLETE - IMPLEMENTATION NOT STARTED

---

## CRITICAL: Drift Between Plan, Issues, and Codebase

This session made significant changes to the v0.2 plan. There is now **drift** between three sources of truth:

| Source | State | Notes |
|--------|-------|-------|
| **`docs/V02-REVISION-PLAN.md`** | Updated | Rewritten to be internally consistent. **This is the canonical plan.** |
| **Beads issues** | Partially updated | 12 new Phase 7 issues created. Old Phase 1-6 issues may be stale. |
| **Codebase** | Not updated | Still has v0.1 workflow (proposer-first, quorum=2, --atomic flag exists) |

### What Changed in the Plan

The original V02-REVISION-PLAN.md had contradictions:
- Steps 1.3/1.4 added `--atomic` hints, but Phase 7.10 removes `--atomic`
- References to quorum=2 throughout, but Phase 7.4/7.5 change to quorum=1
- Workflow docs showed proposer-first, but Phase 7 implements verifier-first

**Resolution:** Rewrote the document to be consistent:
- Removed old 1.3/1.4 (atomic hints) - now superseded by 7.10
- Updated all quorum references to 1
- Updated all workflow descriptions to verifier-first
- Moved Batch 7 (workflow refactoring) to be implemented FIRST

### Old Beads Issues That May Be Stale

These issues from the old plan may need review/closure:
- `alethfeld-19kq` - "Add --atomic hint to proposer prompt" - **CONTRADICTS** 7.10 (remove --atomic)
- `alethfeld-umt5` - "Contextual --atomic suggestion" - **CONTRADICTS** 7.10 (remove --atomic)
- Any issues referencing quorum=2 need review

### New Beads Issues Created (Phase 7)

| ID | Priority | Title |
|----|----------|-------|
| `alethfeld-j3s7` | P0 | 7.1 Change default taint to :needs-verification |
| `alethfeld-lpiy` | P0 | 7.2 Update proposal taints for verifier-first |
| `alethfeld-b3ze` | P0 | 7.3 Reorder role priorities (verifier first) |
| `alethfeld-wb01` | P1 | 7.4 Change proposal quorum to 1 |
| `alethfeld-6tg2` | P1 | 7.5 Change vote quorum to 1 |
| `alethfeld-u8rl` | P1 | 7.6 Update verifier prompt for decomposition demands |
| `alethfeld-b5wf` | P2 | 7.7 Update verifier CLI output with taint commands |
| `alethfeld-q02u` | P2 | 7.8 Add verifier :taint-remove permission |
| `alethfeld-vi0r` | P2 | 7.9 Update proposer prompt context for verifier-first |
| `alethfeld-o137` | P2 | 7.10 Remove --atomic flag from propose command |
| `alethfeld-quz8` | P3 | 7.11 Add refinement demand to verifier prompt |
| `alethfeld-iqsd` | P0 | 7.12 Update tests for new workflow defaults |

**Dependencies:** `alethfeld-iqsd` (tests) depends on 7.1, 7.2, 7.3, 7.4, 7.5, 7.10

---

## Quick Status Check

Run these to verify project health:
```bash
clj -M:test                    # Should pass ~1098 tests (will FAIL after Phase 7 code changes until 7.12 done)
git status                     # Should be clean
bd stats                       # Check open/closed counts
bd ready                       # See available work (Phase 7 P0 issues should appear first)
```

---

## Current State

### What v0.2 Is Now About

The v0.2 revision is now primarily about a **workflow paradigm shift**:

**Old workflow (v0.1):**
```
New mote → :needs-decomposition → Proposer → Advisor (2 votes) → Children → Verifier
```

**New workflow (v0.2):**
```
New mote → :needs-verification → Verifier → {
  Votes for → Verified
  Votes against → Refuted
  Demands decomposition → :needs-decomposition → Proposer → Advisor (1 vote) → Children → Verifier...
}
```

**Key design decisions:**
1. **Remove `:atomic` flag** - Verifiers decide what needs decomposition
2. **Change quorums to 1** - Single vote to verify/approve (was 2)
3. **Keep prover role** - Verifiers can demand `:needs-refinement`

### Repository Structure
- **Branch:** `main` (v2 development)
- **Default branch on GitHub:** `legacy` (v1, public-facing)

### Test Health (Before Phase 7 Implementation)
- **Total tests:** ~1,098
- **Total assertions:** ~6,520
- **Status:** ALL PASSING
- **Warning:** Tests will fail during Phase 7 implementation until 7.12 (test updates) is complete

---

## This Session: Planning & Issue Creation

### What Was Done

1. **Analyzed the codebase** for workflow refactoring requirements
   - Explored job.clj, mote.clj, proposal.clj, verify.clj, session.clj
   - Identified all locations where taints, quorums, and role priorities are set

2. **Created detailed implementation plan** at `.claude/plans/snoopy-twirling-hamming.md`
   - 12 implementation phases (7.1 - 7.12)
   - File-by-file change specifications
   - Verification plan with manual test script

3. **Clarified design decisions with user:**
   - Remove `--atomic` flag (verifiers decide)
   - Change vote quorum to 1 (was 2)
   - Keep prover role (verifiers can demand refinement)

4. **Updated V02-REVISION-PLAN.md** to be internally consistent
   - Removed contradictory 1.3/1.4 sections
   - Updated all quorum references
   - Updated all workflow descriptions
   - Reordered implementation priority (Batch 7 first)

5. **Created 12 beads issues** for Phase 7 workflow refactoring
   - Set appropriate priorities (P0 for critical, P1-P3 for others)
   - Added dependencies (7.12 tests depends on implementation issues)

### Files Modified

```
docs/V02-REVISION-PLAN.md      - Major rewrite for consistency
handoff.md                     - This file
.beads/                        - 12 new issue files (auto-synced)
```

### No Code Changes Made

This was a **planning session only**. The codebase still has:
- Default taint: `:needs-decomposition` (needs to be `:needs-verification`)
- Role priority: advisor=0, verifier=3 (needs verifier=0)
- Quorums: 2 (needs to be 1)
- `--atomic` flag exists (needs to be removed)

---

## Next Steps

### Immediate Priority: Resolve Drift

Before implementing anything, the next agent should:

1. **Review stale issues:**
   ```bash
   bd show alethfeld-19kq   # --atomic hint - should this be closed?
   bd show alethfeld-umt5   # --atomic suggestion - should this be closed?
   ```

2. **Verify Phase 7 issues are correct:**
   ```bash
   bd list --status=open | grep "7\."
   ```

### Implementation Order

The plan specifies **Batch 7 first** (workflow refactoring), then other batches. Within Batch 7:

1. **P0 Critical (do first):**
   - 7.1 Default taint to :needs-verification (`alethfeld-j3s7`)
   - 7.2 Proposal taints for verifier-first (`alethfeld-lpiy`)
   - 7.3 Reorder role priorities (`alethfeld-b3ze`)
   - 7.12 Update tests (`alethfeld-iqsd`) - **do last in P0, after other P0s**

2. **P1 High:**
   - 7.4 Proposal quorum to 1 (`alethfeld-wb01`)
   - 7.5 Vote quorum to 1 (`alethfeld-6tg2`)
   - 7.6 Verifier prompt for decomposition (`alethfeld-u8rl`)

3. **P2 Medium:**
   - 7.7 Verifier CLI output (`alethfeld-b5wf`)
   - 7.8 Verifier taint-remove permission (`alethfeld-q02u`)
   - 7.9 Proposer prompt context (`alethfeld-vi0r`)
   - 7.10 Remove --atomic flag (`alethfeld-o137`)

4. **P3 Low:**
   - 7.11 Refinement demand option (`alethfeld-quz8`)

### Test Strategy

**Warning:** Tests will break during implementation.

Recommended approach:
1. Implement 7.1, 7.2, 7.3 together (core workflow changes)
2. Run tests - many will fail
3. Implement 7.12 (test updates) immediately after
4. Run tests - should pass
5. Continue with P1, P2, P3 issues

---

## Architecture Reference

### Files to Modify (Phase 7)

| File | Changes |
|------|---------|
| `src/alethfeld/mote.clj` | Line 136: default taint → `:needs-verification` |
| `src/alethfeld/proposal.clj` | Lines 60-63, 177-183: remove atomic handling, all claims get `:needs-verification` |
| `src/alethfeld/job.clj` | Lines 22-30: reorder role priorities (verifier=0) |
| `src/alethfeld/store.clj` | Lines 182-183: quorums → 1 |
| `src/alethfeld/verify.clj` | Line 135: vote quorum default → 1 |
| `src/alethfeld/session.clj` | Line 52: add `:taint-remove` to verifier role |
| `src/alethfeld/cmd.clj` | Lines 614-620: verifier CLI output with taint commands |
| `src/alethfeld/cli.clj` | Remove `--atomic` option from propose |
| `prompts/verifier.md` | New verifier prompt with decomposition/refinement demands |
| `prompts/proposer.md` | Remove --atomic refs, add verifier context |

### Key Code Locations

**Default taint:**
```clojure
;; src/alethfeld/mote.clj:136
:taint (or taint #{:needs-decomposition})  ; Change to #{:needs-verification}
```

**Role priority:**
```clojure
;; src/alethfeld/job.clj:22-30
(def ^:private role-priority
  {:advisor 0, :proposer 1, :prover 2, :verifier 3, ...})
;; Change to {:verifier 0, :proposer 1, :advisor 2, :prover 3, ...}
```

**Quorum defaults:**
```clojure
;; src/alethfeld/store.clj:182-183
:vote-quorum 2      ; Change to 1
:proposal-quorum 2  ; Change to 1
```

---

## Key Documents

| Document | Purpose |
|----------|---------|
| **`docs/V02-REVISION-PLAN.md`** | **CANONICAL** - Full v0.2 plan (just rewritten) |
| **`.claude/plans/snoopy-twirling-hamming.md`** | Detailed Phase 7 implementation plan |
| `docs/IMPLEMENTATION-PLAN.md` | Overall v0.1-v0.2 spec |
| `CLAUDE.md` | Development conventions |

---

## Known Issues

1. **Drift between plan/issues/code** - See top of this document

2. **Stale beads issues** - `alethfeld-19kq` and `alethfeld-umt5` contradict Phase 7

3. **Tests will break** - During Phase 7 implementation, tests will fail until 7.12 is complete

4. **Concurrency tests flaky** - 3 tests in `concurrency_test.clj` marked `^:flaky`

---

## Environment

- **Language:** Clojure
- **Build tool:** deps.edn with aliases
- **Test runner:** cognitect-labs/test-runner
- **Schema validation:** Malli
- **File format:** EDN
- **VCS:** Git-backed (every CLI operation commits)
- **Issue tracking:** beads (bd command)
