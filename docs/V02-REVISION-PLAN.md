# Alethfeld v0.2 Revision Plan

**Status:** APPROVED
**Date:** 2026-01-09
**Based on:** Agent UX testing with claude-opus-4.5 (sqrt(2) irrationality proof)
**Test Reports:** `review/ux-review/af_recommendations.md`, `agent_behavior_log.md`, `subagent_test_log.md`

---

## Executive Summary

Alethfeld v0.1 successfully implements the core proof verification workflow, but agent testing and workflow analysis revealed significant issues:

1. **Workflow paradigm flaw** - Proposers act first, but verifiers should be gatekeepers
2. **Naming confusion** - `--agent` vs `--role` semantic overlap
3. **Batch operation gaps** - `vote-all` exists but `approve-all` doesn't
4. **Session ergonomics** - 73-character UUIDs are unwieldy
5. **Multi-agent race conditions** - Parallel subagents corrupt DAG
6. **Excessive ceremony** - 2-vote quorums slow down the workflow

**Goal:** Implement verifier-first workflow, reduce commands-to-completion from 55 to <40.

---

## Test Results Summary

| Metric | v0.1 Result | v0.2 Target |
|--------|-------------|-------------|
| Commands to completion | 55 | <40 |
| Stuck points | 2 | 0 |
| Help consultations | 4 | <2 |
| Role discovery errors | 1 | 0 |
| Subagent success rate | 50% (parallel) | 95%+ |

### Stuck Points Identified

1. **Role selection confusion** (command 11): Tried `af ready --agent advisor` expecting to get advisor role, but `--agent` is just a name field. Required `af ready --help` to discover `--role` flag.

2. **Leaf node handling** (commands 27-31): Unclear how to handle claims that don't need decomposition. The old `--atomic` flag was poorly discoverable.

### What Works Well (Preserve)

- Contextual "Next steps" in command output
- Role-specific ALLOWED/FORBIDDEN instructions
- `vote-all` batch command
- `af tree` visualization
- Session-based isolation

---

## Phase 1: Naming & Discoverability (HIGH PRIORITY)

### 1.1 Rename `--agent` to `--name`

**Problem:** `--agent` sounds like it should specify a role/agent-type, not an identifier.

**Evidence:** Agent tried `af ready --agent advisor` expecting to get advisor role.

**Change:**
```bash
# Before (confusing)
af ready --agent claude --role advisor

# After (clear)
af ready --name claude --role advisor
```

**Implementation:**
- Update `cli.clj`: rename `--agent` to `--name` in all commands
- Add `--agent` as deprecated alias (prints warning, still works)
- Update all prompts and documentation

**Files:** `src/alethfeld/cli.clj`, `prompts/*.md`

---

### 1.2 Smart Role Detection Hint

**Problem:** When `--name` value matches a known role name, agent was confused.

**Change:** Add contextual hint when this happens:
```
$ af ready --name advisor
Note: "advisor" looks like a role name.
Did you mean: af ready --name <your-name> --role advisor?
```

**Implementation:**
- In `cmd-ready`, check if `--name` value matches a role
- If match, print hint before proceeding

**Files:** `src/alethfeld/cmd.clj`

---

## Phase 2: Batch Operations Parity (HIGH PRIORITY)

Testing showed `vote-all` made verifier work 4x more efficient. Advisors need the same.

### 2.1 Add `approve-all` Command

**Problem:** Multiple advisor approvals required per proof.

**Change:**
```bash
# Approve all pending proposals in session
af approve-all --session xxx --reason "Valid decomposition"
```

**Implementation:**
- Add `cmd-approve-all` in `cmd.clj`
- Find all motes with pending proposals that session can approve
- Apply approval to each
- Report: "Approved 4 proposals: 1.1, 1.2, 1.3, 1.4"

**Files:** `src/alethfeld/cmd.clj`, `src/alethfeld/cli.clj`

---

### 2.2 Add `--max` Flag to `af ready`

**Problem:** Each job requires a new session, even for batch work.

**Change:**
```bash
# Claim up to 4 jobs for batch processing
af ready --name claude --role advisor --max 4
```

**Implementation:**
- Add `--max N` option to `cmd-ready`
- Claim N highest-priority jobs for the role
- Return list of motes and single session covering all
- Session tracks multiple mote assignments

**Files:** `src/alethfeld/cmd.clj`, `src/alethfeld/session.clj`

---

## Phase 3: Session Ergonomics (MEDIUM PRIORITY)

### 3.1 Support `@current` Session Alias

**Problem:** Session tokens are 73 characters, tedious to copy.

**Change:**
```bash
# Use special alias
af approve 1.1 --session @current   # Uses most recent session
af approve 1.1 --session @last      # Same as @current
```

**Implementation:**
- In session resolution, intercept `@current` and `@last`
- Look up most recent active session for the agent
- Error if multiple sessions active (ambiguous)

**Files:** `src/alethfeld/session.clj`, `src/alethfeld/cmd.clj`

---

### 3.2 Auto-Infer Session When Unambiguous

**Problem:** Even with aliases, requiring `--session` is tedious.

**Change:**
```bash
# If agent has exactly one active session, infer it
$ af approve 1.1
Using session: abc-123... (your only active session)
Approved!
```

**Implementation:**
- When `--session` not provided, check active sessions for current agent
- If exactly one, use it (print note)
- If zero or multiple, require explicit `--session`

**Files:** `src/alethfeld/cmd.clj`

---

### 3.3 Support `AF_SESSION` Environment Variable

**Problem:** Agents may want to set session once and reuse.

**Change:**
```bash
export AF_SESSION=$(af ready --name claude --role advisor --quiet)
af approve 1.1  # Uses AF_SESSION
af approve 1.2  # Uses AF_SESSION
af done         # Uses AF_SESSION
```

**Implementation:**
- Check `AF_SESSION` env var when `--session` not provided
- Priority: explicit flag > env var > auto-inference

**Files:** `src/alethfeld/cmd.clj`

---

## Phase 4: Visibility Improvements (MEDIUM PRIORITY)

### 4.1 Show Quorum Progress in Vote Displays

**Problem:** Agents didn't know quorum requirements until blocked.

**Change:**
```
# Show current/required format (quorum is configurable)
VOTES: 1/1 approve, 0 reject (quorum reached!)
```

**Implementation:**
- Load quorum config when displaying votes
- Show current/required format

**Files:** `src/alethfeld/cmd.clj` (show, approve, vote commands)

---

### 4.2 Enhanced `af status` Progress Breakdown

**Problem:** Status shows percentage but not work remaining by type.

**Change:**
```
sqrt(2) is irrational - 73% verified (14/19)

Progress by stage:
  Verifier work:    5 remaining (need verification or decomposition demand)
  Proposer work:    0 remaining
  Advisor reviews:  0 remaining (all proposals approved)

Structure: 5 intermediate + 14 leaf motes
Next action: af ready --name <you> --role verifier
```

**Implementation:**
- Calculate remaining work per role
- Show intermediate vs leaf breakdown
- Suggest next action based on what's needed

**Files:** `src/alethfeld/cmd.clj`

---

### 4.3 Explain Parent Mote Status

**Problem:** After all 14 leaves verified, 5 parents remained "fixed" (73%), confusing.

**Change:** Add explanation to status:
```
73% verified (14/19)
Note: 5 intermediate motes are "fixed" (decomposed into children).
      Verification applies to leaf motes only.
      All leaves verified = proof complete.
```

**Implementation:**
- Detect when all leaves verified but parents aren't
- Add explanatory note

**Files:** `src/alethfeld/cmd.clj`

---

## Phase 5: Multi-Agent Robustness (HIGH PRIORITY)

Subagent testing revealed critical race condition issues.

### 5.1 Add `af sessions` Command

**Problem:** No way to see active sessions for coordination.

**Change:**
```bash
$ af sessions
Active sessions:
  abc-123... | claude-1 | advisor | mote 1.1 | 5 min ago
  def-456... | claude-2 | verifier | mote 1.2 | 2 min ago

Stale sessions (may need cleanup):
  ghi-789... | claude-3 | proposer | mote 1.3 | 45 min ago (expired)
```

**Implementation:**
- Add `cmd-sessions` command
- List all active sessions with metadata
- Flag expired/stale sessions

**Files:** `src/alethfeld/cmd.clj`, `src/alethfeld/cli.clj`

---

### 5.2 Add Session Auto-Expire

**Problem:** Crashed agents leave sessions orphaned.

**Change:**
- Sessions expire after 30 minutes by default
- Configurable via `af config set session-timeout 60`
- `af ready` auto-cleans expired sessions before listing

**Implementation:**
- Add `:expires-at` to session schema (already exists)
- Enforce expiration in `cleanup-stale-sessions!`
- Make timeout configurable

**Files:** `src/alethfeld/session.clj`, `src/alethfeld/config.clj`

---

### 5.3 Add `af ready --reserve` for Job Reservation

**Problem:** Parallel subagents claiming jobs causes race conditions.

**Change:**
```bash
# Reserve without claiming (for orchestrators)
$ af ready --reserve --role proposer
Reserved: mote 1.1 for proposer
Reservation expires in 60 seconds
Claim with: af ready --name claude --claim-reservation abc123
```

**Implementation:**
- Add reservation system (lightweight pre-claim)
- Reservations expire quickly (60s)
- Must explicitly claim reservation to get session
- Prevents race: orchestrator reserves, then spawns subagent to claim

**Files:** `src/alethfeld/session.clj`, `src/alethfeld/cmd.clj`

---

### 5.4 Add `af repair` Command

**Problem:** DAG corruption from race conditions requires manual recovery.

**Change:**
```bash
$ af repair
Checking DAG integrity...
Found issues:
  - mote 1.1.1 references non-existent parent 1.1
  - session abc-123 references deleted mote

Repair options:
  af repair --dry-run     # Show what would be fixed
  af repair --auto        # Fix automatically
  af repair --interactive # Prompt for each fix
```

**Implementation:**
- Detect common DAG inconsistencies
- Offer repair strategies (archive orphans, clear stale sessions)
- Always create backup before repair

**Files:** `src/alethfeld/repair.clj` (new), `src/alethfeld/cmd.clj`

---

## Phase 6: Help & Documentation (LOW PRIORITY)

### 6.1 Make `af help` = `af --help`

**Problem:** `af help` shows minimal output; `af --help` shows full list.

**Change:** `af help` (no args) shows same output as `af --help`.

**Implementation:**
- Route `af help` to same handler as `--help`

**Files:** `src/alethfeld/cli.clj`

---

### 6.2 Add `af workflow` Command

**Problem:** Overall workflow isn't obvious without experimentation.

**Change:**
```bash
$ af workflow
Alethfeld Proof Workflow (Verifier-First)
==========================================

1. INITIALIZE
   af init --name "My Proof"
   af create --root --claim "Main theorem"

2. VERIFY (verifier role) - first step for all motes
   af ready --name <you> --role verifier
   - Vote for/against if claim is verifiable as-is
   - Demand decomposition if claim needs substeps
   - Demand refinement if claim needs assumptions/definitions

3. DECOMPOSE (proposer role) - only after verifier demands
   af ready --name <you> --role proposer
   af propose <id> --claim "substep 1" --claim "substep 2"

4. REVIEW (advisor role) - single approval needed
   af ready --name <you> --role advisor
   af approve <id> --reason "..."
   af approve-all --reason "..."  # Batch approve

5. REPEAT - children go back to verifiers

6. VALIDATE
   af check   # Verify DAG integrity
   af tree 1  # View proof structure

Roles: verifier (gatekeeper), proposer, advisor, prover, ref-checker, counterexample
```

**Implementation:**
- Add `cmd-workflow` command
- Load from `prompts/workflow.md` template

**Files:** `src/alethfeld/cmd.clj`, `prompts/workflow.md` (new)

---

### 6.3 Add `af roles` Enhancement

**Current:** Lists role names only.

**Change:** Show descriptions and when each is needed:
```bash
$ af roles
Alethfeld Roles
===============

verifier      GATEKEEPER - First role for all motes
              Vote for/against, or demand decomposition/refinement
              Use when: mote has 'needs-verification' taint

proposer      Break claims into sub-claims (decomposition)
              Only invoked after verifier demands decomposition
              Use when: mote has 'needs-decomposition' taint

advisor       Review and approve/reject proposals
              Single vote approves (quorum=1)
              Use when: proposal pending approval

prover        Add references, definitions, assumptions
              Use when: mote has 'needs-refinement' taint

ref-checker   Validate external references exist and apply
              Use when: mote has 'needs-refs' taint

counterexample  Find flaws and counterexamples
              Use when: adversarial review needed
```

**Implementation:**
- Enhance `cmd-roles` output
- Load descriptions from `prompts/roles.edn`

**Files:** `src/alethfeld/cmd.clj`, `prompts/roles.edn`

---

## Phase 7: Workflow Refactoring - Verifier-First Paradigm (CRITICAL)

Experience has shown that serious workflow role change is needed. The canonical work cycle should be: **prover ↔ verifier**. The verifier should be aggressive - acting as the first gatekeeper. The proposer is only invoked **after** the verifier complains that the proof is not detailed enough.

### Current Workflow (v0.1)
```
New mote → :needs-decomposition → Proposer → Advisor (2 votes) → Children → Verifier
```

### New Workflow (v0.2)
```
New mote → :needs-verification → Verifier → {
  Votes for → Verified
  Votes against → Refuted
  Demands decomposition → :needs-decomposition → Proposer → Advisor (1 vote) → Children → Verifier...
}
```

### Design Decisions
1. **Remove `:atomic` flag** - Verifiers now decide what needs decomposition for all claims
2. **Change vote quorum to 1** - Single verifier vote to verify (matches proposal quorum)
3. **Keep prover role** - Verifiers can demand `:needs-refinement` for missing assumptions/definitions

---

### 7.1 Change Default Taint to `:needs-verification`

**Problem:** New motes get `:needs-decomposition`, sending them to proposers first.

**Change:** All new motes start with `:needs-verification` taint.

**Implementation:**
- `mote.clj` line 136: Default taint `#{:needs-verification}` instead of `#{:needs-decomposition}`

**Files:** `src/alethfeld/mote.clj`

---

### 7.2 Update Proposal Taints for Verifier-First

**Problem:** Non-atomic proposed children get `:needs-decomposition`.

**Change:** All proposed/promoted children get `:needs-verification`.

**Implementation:**
- `proposal.clj` lines 60-63: All claims get `#{:needs-verification}`
- `proposal.clj` lines 177-183: Promoted children get `:needs-verification`

**Files:** `src/alethfeld/proposal.clj`

---

### 7.3 Reorder Role Priorities

**Problem:** Verifier is priority 3 (low), advisor is 0 (highest).

**Change:**
```clojure
;; NEW priority order:
{:verifier       0  ; Verify FIRST (gatekeeper)
 :proposer       1  ; Decompose (only after verifier demands)
 :advisor        2  ; Review proposals
 :prover         3  ; Refine details
 :ref-checker    4  ; Check refs
 :counterexample 5}
```

**Files:** `src/alethfeld/job.clj`

---

### 7.4 Change Proposal Quorum to 1

**Problem:** Requiring 2 advisor votes is cumbersome with verifier-first workflow.

**Change:** Single advisor vote approves proposals.

**Implementation:**
- `store.clj` line 183: Default `proposal-quorum` to 1
- `proposal.clj` line 161: Fallback default to 1

**Files:** `src/alethfeld/store.clj`, `src/alethfeld/proposal.clj`

---

### 7.5 Change Vote Quorum to 1

**Problem:** Requiring 2 verifier votes slows the verifier-first cycle.

**Change:** Single verifier vote to verify motes.

**Implementation:**
- `store.clj` line 182: Default `vote-quorum` to 1
- `verify.clj` line 135: Fallback default to 1

**Files:** `src/alethfeld/store.clj`, `src/alethfeld/verify.clj`

---

### 7.6 Update Verifier Prompt for Decomposition Demands

**Problem:** Verifier prompt doesn't show how to demand decomposition.

**Change:** New verifier prompt with three options:
1. Vote for/against (claim is verifiable)
2. Demand decomposition (claim needs substeps)
3. Demand refinement (claim needs assumptions/definitions)

**Implementation:**
- Rewrite `prompts/verifier.md` with new task structure
- Add `af taint --add needs-decomposition` command

**Files:** `prompts/verifier.md`

---

### 7.7 Update Verifier CLI Output

**Problem:** CLI only shows vote commands for verifiers.

**Change:** Add taint commands to verifier output:
```
If claim NEEDS MORE DETAIL (demand decomposition):
  af taint <id> --add needs-decomposition --session <session>
```

**Files:** `src/alethfeld/cmd.clj`

---

### 7.8 Add Verifier `:taint-remove` Permission

**Problem:** Verifiers need to remove `:needs-verification` when demanding decomposition.

**Change:**
```clojure
;; BEFORE:
:verifier #{:vote :taint-add :done}

;; AFTER:
:verifier #{:vote :taint-add :taint-remove :done}
```

**Files:** `src/alethfeld/session.clj`

---

### 7.9 Update Proposer Prompt Context

**Problem:** Proposer prompt doesn't reflect responding to verifier demands.

**Change:** Add context:
```markdown
A VERIFIER has determined this claim needs more detail before it can be verified.
Your job is to break it down into verifiable substeps.
```

**Files:** `prompts/proposer.md`

---

### 7.10 Remove `--atomic` Flag

**Problem:** Atomic flag is redundant - verifiers now decide what needs decomposition.

**Change:** Remove `--atomic` option from propose command.

**Implementation:**
- Remove atomic handling in `proposal.clj` create-child-mote
- Remove `--atomic` CLI option from `cli.clj`
- Update proposer prompt to remove `--atomic` references
- Remove atomic-specific tests

**Files:** `src/alethfeld/proposal.clj`, `src/alethfeld/cli.clj`, `prompts/proposer.md`, tests

---

### 7.11 Add Refinement Demand to Verifier Prompt

**Problem:** Verifiers should be able to request more detail without full decomposition.

**Change:** Add to verifier commands:
```markdown
If claim needs REFINEMENT (missing assumptions/definitions):
  af taint {{mote-id}} --add needs-refinement --session {{session-id}}
```

**Files:** `prompts/verifier.md`

---

### 7.12 Update Tests for New Defaults

**Problem:** Many tests assume old defaults (quorum=2, taint=needs-decomposition).

**Implementation:**
- `test/alethfeld/mote_test.clj` - Default taint assertions
- `test/alethfeld/proposal_test.clj` - Remove atomic tests, update taint assertions
- `test/alethfeld/job_test.clj` - Role priority tests
- `test/alethfeld/verify_test.clj` - Vote quorum tests
- `test/alethfeld/cmd/vote_all_test.clj` - Quorum expectations

**Files:** Multiple test files

---

## Implementation Priority

### Batch 7: Workflow Refactoring (Do First - Critical)
| Step | Description | Impact |
|------|-------------|--------|
| 7.1 | Default taint to :needs-verification | Critical |
| 7.2 | Proposal taints for verifier-first | Critical |
| 7.3 | Reorder role priorities | Critical |
| 7.4 | Proposal quorum to 1 | High |
| 7.5 | Vote quorum to 1 | High |
| 7.6 | Verifier prompt for decomposition | High |
| 7.7 | Verifier CLI output | Medium |
| 7.8 | Verifier taint-remove permission | Medium |
| 7.9 | Proposer prompt context | Medium |
| 7.10 | Remove --atomic flag | Medium |
| 7.11 | Refinement demand option | Low |
| 7.12 | Update tests | Critical |

### Batch 1: Naming Fixes
| Step | Description | Impact |
|------|-------------|--------|
| 1.1 | Rename `--agent` to `--name` | High |
| 1.2 | Smart role detection hint | High |

### Batch 2: Batch Operations
| Step | Description | Impact |
|------|-------------|--------|
| 2.1 | Add `approve-all` command | High |
| 2.2 | Add `--max` flag to `af ready` | Medium |

### Batch 3: Session Ergonomics
| Step | Description | Impact |
|------|-------------|--------|
| 3.1 | Support `@current` session alias | Medium |
| 3.2 | Auto-infer session | Medium |
| 3.3 | Support `AF_SESSION` env var | Low |

### Batch 4: Visibility
| Step | Description | Impact |
|------|-------------|--------|
| 4.1 | Show quorum progress | Medium |
| 4.2 | Enhanced status breakdown | Medium |
| 4.3 | Explain parent mote status | Low |

### Batch 5: Multi-Agent
| Step | Description | Impact |
|------|-------------|--------|
| 5.1 | Add `af sessions` command | Medium |
| 5.2 | Session auto-expire | High |
| 5.3 | Add `af ready --reserve` | High |
| 5.4 | Add `af repair` command | High |

### Batch 6: Documentation
| Step | Description | Impact |
|------|-------------|--------|
| 6.1 | Make `af help` = `af --help` | Low |
| 6.2 | Add `af workflow` command | Medium |
| 6.3 | Enhance `af roles` output | Low |

---

## Success Criteria

### Quantitative
- Commands to completion: <40 (was 55)
- Stuck points: 0 (was 2)
- Subagent success rate: >95% (was 50% parallel)

### Qualitative
- Agent never tries `--agent` when meaning `--role`
- Verifier naturally acts as first gatekeeper
- Single votes move work forward (no waiting for quorum)
- Batch operations reduce session overhead
- Multi-agent workflows don't cause DAG corruption

---

## Testing Plan

After each batch:
1. Run blind discovery test (Phase 1 from testing guide)
2. Record commands-to-completion
3. Note any new stuck points
4. Run subagent test for multi-agent batches

Final validation:
- Fresh agent completes sqrt(2) proof in <40 commands
- Orchestrator + 5 subagents complete proof without race conditions
- Verifier-first workflow feels natural

---

## Files Modified

| File | Batches |
|------|---------|
| `src/alethfeld/mote.clj` | 7 |
| `src/alethfeld/proposal.clj` | 7 |
| `src/alethfeld/job.clj` | 7 |
| `src/alethfeld/store.clj` | 7 |
| `src/alethfeld/verify.clj` | 7 |
| `src/alethfeld/session.clj` | 2, 3, 5, 7 |
| `src/alethfeld/cli.clj` | 1, 2, 5, 6, 7 |
| `src/alethfeld/cmd.clj` | 1, 2, 3, 4, 5, 6, 7 |
| `src/alethfeld/config.clj` | 5 |
| `src/alethfeld/repair.clj` | 5 (new) |
| `prompts/verifier.md` | 7 |
| `prompts/proposer.md` | 7 |
| `prompts/workflow.md` | 6 (new) |
| `prompts/roles.edn` | 6 |

---

## Changelog for v0.2

### Breaking Changes
- `--agent` renamed to `--name` (deprecated alias still works)
- **Workflow paradigm shift**: Verifier is now the first role (was proposer)
- Default `proposal-quorum` changed from 2 to 1
- Default `vote-quorum` changed from 2 to 1
- `--atomic` flag removed from `af propose` (verifiers decide decomposition)
- Default taint for new motes is `:needs-verification` (was `:needs-decomposition`)

### New Commands
- `af approve-all` - Batch approve pending proposals
- `af sessions` - List active sessions
- `af repair` - Fix DAG inconsistencies
- `af workflow` - Show workflow guide

### New Flags
- `af ready --max N` - Claim up to N jobs
- `af ready --reserve` - Reserve job without claiming
- `--session @current` - Alias for current session

### Enhancements
- **Verifier-first workflow**: Verifiers act as gatekeepers, demanding decomposition when needed
- Verifiers can now demand `:needs-decomposition` or `:needs-refinement`
- Verifiers have `:taint-remove` permission for workflow control
- Quorum progress shown in vote displays
- Enhanced `af status` with progress by stage
- Smart detection when `--name` matches a role
- Session auto-inference when unambiguous
- `AF_SESSION` environment variable support
- `af help` now shows full help (same as `af --help`)
- Enhanced `af roles` with descriptions

### Bug Fixes
- Session auto-expire prevents orphaned sessions
- Reservation system prevents multi-agent race conditions
