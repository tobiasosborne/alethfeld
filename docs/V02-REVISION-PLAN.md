# Alethfeld v0.2 Revision Plan

**Status:** APPROVED
**Date:** 2026-01-09
**Based on:** Agent UX testing with claude-opus-4.5 (sqrt(2) irrationality proof)
**Test Reports:** `review/ux-review/af_recommendations.md`, `agent_behavior_log.md`, `subagent_test_log.md`

---

## Executive Summary

Alethfeld v0.1 successfully implements the core proof verification workflow, but agent testing revealed significant UX friction. This revision plan addresses:

1. **Discoverability failures** - Agents couldn't find `--role` or `--atomic` flags
2. **Naming confusion** - `--agent` vs `--role` semantic overlap
3. **Batch operation gaps** - `vote-all` exists but `approve-all` doesn't
4. **Session ergonomics** - 73-character UUIDs are unwieldy
5. **Multi-agent race conditions** - Parallel subagents corrupt DAG
6. **Quorum invisibility** - Agents didn't know 2 votes were required

**Goal:** Reduce commands-to-completion from 55 to <40, eliminate stuck points.

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

2. **Atomic flag discovery** (commands 27-31): Unclear how to handle leaf nodes. Explored prover role, verifier role, and `af update` before finding `--atomic` in `af propose --help`.

### What Works Well (Preserve)

- Contextual "Next steps" in command output
- Role-specific ALLOWED/FORBIDDEN instructions
- `vote-all` batch command
- `af tree` visualization
- Session-based isolation

---

## Phase 1: Naming & Discoverability (HIGH PRIORITY)

These fixes address the two explicit stuck points from testing.

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

**Problem:** When `--agent` value matches a known role name, agent was confused.

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

### 1.3 Add `--atomic` Hint to Proposer Instructions

**Problem:** Took 5 commands to discover `--atomic` flag for leaf claims.

**Change:** Add to proposer role prompt:
```
COMMANDS:
  af propose <id> --claim "substep" --difficulty N
  af propose <id> --claim "leaf claim" --atomic    # For self-evident claims

Tip: Use --atomic for claims that need verification but not further decomposition.
```

**Implementation:**
- Update proposer prompt template
- Add to "Next steps" output after `af ready` assigns proposer role

**Files:** `prompts/proposer.md`, `src/alethfeld/cmd.clj`

---

### 1.4 Contextual `--atomic` Suggestion

**Problem:** Even with documentation, agents may miss it.

**Change:** When a proposer claims a difficulty-1 mote:
```
Hint: This is a difficulty-1 mote. If it's self-evident, use --atomic:
  af propose 1.1 --claim "..." --atomic --session xxx
```

**Implementation:**
- In `cmd-ready`, check if assigned mote has difficulty 1
- Add conditional hint to output

**Files:** `src/alethfeld/cmd.clj`

---

## Phase 2: Batch Operations Parity (HIGH PRIORITY)

Testing showed `vote-all` made verifier work 4x more efficient. Advisors need the same.

### 2.1 Add `approve-all` Command

**Problem:** Required 8 separate advisor sessions (2 votes × 4 proposals).

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

**Problem:** Agents didn't know 2 votes were required until blocked.

**Change:**
```
# Before
VOTES: 1 approve, 0 reject

# After
VOTES: 1/2 approve, 0 reject (need 1 more for quorum)
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
  Proposer work:    0 remaining
  Advisor reviews:  0 remaining (all proposals approved)
  Verifier votes:   14 remaining (0/14 at quorum)

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
Alethfeld Proof Workflow
========================

1. INITIALIZE
   af init --name "My Proof"
   af create --root --claim "Main theorem"

2. DECOMPOSE (proposer role)
   af ready --name <you> --role proposer
   af propose <id> --claim "substep 1" --claim "substep 2"
   Use --atomic for self-evident claims

3. REVIEW (advisor role) - requires 2 approvals
   af ready --name <you> --role advisor
   af approve <id> --reason "..."
   af approve-all --reason "..."  # Batch approve

4. VERIFY (verifier role) - requires 2 votes
   af ready --name <you> --role verifier
   af vote <id> --for --reason "..."
   af vote-all --for --reason "..."  # Batch vote

5. VALIDATE
   af check   # Verify DAG integrity
   af tree 1  # View proof structure

Roles: proposer, advisor, prover, verifier, ref-checker, counterexample
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

proposer      Break claims into sub-claims (decomposition)
              Use when: mote has 'needs-decomposition' taint

advisor       Review and approve/reject proposals
              Use when: proposal pending approval

verifier      Vote on whether claims are valid
              Use when: mote has 'needs-verification' taint

prover        Add references, definitions, assumptions
              Use when: mote needs more supporting detail

ref-checker   Validate external references exist and apply
              Use when: mote has references to check

counterexample  Find flaws and counterexamples
              Use when: adversarial review needed
```

**Implementation:**
- Enhance `cmd-roles` output
- Load descriptions from `prompts/roles.edn`

**Files:** `src/alethfeld/cmd.clj`, `prompts/roles.edn`

---

## Implementation Priority

### Batch 1: Stuck Point Fixes (Do First)
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 1.1 | Rename `--agent` to `--name` | 2h | High |
| 1.2 | Smart role detection hint | 1h | High |
| 1.3 | Add `--atomic` to proposer prompt | 30m | High |
| 1.4 | Contextual `--atomic` suggestion | 1h | Medium |

### Batch 2: Batch Operations
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 2.1 | Add `approve-all` command | 3h | High |
| 2.2 | Add `--max` flag to `af ready` | 4h | Medium |

### Batch 3: Session Ergonomics
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 3.1 | Support `@current` session alias | 2h | Medium |
| 3.2 | Auto-infer session | 2h | Medium |
| 3.3 | Support `AF_SESSION` env var | 1h | Low |

### Batch 4: Visibility
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 4.1 | Show quorum progress | 1h | Medium |
| 4.2 | Enhanced status breakdown | 2h | Medium |
| 4.3 | Explain parent mote status | 1h | Low |

### Batch 5: Multi-Agent
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 5.1 | Add `af sessions` command | 2h | Medium |
| 5.2 | Session auto-expire | 2h | High |
| 5.3 | Add `af ready --reserve` | 4h | High |
| 5.4 | Add `af repair` command | 6h | High |

### Batch 6: Documentation
| Step | Description | Effort | Impact |
|------|-------------|--------|--------|
| 6.1 | Make `af help` = `af --help` | 30m | Low |
| 6.2 | Add `af workflow` command | 2h | Medium |
| 6.3 | Enhance `af roles` output | 1h | Low |

---

## Success Criteria

### Quantitative
- Commands to completion: <40 (was 55)
- Stuck points: 0 (was 2)
- Subagent success rate: >95% (was 50% parallel)

### Qualitative
- Agent discovers `--atomic` without consulting help
- Agent never tries `--agent` when meaning `--role`
- Batch operations reduce advisor sessions from 8 to 2
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

---

## Files Modified

| File | Batches |
|------|---------|
| `src/alethfeld/cli.clj` | 1, 2, 5, 6 |
| `src/alethfeld/cmd.clj` | 1, 2, 3, 4, 5, 6 |
| `src/alethfeld/session.clj` | 2, 3, 5 |
| `src/alethfeld/config.clj` | 5 |
| `src/alethfeld/repair.clj` | 5 (new) |
| `prompts/proposer.md` | 1 |
| `prompts/workflow.md` | 6 (new) |
| `prompts/roles.edn` | 6 |

---

## Changelog for v0.2

### Breaking Changes
- `--agent` renamed to `--name` (deprecated alias still works)

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
- Quorum progress shown in vote displays (1/2 approve)
- Enhanced `af status` with progress by stage
- Contextual hints for `--atomic` flag
- Smart detection when `--name` matches a role
- Session auto-inference when unambiguous
- `AF_SESSION` environment variable support
- `af help` now shows full help (same as `af --help`)
- Enhanced `af roles` with descriptions

### Bug Fixes
- Session auto-expire prevents orphaned sessions
- Reservation system prevents multi-agent race conditions
