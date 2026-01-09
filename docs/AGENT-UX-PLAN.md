# Agent UX Implementation Plan

**Status:** PROPOSED
**Date:** 2026-01-09
**Priority:** P0 - Critical
**Reason:** Agent testing revealed fundamental workflow discovery failures

---

## Executive Summary

Agent testing revealed catastrophic UX failures:

1. **Agents discovered the WRONG workflow** - They guessed at roles and invented workflows instead of using `af ready`
2. **Prompts didn't print** - Role prompts (the agent's instructions) were buried in EDN, invisible
3. **No workflow guidance** - Bare `af` showed a command list, not "what to do first"

**Root cause:** The CLI was designed for humans who read docs, not agents who discover through interaction.

---

## Critical Issues from Testing

### Issue 1: Workflow Discovery Failure

**What happened:** Agents tried 7+ invalid role names before discovering `advisor` via `af ready --no-claim`. 25% of all commands were wasted on role discovery.

**Why it happened:**
- `af` bare shows alphabetical command list, not workflow
- No command says "start here"
- Role names not listed anywhere visible
- Error messages don't suggest valid alternatives

**Evidence from test logs:**
```
af claim 1 --role decomposer → ERROR: Invalid role
af claim 1 --role reviewer → ERROR: Invalid role
af claim 1 --role critic → ERROR: Invalid role
af claim 1 --role judge → ERROR: Invalid role
af claim 1 --role approver → ERROR: Invalid role
af claim 1 --role admin → ERROR: Invalid role
af claim 1 --role arbiter → ERROR: Invalid role
```

### Issue 2: Prompts Not Visible

**What happened:** Role prompts (instructions for what the agent should do) are generated but buried in the `:prompt` key of EDN output. Agents never saw them.

**Why it matters:** The prompts contain:
- Task description ("You are a VERIFIER agent...")
- Allowed commands with examples
- What to look for
- How to complete the task

Without prompts, agents are flying blind.

### Issue 3: No Next-Action Guidance

**What happened:** After every command, agents had to figure out what to do next from scratch.

**Evidence:** Agent ran `af show` 12 times just to understand state, and consulted help 13 times throughout the session.

---

## Core Agent Lifecycle Principle

**One agent = One mote = One role = Terminate**

Agents are ephemeral workers. The workflow is:
1. Agent spawns
2. Agent runs `af ready --agent <name>` to get assigned ONE job (mote + role)
3. Agent reads the prompt and performs the task
4. Agent runs `af done --session <token>` to complete
5. **Agent terminates**

**Critical design constraints:**
- An agent CANNOT change roles mid-session
- An agent CANNOT claim additional motes
- When work is done, the agent's job is FINISHED
- New work = spawn a NEW agent

This prevents:
- Role confusion (agent tries to verify its own proposal)
- Workflow corruption (agent skips steps)
- Context pollution (agent carries state between tasks)

The CLI should make this lifecycle OBVIOUS:
- `af ready` output should say "You have ONE task. Complete it, then terminate."
- `af done` output should say "Session complete. Agent should now terminate."
- Error messages should NOT suggest switching roles, only suggest `af done` and spawning new agent

---

## Design Principles to Implement

From Part 4 of the Agent UX Testing Guide:

| Principle | Current State | Target State |
|-----------|---------------|--------------|
| P1: Bare command shows context | Shows help list | Shows project status + "run `af ready`" |
| P2: Every output suggests next action | Raw EDN output | "Next: af vote 1.2 --for" |
| P3: Errors explain why + alternatives | "Invalid role" | "Invalid role 'reviewer'. Valid: proposer, advisor, verifier..." |
| P4: Structured output includes commands | Job has `:prompt` | Job has `:example-commands` list |
| P5: Idempotent operations | Some are, some crash | All idempotent or explicit error |
| P6: Forgiving syntax | Strict parsing | Typo suggestions, flexible flags |
| P7: Contextual defaults | None | Single session = auto-use |
| P8: Dry run mode | Only vote-all | All mutating commands |
| P9: Progressive disclosure | All-or-nothing | Default simple, --verbose for detail |
| P10: Teach through errors | Generic errors | Workflow explanation in errors |

---

## Implementation Plan

### Phase 1: Critical Path Fixes (HIGHEST PRIORITY)

These changes fix the core workflow discovery problem.

#### 1.1 New Bare Command Output

**File:** `src/alethfeld/cli.clj`

**Current behavior:** `af` shows alphabetical command list

**New behavior:**
```
$ af
Alethfeld v0.1.0 - Collaborative Proof Verification

Project: My Proof
Motes: 15 (10 verified, 3 need work, 2 proposed)

Your next action:
  af ready --agent <name>    → Get assigned a task with instructions

Quick commands:
  af status                  → View proof progress
  af tree 1                  → View proof structure from mote 1
  af help                    → Full command reference

Roles: proposer, advisor, prover, verifier, ref-checker, counterexample
```

**Implementation:**
1. Create `cmd-bare` handler that detects bare invocation
2. Load project status (if initialized) or show init guidance
3. Always show roles list
4. Always suggest `af ready --agent <name>` as primary action

#### 1.2 Prompts MUST Print

**File:** `src/alethfeld/cmd.clj` (`cmd-ready`)

**Current behavior:** Prompt buried in `:prompt` key of returned Job

**New behavior:** When `af ready --agent <name>` claims a job, print the prompt prominently:

```
$ af ready --agent claude-1

╔═══════════════════════════════════════════════════════════════════════════════╗
║  JOB CLAIMED: verifier on mote 1.2                                            ║
╠═══════════════════════════════════════════════════════════════════════════════╣
║  Session: abc-123-def                                                          ║
║  Role: verifier                                                                 ║
║  Priority: p1 | Difficulty: 3                                                   ║
╚═══════════════════════════════════════════════════════════════════════════════╝

You are a VERIFIER agent. Your task is to VALIDATE this mote.

MOTE: 1.2
CLAIM: Both p and q are even contradicts coprimality
...

COMMANDS YOU CAN USE:
  af vote 1.2 --for --session abc-123-def --reason "..."
  af vote 1.2 --against --session abc-123-def --reason "..."

WHEN FINISHED:
  af done --session abc-123-def
```

**Implementation:**
1. Separate `:human-output` from `:data-output` in command results
2. For `af ready`, construct formatted prompt block
3. Human output goes to stdout, data to stderr (or format-based routing)

#### 1.3 External Prompt Files

**Files:** Create `prompts/` directory

**Current state:** Prompts hardcoded in `src/alethfeld/prompt.clj`

**New state:** Prompts loaded from EDN/Markdown files:
```
prompts/
├── roles.edn              # Role definitions and descriptions
├── proposer.md            # Proposer role prompt template
├── advisor.md             # Advisor role prompt template
├── verifier.md            # Verifier role prompt template
├── prover.md              # Prover role prompt template
├── ref-checker.md         # Ref-checker role prompt template
├── counterexample.md      # Counterexample role prompt template
└── session-context.md     # Session context block template
```

**Implementation:**
1. Create `prompts/` directory with role templates
2. Update `prompt.clj` to load templates from files
3. Use mustache/stencil style placeholders: `{{mote-id}}`, `{{claim}}`
4. Fallback to embedded prompts if files missing

#### 1.4 List Jobs, THEN Claim

**Current workflow:** `af ready --agent X` auto-claims first job

**Problem:** Agent doesn't see what's available, can't choose

**New workflow:**
```bash
# Step 1: See available jobs (no claim)
$ af ready
Available jobs:
  1. mote 1.2 | role: verifier | p1 | difficulty: 3
  2. mote 1.3 | role: advisor | p2 | difficulty: 2
  3. mote 1.4 | role: proposer | p2 | difficulty: 4

Claim a job:
  af ready --agent <name> --job 1    # Claim job #1
  af ready --agent <name>            # Claim highest priority

# Step 2: Claim specific job
$ af ready --agent claude-1 --job 1
[Prints full prompt and session info]
```

**Implementation:**
1. `af ready` without `--agent` = list mode (no claim)
2. Add `--job N` option to claim specific job from list
3. `af ready --agent X` without `--job` = claim #1 (current behavior)

---

### Phase 2: Error Message Overhaul

#### 2.1 Invalid Role Error

**Current:**
```
Failed to validate "--role reviewer": Invalid role
```

**New:**
```
Invalid role: "reviewer"

Valid roles:
  proposer      - Break claims into sub-claims
  advisor       - Review and approve/reject proposals
  prover        - Add references and refine claims
  verifier      - Vote on claim validity
  ref-checker   - Validate external references
  counterexample - Find flaws and counterexamples

Did you mean: verifier?

Get available work:
  af ready --agent <name>    → Shows what roles are needed
```

**Implementation:**
1. Create `suggest-role` function using Levenshtein distance
2. Add role descriptions to schema or config
3. Update all role validation errors

#### 2.2 Session Not Found Error

**Current:**
```
Session not found or expired
```

**New:**
```
Session not found: abc-123-...

This can happen if:
  • The session expired (timeout: 30 minutes)
  • The session was ended with 'af done'
  • The session ID is incorrect

To get a new session:
  af ready --agent <name>    → Claim a job and get new session

To check your active sessions:
  af status                  → Shows active sessions
```

#### 2.3 Role Cannot Perform Action

**Current:**
```
Action not allowed for your role.
Your role: verifier
Attempted action: approve
Allowed actions: vote, done, taint-add
```

**New:**
```
Cannot approve: your role is 'verifier'

Approving proposals requires role 'advisor'. As a verifier, you can:
  af vote 1.2 --for --session xxx    → Vote claim is valid
  af vote 1.2 --against --session xxx → Vote claim is invalid
  af done --session xxx               → End your session

To get advisor work instead:
  af done --session xxx               → End current session
  af ready --agent <name> --role advisor → Get advisor work
```

---

### Phase 3: Next-Action Suggestions

#### 3.1 After Every Command Output

Every command should end with a "Next steps" section:

```
$ af propose 1 --session xxx --claim "First" --claim "Second"
✓ Created proposal with 2 children

  1.1 [proposed] First
  1.2 [proposed] Second

Waiting for advisor approval (0/2 votes)

Next steps:
  → af done --session xxx              End session (proposal submitted)
  → af show 1                          Check proposal status later
```

**Implementation:**
1. Add `:next-actions` key to all command results
2. `next-actions` is a vector of `{:command "..." :description "..."}`
3. Format layer renders these after main output

#### 3.2 Contextual Next Actions

Next actions should be intelligent based on state:

| After | If | Suggest |
|-------|-----|---------|
| `af vote 1.1 --for` | Quorum not reached | "Waiting for 1 more vote" |
| `af vote 1.1 --for` | Quorum reached, more siblings | "Continue: af vote 1.2 --for" |
| `af vote 1.1 --for` | All siblings done | "af done --session xxx" |
| `af approve 1` | Quorum reached | "Children promoted. Verification needed." |
| `af propose 1` | Submitted | "Waiting for advisors. Run af done" |

---

### Phase 4: Forgiving Syntax

#### 4.1 Typo Suggestions

```
$ af porpose 1 --claim "..."
Unknown command: porpose

Did you mean: propose?
  af propose 1 --claim "..."
```

**Implementation:**
1. On unknown command, compute Levenshtein distance to all commands
2. If distance ≤ 2, suggest "Did you mean: X?"

#### 4.2 Flexible Flag Parsing

Accept common variations:
- `--session` or `-s` or `--sess`
- `--agent` or `-a`
- `--for` or `--yes` or `--approve`
- `--against` or `--no` or `--reject`

#### 4.3 Flag Order Independence

```bash
# All equivalent:
af vote 1.2 --for --session xxx
af vote --for 1.2 --session xxx
af --session xxx vote 1.2 --for
```

This already works with tools.cli, but document it.

---

### Phase 5: Contextual Defaults

#### 5.1 Single Session Auto-Use

**Current:** Always require `--session`

**New:** If agent has exactly one active session, use it:
```
$ af vote 1.2 --for
Using session: abc-123-def (your only active session)
✓ Vote recorded
```

If multiple sessions, require explicit choice or list them.

#### 5.2 Default Agent from Environment

```bash
export AF_AGENT=claude-1
af ready  # Uses AF_AGENT
```

---

### Phase 6: Dry Run Mode

Add `--dry-run` to all mutating commands:

```
$ af propose 1 --claim "A" --claim "B" --dry-run

DRY RUN - No changes made

Would create:
  1.1 [proposed] A (difficulty: 3)
  1.2 [proposed] B (difficulty: 3)

Would update:
  1 → set taint :needs-proposal-review

Would require:
  2 advisor votes to approve

Run without --dry-run to execute.
```

---

### Phase 7: Progressive Disclosure

#### 7.1 Simple Default Output

```
$ af status
My Proof - 70% verified (7/10)
Ready work: 3 motes (1 advisor, 2 verifier)
```

#### 7.2 Verbose Output

```
$ af status --verbose
My Proof - 70% verified

By status:
  verified: 7
  fixed: 2 (needs-verification: 1, needs-decomposition: 1)
  proposed: 1

By role needed:
  advisor: 1 mote (proposal approval)
  verifier: 2 motes
  proposer: 0 motes

Active sessions: 0
Recent: prover-1 proposed 1.2.1-1.2.3 (5 min ago)
```

---

### Phase 8: Command Aliases

Add agent-intuitive aliases:

| Alias | Maps To |
|-------|---------|
| `af list` | `af status` |
| `af verify` | `af vote --for` |
| `af refute` | `af vote --against` |
| `af decompose` | `af propose` |
| `af add-child` | `af propose` (single child) |
| `af roles` | Show role descriptions |
| `af jobs` | `af ready` (list mode) |

---

## Implementation Order

### Batch 1: Critical (Do First)
1. ✦ 1.1 New bare command output
2. ✦ 1.2 Prompts MUST print
3. ✦ 2.1 Invalid role error improvement

### Batch 2: Workflow
4. 1.4 List jobs, then claim
5. 1.3 External prompt files
6. 3.1 Next-action suggestions

### Batch 3: Errors
7. 2.2 Session not found error
8. 2.3 Role cannot perform action
9. 3.2 Contextual next actions

### Batch 4: Polish
10. 4.1 Typo suggestions
11. 5.1 Single session auto-use
12. 6 Dry run mode
13. 7 Progressive disclosure
14. 8 Command aliases

---

## Success Criteria

After implementation, an agent should:

1. **Discover workflow on first try**: `af` → `af ready --agent X` → gets prompt → follows prompt
2. **Never guess roles**: All valid roles visible in bare output
3. **Never get stuck**: Every output suggests next action
4. **Recover from errors**: Error messages teach the correct workflow
5. **Complete sqrt(2) proof in <50 commands** (current: 76, 25% wasted on discovery)

---

## Testing Plan

After implementation:

1. Re-run Phase 1 (Blind Discovery) test with fresh agent
2. Record commands-to-completion
3. Target: <50 commands, 0 role discovery errors
4. Run Phase 6 (Teach Back) to verify mental model

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/alethfeld/cli.clj` | Bare command handler, alias registration, typo suggestions |
| `src/alethfeld/cmd.clj` | Human output formatting, next-action generation |
| `src/alethfeld/prompt.clj` | Load from external files, add session context |
| `src/alethfeld/errors.clj` | Enhanced error messages with suggestions |
| `prompts/*.md` | NEW: External prompt templates |
| `prompts/roles.edn` | NEW: Role descriptions |

---

## Dependencies

None. This is a UX overhaul, not a data model change.

All existing tests should continue to pass (output format changes only affect human-readable output, not command behavior).
