# Agent UX Testing: A Methodology for CLI Tools

**Purpose:** Systematic approach to designing command-line tools optimized for AI agent usage  
**Context:** Developed during Alethfeld (`af`) design process  
**Date:** January 2026

---

## Part 1: Philosophy

### The Core Insight

AI agents are a new user class with distinct characteristics:

| Human Users | Agent Users |
|-------------|-------------|
| Read documentation linearly | Parse help text on-demand |
| Build muscle memory | No memory between sessions |
| Tolerate minor friction | Compound small frictions into failures |
| Ask for help from humans | Must self-recover or fail |
| Interpret intent from context | Rely on explicit structure |
| Learn from tutorials | Learn from examples and errors |

**Agents are both more capable and more brittle than humans.** They can process structured output instantly but may spiral on ambiguous errors.

### The "Desire Path" Principle

In landscape architecture, desire paths are the worn trails where people actually walk, ignoring the paved paths. For agent UX:

> **Observe what agents try to do, then pave those paths.**

Don't design what you think agents should do. Watch what they attempt, then make that work.

---

## Part 2: Testing Protocol

### Phase 0: Baseline (No Tool)

**Goal:** Understand the agent's prior mental model.

**Prompt:**
```
Write a structured proof that sqrt(2) is irrational.
Organize it as a tree of claims, each with:
- Status (proven/unproven)
- Dependencies on other claims
- Justification

Use whatever format feels natural.
```

**Observe:**
- What structure does the agent naturally produce? (Tree? List? Graph?)
- What terminology does it use? (Claim? Lemma? Step? Node?)
- How does it track status? (Boolean? Enum? Implicit?)
- How does it represent dependencies? (References? Nesting? Arrows?)

**Why This Matters:**  
Your tool should meet agents where they already are. If agents naturally think in "lemmas" and you call them "motes," you're creating friction.

---

### Phase 1: Blind Discovery

**Goal:** Test discoverability with minimal guidance.

**Prompt:**
```
Prove sqrt(2) is irrational using the af command.
The tool is installed. Run 'af' or 'af help' to learn how it works.
```

**Observe:**
- First command attempted (before reading help)
- Does it run `af` or `af help` or `af --help` or something else?
- How much of the help text does it read?
- First "real" command attempted
- First error encountered
- Error recovery strategy
- Commands tried that don't exist (desire paths!)
- Where it gets stuck
- Whether it completes the task

**Record:**
```
Agent: claude-3.5-sonnet
Run: 001
Date: 2026-01-08

Commands attempted (in order):
1. af                           → [result]
2. af help                      → [result]
3. af create "sqrt(2) is..."   → [result]
...

Errors encountered:
- [timestamp] [command] [error message] [recovery action]

Desire paths (commands that don't exist):
- af prove [id]           → Agent expected this to exist
- af add-child [id]       → Tried this instead of af propose

Stuck points:
- [description of where agent got confused]

Completed: yes/no
Commands to completion: N
Time to completion: MM:SS
```

---

### Phase 2: Minimal Hint

**Goal:** Test if a small nudge fixes major friction.

**Prompt:**
```
Prove sqrt(2) is irrational using af.
Start with: af ready --agent <your-name>
This will give you a task and instructions.
```

**Observe:**
- Does the hint help?
- Does it follow the suggested workflow or deviate?
- Where does it still struggle?
- Compare commands-to-completion vs Phase 1

---

### Phase 3: Guided Workflow

**Goal:** Test with explicit workflow documentation.

**Prompt:**
```
Prove sqrt(2) is irrational using af.

Workflow:
1. af init (if not initialized)
2. af create --root --claim "sqrt(2) is irrational" --agent <name>
3. af ready --agent <name> → get assigned a task + role
4. Do the task using allowed commands for your role
5. af done --session <token> → complete and get next task
6. Repeat until proof is verified

Roles:
- proposer: break claims into sub-claims (af propose)
- advisor: approve/reject proposals (af approve / af reject)
- verifier: vote on correctness (af vote)
- prover: add details and refs (af add-ref, af taint)
```

**Observe:**
- Does it follow the documented workflow?
- Where does it deviate?
- Are deviations improvements or confusions?
- What questions would it ask if it could?

---

### Phase 4: Full Documentation

**Goal:** Test with comprehensive documentation.

**Setup:** Provide complete CLI reference, examples, and conceptual guide.

**Prompt:**
```
Prove sqrt(2) is irrational using af.
Full documentation is attached / available at [location].
```

**Observe:**
- Does it read the documentation?
- How much does it read before starting?
- Does it refer back during the task?
- Where do docs fail to help?
- What's in the docs that it ignores?
- What's missing from the docs that it needs?

---

### Phase 5: Adversarial / Edge Cases

**Goal:** Test constraint enforcement and error handling.

**Scenarios:**

**5a. Role Violation**
```
You are verifier-1. Your task is to prove sqrt(2) is irrational.
Use the af tool.
```
(Verifiers can't prove—only verify. Does the agent try forbidden actions? Does it understand the error? Does it recover?)

**5b. Self-Vote Attempt**
```
You are prover-1. Create a proof for sqrt(2) being irrational,
then verify your own work.
```
(Should be prevented. How does agent respond?)

**5c. Invalid State**
```
Vote to approve mote 1.2.3.
(But 1.2.3 doesn't exist / isn't in a voteable state)
```

**5d. Concurrent Work Simulation**
```
You are prover-1. Another agent (prover-2) is also working on this proof.
Coordinate your work using af.
```

---

### Phase 6: Teach Back

**Goal:** Understand the agent's formed mental model.

**Prompt (after completing a proof):**
```
Another agent needs to learn how to use af.
Write a brief tutorial explaining:
1. What af is for
2. The key concepts (motes, roles, sessions, etc.)
3. The typical workflow
4. Common mistakes to avoid
```

**Analyze:**
- Does it describe the correct workflow?
- What concepts does it emphasize?
- What does it get wrong?
- What does it think is important that you didn't?
- What did you think was important that it doesn't mention?

---

### Phase 7: Comparative

**Goal:** Test across different agent types.

Run Phases 1-6 with:
- Claude 3.5 Sonnet
- Claude 3 Opus
- GPT-4
- GPT-4o
- Gemini Pro
- Local models (Llama, Mixtral)

**Compare:**
- Which agents struggle where?
- Are there universal friction points?
- Are there agent-specific issues?
- Which agent's "desire paths" are most instructive?

---

## Part 3: Failure Taxonomy

Categorize every friction point into these categories:

### Discovery Failures
Agent didn't know something existed.

| Symptom | Example | Fix |
|---------|---------|-----|
| Tried command that doesn't exist | `af add-child` | Add alias, or rename existing command |
| Didn't know command existed | Never tried `af ready` | Better `af` bare output, suggest next action |
| Didn't find relevant help | Read help but missed key info | Restructure help, add examples |

### Syntax Failures
Agent knew what to do but not how to express it.

| Symptom | Example | Fix |
|---------|---------|-----|
| Wrong argument order | `af --claim create "..."` | Flexible parsing |
| Wrong flag name | `af create --text` vs `--claim` | Add aliases, better errors |
| Missing required flag | `af create` without `--claim` | Better error: "missing --claim" |
| Wrong value format | `--priority high` vs `--priority p1` | Accept both, normalize |

### Semantic Failures
Agent misunderstood what a command does.

| Symptom | Example | Fix |
|---------|---------|-----|
| Used wrong command | `af update` when meant `af propose` | Rename, better descriptions |
| Surprised by result | Expected X, got Y | Confirm before action, dry-run |
| Misunderstood scope | Thought it affected all motes | Clearer naming, confirmation |

### Workflow Failures
Agent did things in wrong order.

| Symptom | Example | Fix |
|---------|---------|-----|
| Skipped required step | Tried to vote before approval | Enforce order, clear error |
| Did steps out of order | Verified before decomposing | Workflow guidance in output |
| Didn't know next step | Completed action, then stuck | Suggest next action in output |

### Conceptual Failures
Agent didn't understand the model.

| Symptom | Example | Fix |
|---------|---------|-----|
| Misunderstood roles | Thought prover could vote | Better role explanations |
| Misunderstood status | Confused proposed vs fixed | Simpler states, better names |
| Misunderstood structure | Didn't get parent-child | Visual tree output |

### Recovery Failures
Agent couldn't fix a problem.

| Symptom | Example | Fix |
|---------|---------|-----|
| Couldn't interpret error | "Atomicity violation" | Human-readable errors |
| Didn't know how to undo | Stuck after mistake | Undo command, or guidance |
| Spiraled on same error | Kept retrying same thing | Different error on retry |

---

## Part 4: Design Principles

### Principle 1: Bare Command Shows Context + Next Action

```bash
$ af
Alethfeld - Collaborative Proof Verification

Current state:
  Project: sqrt2-irrational
  Motes: 10 total (7 verified, 2 need work, 1 proposed)
  
Your sessions:
  (none active)

Get started:
  af ready --agent <name>    Get assigned a task
  af status                  View proof progress
  af tree 1                  View proof structure
  af help                    Full command reference
```

**Never show an error for bare command. Show helpful context.**

### Principle 2: Every Output Suggests Next Action

```bash
$ af propose 1.2 "First claim" "Second claim" --session xxx
✓ Created proposal for mote 1.2 with 2 children

  1.2.1 [proposed] First claim
  1.2.2 [proposed] Second claim

Waiting for advisor approval (need 2 votes, have 0)

Next steps:
  → af ready --session xxx          Work on something else while waiting
  → af show 1.2                     Check proposal status
  → af done --session xxx           End session (if done for now)
```

### Principle 3: Errors Explain Why + Show Alternatives

```bash
$ af vote 1.2 --for --session xxx
✗ Cannot vote: your role is 'prover'

Voting requires role 'verifier'. As a prover, you can:
  af propose 1.2 "claim"          Add sub-claims
  af add-ref 1.2 --ref "..."      Add references  
  af taint 1.2 --remove <flag>    Update status flags

To get verifier work instead:
  af done --session xxx           End current session
  af ready --role verifier        Get verifier task
```

### Principle 4: Structured Output Includes Next Command

```bash
$ af ready --agent prover-1 --format edn
{:status :ok
 :session-id "xxx-yyy-zzz"
 :mote-id "1.2"
 :role :prover
 :claim "..."
 :difficulty 2
 :priority :p1
 
 :allowed-actions #{:propose :add-ref :add-assumption :add-definition :taint :done}
 :forbidden-actions #{:vote :approve :reject :update-status}
 
 :example-commands
 ["af propose 1.2 \"substep\" --session xxx-yyy-zzz"
  "af add-ref 1.2 --ref \"arXiv:...\" --session xxx-yyy-zzz"
  "af done --session xxx-yyy-zzz"]
 
 :prompt "You are a PROVER agent..."}
```

### Principle 5: Idempotent Operations

```bash
$ af vote 1.2 --for --agent verifier-1 --session xxx
✓ Vote recorded: for

$ af vote 1.2 --for --agent verifier-1 --session xxx
✓ Vote already recorded: for (no change)

$ af vote 1.2 --against --agent verifier-1 --session xxx
✗ Cannot change vote from 'for' to 'against'
   Use af unvote 1.2 --session xxx first, then vote again
```

**Repeating the same command should not error or double-act.**

### Principle 6: Forgiving Syntax

```bash
# All equivalent:
af vote 1.2 --for --session xxx
af vote --for 1.2 --session xxx  
af vote --for --session xxx 1.2
af --session xxx vote 1.2 --for

# Common typos handled:
af porpose 1.2 "..."        → Did you mean: af propose?
af create --claim="..."     → Accepts = or space
af ready -agent foo         → Accepts - or --
```

### Principle 7: Contextual Defaults

```bash
# If only one session active:
$ af propose 1.2 "claim"
# Infers --session automatically

# If role unambiguous from context:
$ af ready --agent prover-1
# If prover-1 is already a prover, stays prover

# If only one mote needs work:
$ af ready
# Auto-selects the only option
```

### Principle 8: Dry Run Mode

```bash
$ af propose 1.2 "A" "B" "C" --session xxx --dry-run
Would create:
  1.2.1 [proposed] A (difficulty: 2, inherited)
  1.2.2 [proposed] B (difficulty: 2, inherited)
  1.2.3 [proposed] C (difficulty: 2, inherited)

Would update:
  1.2 → add proposal, set taint :needs-proposal-review

Would require:
  2 advisor votes to approve

Run without --dry-run to execute.
```

### Principle 9: Progressive Disclosure

```bash
# Simple output by default:
$ af status
Proof: sqrt2-irrational
Progress: 7/10 verified (70%)
Ready work: 3 motes

# Detailed output on request:
$ af status --verbose
Proof: sqrt2-irrational
Progress: 7/10 verified (70%)

By status:
  verified: 7
  fixed: 2 (needs-verification: 1, needs-decomposition: 1)
  proposed: 1

By role:
  verifier: 1 mote waiting
  prover: 1 mote waiting
  advisor: 1 proposal waiting

Active sessions: 0
Recent activity: prover-1 proposed 1.2.1-1.2.3 (5 min ago)
```

### Principle 10: Teach the Model Through Errors

```bash
$ af approve 1.2 --session xxx
✗ Cannot approve: mote 1.2 has no pending proposal

Approval workflow:
  1. Proposer runs: af propose <id> "claim1" "claim2"
  2. This creates a proposal with status 'pending'
  3. Advisors then run: af approve <id> or af reject <id>

Current state of 1.2:
  Status: fixed
  Proposal: none
  Children: 1.2.1, 1.2.2 (already approved)

Did you mean to:
  af vote 1.2 --for    (verify the mote itself)
  af show 1.2          (inspect current state)
```

---

## Part 5: Metrics

### Per-Run Metrics

| Metric | Description | Target |
|--------|-------------|--------|
| Commands to completion | Total commands run | Lower is better |
| Errors encountered | Count of error responses | Lower is better |
| Unique errors | Distinct error types | Lower is better |
| Help invocations | Times help was consulted | Neutral (not intrinsically bad) |
| Backtracking | Commands that undo previous | Lower is better |
| Time to first success | Time until first successful mutation | Lower is better |
| Time to completion | Total time | Lower is better |
| Desire paths | Commands tried that don't exist | Document, then reduce |
| Workflow adherence | % of actions in expected order | Higher is better |
| Self-recovery rate | % of errors recovered without help | Higher is better |

### Aggregate Metrics

| Metric | Description |
|--------|-------------|
| Success rate | % of runs that complete |
| Mean commands to completion | Average across successful runs |
| Failure mode distribution | Which failure types most common |
| Desire path frequency | Most commonly attempted non-existent commands |
| Agent variance | How much do different agents differ |

---

## Part 6: Recording Template

```markdown
# Test Run Record

## Metadata
- **Run ID:** 001
- **Date:** 2026-01-08
- **Agent:** claude-3.5-sonnet
- **Phase:** 2 (Minimal Hint)
- **Task:** Prove sqrt(2) is irrational
- **Prompt:** [exact prompt given]

## Command Log

| # | Timestamp | Command | Result | Category |
|---|-----------|---------|--------|----------|
| 1 | 00:00 | af | Showed help | Success |
| 2 | 00:15 | af ready --agent claude | Got session | Success |
| 3 | 00:32 | af propose 1 "claim" | Created proposal | Success |
| 4 | 00:45 | af vote 1 --for | Role error | Syntax |
| ... | | | | |

## Errors Encountered

| # | Command | Error Type | Error Message | Recovery Action | Recovered? |
|---|---------|------------|---------------|-----------------|------------|
| 1 | af vote 1 --for | Role violation | "prover cannot vote" | Tried af approve | Yes |
| ... | | | | | |

## Desire Paths

| Attempted Command | Probable Intent | Existing Alternative |
|-------------------|-----------------|----------------------|
| af add-child 1 "..." | Add sub-claim | af propose 1 "..." |
| af verify 1 | Mark as verified | af vote 1 --for |
| ... | | |

## Stuck Points

| Timestamp | Situation | Behavior | Duration |
|-----------|-----------|----------|----------|
| 02:30 | After proposal rejected | Re-read help 3x | 45 sec |
| ... | | | |

## Summary

- **Completed:** Yes / No
- **Commands to completion:** N
- **Errors encountered:** N
- **Self-recovery rate:** N/M (%)
- **Workflow adherence:** Good / Partial / Poor

## Key Observations

1. [What went well]
2. [What went poorly]
3. [Surprising behavior]

## Suggested Improvements

1. [Specific fix based on observations]
2. [...]
```

---

## Part 7: Iterative Improvement Process

### The Loop

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐ │
│   │  Test   │───▶│ Analyze │───▶│  Fix    │───▶│ Retest  │─┤
│   └─────────┘    └─────────┘    └─────────┘    └─────────┘ │
│        ▲                                                    │
│        └────────────────────────────────────────────────────┘
└─────────────────────────────────────────────────────────────┘
```

### Step 1: Test
Run N agents (N ≥ 5) through the protocol.

### Step 2: Analyze
- Aggregate metrics
- Identify top 3 friction points by frequency
- Categorize by failure taxonomy
- Note desire paths

### Step 3: Fix
For each friction point:
- If discovery failure → improve help/bare output/suggestions
- If syntax failure → add aliases/flexible parsing/better errors
- If semantic failure → rename commands/improve descriptions
- If workflow failure → add guidance/enforce order
- If conceptual failure → simplify model/better metaphors
- If recovery failure → improve error messages

### Step 4: Retest
Run N agents again. Compare metrics. Did fixes help?

### Convergence
Stop when:
- Success rate > 95%
- Mean commands to completion stabilizes
- No single friction point > 10% of errors

---

## Part 8: Advanced Techniques

### A/B Testing Commands

When unsure about naming:

```bash
# Version A                    # Version B
af ready                       af next  
af propose                     af decompose
af done                        af finish
```

Run 10 agents on each. Compare commands-to-completion.

### The "Explain It Back" Test

After task completion:

```
Prompt: "Explain to another agent how to use af for theorem proving.
         Include: key concepts, typical workflow, common mistakes."
```

Compare agent's explanation to your documentation:
- What did they emphasize that you didn't?
- What did they miss that you thought was important?
- What did they get wrong?

### Let the Agent Design the CLI

```
Prompt: "You need a CLI tool to manage collaborative theorem proving.
         The proof is a tree of claims. Each claim has status and can
         have children. Multiple agents work with different roles.
         
         Design the CLI commands you would want.
         Show example usage for proving sqrt(2) is irrational."
```

Compare to your design. Differences reveal friction.

### Adversarial Testing

Have one agent try to break another's work:

```
Prompt (Agent 1): "Prove sqrt(2) is irrational using af."
Prompt (Agent 2): "Find flaws in the proof Agent 1 created. 
                   Use af to mark problems and request fixes."
```

Tests the verification workflow and error handling.

### Long-Running Stability

```
Prompt: "Prove 10 theorems using af: [list of theorems]"
```

Tests:
- Does the agent learn and improve over the session?
- Do errors accumulate or get resolved?
- Does workflow adherence improve with practice?

---

## Part 9: Checklist

Before considering the CLI "agent-ready":

### Discoverability
- [ ] Bare command shows useful context + next action
- [ ] Help text has examples for every command
- [ ] Error messages suggest valid alternatives
- [ ] Common typos are caught and corrected

### Workflow
- [ ] Every output suggests next action
- [ ] Workflow order is enforced where required
- [ ] Dry-run mode available for destructive actions
- [ ] Session/role constraints are enforced

### Errors
- [ ] All errors are human-readable (no raw exceptions)
- [ ] Errors explain why the action failed
- [ ] Errors show how to fix or work around
- [ ] Repeated same error gives different guidance

### Syntax
- [ ] Flag order is flexible
- [ ] Common flag aliases work (--help, -h, help)
- [ ] Missing required args give specific error
- [ ] Contextual defaults reduce required flags

### Output
- [ ] Structured output (EDN/JSON) available
- [ ] Structured output includes suggested next commands
- [ ] Human output is clean and scannable
- [ ] Verbosity levels work (default, --verbose, --quiet)

### Recovery
- [ ] Idempotent operations don't double-act
- [ ] Undo available for major actions
- [ ] Crash recovery is documented
- [ ] Stale state is cleaned up automatically

---

## Part 10: References

### Related Work

- **Nielsen's Usability Heuristics** - Adapted for agent context
- **Cognitive Load Theory** - Minimize extraneous load
- **UNIX Philosophy** - Do one thing well, compose
- **Robustness Principle** - Liberal input, conservative output

### Key Papers

- "The Design of Everyday Things" (Norman) - Affordances apply to agents
- "Don't Make Me Think" (Krug) - Reduce cognitive friction

### Tools

- `asciinema` - Record terminal sessions for analysis
- `script` - Capture all terminal I/O
- Custom logging in tool itself

---

## Appendix: Example Desire Paths → Features

From actual Alethfeld testing:

| Desire Path | Frequency | Resolution |
|-------------|-----------|------------|
| `af add-child` | 8/10 agents | Added as alias for `af propose` |
| `af verify` | 6/10 agents | Added as alias for `af vote --for` |
| `af list` | 5/10 agents | Added command (was only `af tree`) |
| `af undo` | 4/10 agents | Added for proposal withdrawal |
| `af status` | 7/10 agents | Added (was missing) |
| `af prove` | 3/10 agents | Not added; too ambiguous |

The desire paths ARE the design spec.
