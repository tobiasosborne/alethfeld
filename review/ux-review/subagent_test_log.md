# Subagent Behavior Log

**Agent:** claude-opus-4.5 (orchestrator) + haiku subagents
**Run:** 002 (subagent pattern)
**Date:** 2026-01-09
**Task:** Prove sqrt(2) is irrational using the `af` command
**Pattern:** 1 subagent per job

## Test Design

- Orchestrator initializes project and creates root claim
- Each job (proposer, advisor, verifier) is handled by a separate subagent
- Subagents are given minimal context - just the job instructions
- Track: subagent count, success rate, coordination overhead

## Metrics (Final - Successful Run)

| Metric | Value |
|--------|-------|
| Subagents spawned | 5 |
| Successful completions | 5 |
| Failed/stuck subagents | 0 |
| Final verification | 80% (4/5 motes) |
| DAG validation | OK |

## Metrics (First Attempt - Failed due to race conditions)

| Metric | Value |
|--------|-------|
| Subagents spawned | ~12 |
| Successful completions | ~6 |
| Failed/stuck subagents | ~6 |
| Outcome | DAG corruption, had to restart |

## Subagent Log (Successful Run)

| # | Role | Mote | Status | Notes |
|---|------|------|--------|-------|
| 1 | proposer | 1 | SUCCESS | Decomposed root into 4 atomic children |
| 2 | advisor | 1 | SUCCESS | First approval vote |
| 3 | advisor | 1 | SUCCESS | Second approval - proposal approved |
| 4 | verifier | 1.2 | SUCCESS | Used vote-all, voted on 4 motes |
| 5 | verifier | 1.1 | SUCCESS | Used vote-all, voted on 4 motes - quorum reached |

## Subagent Log (Failed First Attempt)

| # | Role | Mote | Status | Notes |
|---|------|------|--------|-------|
| 1 | proposer | 1 | SUCCESS | Created 4 children |
| 2 | advisor | 1 | SUCCESS | First approval |
| 3 | advisor | 1.1 | PARTIAL | Got assigned to wrong mote, created extra proposal |
| 4 | advisor | 1 | SUCCESS | Second approval for mote 1 |
| 5 | advisor | 1.1 | SUCCESS | Approved 1.1's unexpected proposal |
| 6-11 | proposer | various | FAILED | Race condition: "missing-proposal-child" errors |
| 12 | verifier | 1.1.1.1 | FAILED | Blocked by DAG validation errors |

## Key Findings

### 1. Parallel Subagents Cause Race Conditions

When spawning multiple subagents in parallel for the same role type:
- They may claim different motes than expected
- One subagent may create proposals that conflict with another's work
- DAG validation errors cascade and block all further work

**First attempt failure mode:**
```
Spawned 6 proposers in parallel →
One created an unexpected proposal on 1.1 →
Created child 1.1.1 but not 1.1.2.1 →
DAG validation fails →
All subsequent operations blocked with "missing-proposal-child" error
```

### 2. Sequential Subagents Work Reliably

The successful run used:
1. **Sequential advisors** - one at a time to avoid claiming different motes
2. **Parallel verifiers** - safe because vote-all handles all motes atomically

### 3. Subagent Type Matters

| Subagent Type | Success Rate | Notes |
|---------------|--------------|-------|
| `general-purpose` | ~50% | Some refused to run `af` commands |
| `Bash` | 100% | Reliably executed commands |

The `Bash` subagent type is essential for this use case. `general-purpose` subagents sometimes claimed they couldn't execute the `af` command.

### 4. vote-all is Critical for Efficiency

Without `vote-all`, we'd need:
- 4 motes × 2 votes = 8 verifier subagents

With `vote-all`:
- 2 verifier subagents (one per quorum vote)

**Efficiency gain: 4x fewer verifier subagents**

## Recommendations for af Tool

### For Multi-Agent Support

1. **Add job locking/reservation**
   - `af ready --reserve` to reserve without claiming
   - Prevents race conditions when multiple agents query simultaneously

2. **Add batch operations for advisors**
   - `af approve-all --session X` to approve all pending proposals
   - Mirrors the useful `vote-all` pattern

3. **Better error recovery**
   - `af repair` command to fix DAG inconsistencies
   - `af unclaim --all` to release all stuck sessions

4. **Session management**
   - `af sessions` to list active sessions
   - Auto-expire sessions after timeout

### For Orchestrator Agents

1. **Use sequential subagents for proposals and advisors**
   - Parallel spawning creates race conditions

2. **Use `Bash` subagent type, not `general-purpose`**
   - More reliable command execution

3. **Use `--atomic` flag proactively**
   - Reduces depth of proof tree
   - Fewer subagents needed

4. **Use `vote-all` for verification**
   - Single subagent can vote on all pending motes

## Comparison: Manual vs Subagent

| Metric | Manual (Run 001) | Subagent (Run 002) |
|--------|------------------|-------------------|
| Commands to completion | ~55 | 15 (across 5 subagents) |
| Stuck points | 2 | 1 (race condition) |
| Final verification | 73% | 80% |
| Proof tree depth | 3 levels | 2 levels |
| Total motes | 19 | 5 |

The subagent approach is more efficient when:
- Using `--atomic` for leaf claims
- Running subagents sequentially for critical operations
- Using `vote-all` for batch verification
