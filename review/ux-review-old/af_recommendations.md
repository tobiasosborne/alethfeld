# Alethfeld (af) UX Recommendations for AI Agents

**Based on:** claude-opus-4.5 discoverability test
**Date:** 2026-01-09
**Task:** Prove sqrt(2) is irrational

---

## Executive Summary

The `af` tool has excellent contextual guidance through "Next steps" suggestions in command output. The main friction points are:
1. Discoverability of key flags (`--role`, `--atomic`)
2. Repetitive multi-session workflows for quorum-based operations
3. Ambiguous parameter naming (`--agent` vs `--role`)

---

## High Priority

### 1. Role Selection UX

**Problem:** The `--agent` vs `--role` distinction is confusing. I tried `af ready --agent advisor` expecting to get an advisor role, but `--agent` is just a name field.

**Impact:** Wasted a command and had to consult help to discover `--role` flag.

**Suggestions:**
- Rename `--agent` to `--name` to avoid semantic confusion
- Support positional argument: `af ready advisor` (role as first arg)
- Add contextual hint when `--agent` value matches a role name:
  ```
  Note: "advisor" looks like a role. Did you mean --role advisor?
  ```

---

### 2. Atomic Mote Discovery

**Problem:** Spent ~5 commands trying to figure out how to handle leaf nodes that don't need decomposition. Tried prover role, verifier role, and `af update` before discovering `--atomic` flag in `af propose --help`.

**Impact:** Significant time spent exploring wrong paths.

**Suggestions:**
- When a proposer claims a difficulty-1 mote, add hint:
  ```
  Hint: If this claim is self-evident, use --atomic flag to skip decomposition
  Example: af propose 1.1 --claim "..." --atomic
  ```
- Include `--atomic` in the COMMANDS section of proposer context:
  ```
  COMMANDS:
  af propose 1.1 --claim "substep" --difficulty N
  af propose 1.1 --claim "leaf claim" --atomic    # For self-evident claims
  ```

---

### 3. Batch Operations for Quorum

**Problem:** Required 8 separate advisor sessions (2 votes × 4 proposals) and 2 verifier sessions. Each required: claim job → vote → done → repeat.

**Impact:** Tedious and token-intensive for AI agents.

**Suggestions:**

**Option A: Multi-claim sessions**
```bash
af ready --agent claude --role advisor --max 4  # Claim up to 4 jobs
af approve-all --session X --reason "Valid"      # Batch approve
af done --session X
```

**Option B: Batch commands without sessions**
```bash
af approve 1.1 1.2 1.3 1.4 --agent claude --reason "Valid"
af vote-all --for --agent claude --reason "Valid"  # Already exists, works well
```

**Option C: Quorum auto-fill for single-agent workflows**
```bash
af ready --agent claude --role advisor --auto-quorum
# Automatically applies enough votes to reach quorum
```

---

## Medium Priority

### 4. Session Token Ergonomics

**Problem:** Session tokens are 73-character UUIDs, difficult to work with in commands.

**Current:**
```bash
af approve 1.1 --session 3d7812e3-7303-4072-9e74-35c274c9b697-31ddb905-f561-42e6-8d8f-92bd6ca7467e
```

**Suggestions:**
- Support `@current` or `@last` aliases:
  ```bash
  af approve 1.1 --session @current
  ```
- Environment variable injection:
  ```bash
  export AF_SESSION=$(af ready --agent claude --role advisor --quiet)
  af approve 1.1  # Auto-uses AF_SESSION
  ```
- Shorter session IDs (first 8 chars of UUID)

---

### 5. Progress Visibility

**Problem:** `af status` shows percentage but not what work remains by type.

**Current output:**
```
sqrt(2) is irrational - 73% verified (14/19)
Ready work: 14 motes (14 verifier)
```

**Suggested enhancement:**
```
sqrt(2) is irrational - 73% verified (14/19)

Progress by stage:
  ✓ Proposer work:    0 remaining
  ✓ Advisor reviews:  0 remaining (all proposals approved)
  ✓ Verifier votes:   0 remaining (14/14 at quorum)

Structure: 5 intermediate + 14 leaf motes
Next action: Run 'af check' to validate DAG integrity
```

---

### 6. Quorum Visibility

**Problem:** Didn't know 2 votes were required until seeing "Waiting for more advisor votes."

**Current:**
```
VOTES: 1 approve, 0 reject
```

**Suggested:**
```
VOTES: 1/2 approve, 0 reject (need 1 more for quorum)
```

Or in status output:
```
Ready work: 4 motes (4 advisor - each needs 2 votes)
```

---

## Low Priority

### 7. Help Command Consistency

**Problem:** `af help` shows minimal output; `af --help` shows full command list.

**Current behavior:**
```bash
$ af help
Show help
Usage: af help [command]
```

**Suggestion:** Make `af help` (no args) show the same output as `af --help`.

---

### 8. Workflow Documentation Command

**Problem:** The roles exist but overall workflow isn't obvious without experimentation.

**Suggestion:** Add `af workflow` or `af guide` command:

```
Alethfeld Proof Workflow
========================

1. INITIALIZE
   af init --name "My Proof"
   af create --root --claim "Main theorem"

2. DECOMPOSE (proposer role)
   af ready --agent <name> --role proposer
   af propose <id> --claim "substep 1" --claim "substep 2"
   Use --atomic for self-evident claims that need no further decomposition

3. REVIEW (advisor role)
   af ready --agent <name> --role advisor
   af approve <id> --reason "..."
   Requires 2 approvals per proposal

4. VERIFY (verifier role)
   af ready --agent <name> --role verifier
   af vote <id> --for --reason "..."
   af vote-all --for --reason "..."  # Batch vote
   Requires 2 votes per leaf mote

5. VALIDATE
   af check  # Verify DAG integrity
   af tree 1 # View proof structure

Optional roles: prover, ref-checker, counterexample
```

---

### 9. Parent Mote Status Clarity

**Problem:** After all 14 leaf motes were verified, the 5 parent motes remained "fixed" (not "verified"), leaving the proof at 73%.

**Questions this raises:**
- Is the proof complete?
- Do parent motes need separate verification?
- Why don't they auto-promote?

**Suggestions:**
- Auto-promote parent status when all children are verified
- Or explain in `af status`:
  ```
  73% verified (14/19)
  Note: 5 intermediate motes are "fixed" (decomposed).
        Verification applies to leaf motes only.
  ```

---

## What Works Well

These patterns should be preserved and expanded:

1. **Contextual "Next steps"** - Every command shows relevant follow-up actions
2. **Role-specific instructions** - Clear ALLOWED/FORBIDDEN commands per session
3. **`vote-all` command** - Batch operations are agent-friendly
4. **`af tree` visualization** - Clear proof structure display
5. **Session-based isolation** - Prevents accidental cross-contamination

---

## Summary Table

| Issue | Friction | Fix Complexity | Priority |
|-------|----------|----------------|----------|
| `--agent` vs `--role` confusion | High | Low | High |
| Discovering `--atomic` flag | High | Low | High |
| Batch advisor/verifier work | Medium | Medium | High |
| Long session tokens | Low | Low | Medium |
| Progress visibility | Medium | Medium | Medium |
| Quorum visibility | Medium | Low | Medium |
| `af help` vs `af --help` | Low | Low | Low |
| Workflow documentation | Low | Low | Low |
| Parent mote status clarity | Low | Medium | Low |

---

## Appendix: Test Statistics

- **Commands to completion:** ~55
- **Total motes created:** 19 (5 intermediate + 14 leaves)
- **Final verification:** 73% (14/19)
- **Stuck points:** 2 (role selection, atomic discovery)
- **Errors encountered:** 0 significant
- **Help consultations:** 4 (`af ready --help`, `af --help`, `af roles`, `af propose --help`)
