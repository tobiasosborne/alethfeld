# Alethfeld Experience Report: Proving sqrt(2) is Irrational

**Date:** 2026-01-10
**Tool Version:** Alethfeld v0.2.0
**Task:** Prove that the square root of 2 is irrational using collaborative multi-agent verification
**Outcome:** Success (100% verified, 7/7 motes)

---

## Executive Summary

I used the Alethfeld (`af`) command-line tool to construct and verify a formal proof that sqrt(2) is irrational. The process involved initializing a proof repository, decomposing the theorem into sub-claims, and orchestrating multiple AI subagents to review and verify each component. While the proof was ultimately successful, the experience revealed several friction points and opportunities for improvement in both the tool design and the multi-agent workflow.

---

## 1. Tool Overview

### What is Alethfeld?

Alethfeld is a CLI tool for **collaborative proof verification**. It models proofs as a directed acyclic graph (DAG) of "motes" (claims), with a role-based permission system that separates concerns:

| Role | Responsibility |
|------|---------------|
| Proposer | Decompose claims into sub-claims |
| Advisor | Review and approve/reject proposals |
| Prover | Add references, definitions, assumptions |
| Verifier | Vote on claim validity |
| Counterexample | Find flaws and edge cases |
| Ref-checker | Validate external citations |

### Core Workflow

```
Create Root Claim → Propose Decomposition → Advisor Approval → Verification Votes → Complete
```

---

## 2. Step-by-Step Experience

### 2.1 Initialization

**Commands used:**
```bash
af init
af create --root --claim "The square root of 2 is irrational"
```

**Experience:** Smooth. The initialization was straightforward and the feedback was clear.

**Friction:** None at this stage.

---

### 2.2 Understanding the Workflow

**Challenge:** The tool has many commands and roles. Understanding how they fit together required experimentation.

**What helped:**
- `af --help` provided a good overview
- `af roles` explained each role clearly
- `af status` gave useful next-step suggestions

**What didn't help:**
- `af workflow` command failed with a FileNotFoundException (missing `prompts/workflow.md`)
- No built-in tutorial or guided walkthrough

**Friction Level:** Medium - Required trial and error to understand the state machine.

---

### 2.3 Initial State Confusion

**Problem:** After creating the root claim, it was marked as `[fixed]` (leaf node), meaning it couldn't be decomposed by a proposer.

```
1 [fixed] (needs-verification)
The square root of 2 is irrational
```

**Expected:** A theorem should be decomposable by default.

**Workaround:** Used the `prover` role instead, which can propose decompositions on fixed motes.

**Friction Level:** High - This was confusing and non-intuitive. The difference between `fixed` and decomposable motes wasn't clear from the documentation.

**Suggested Improvement:**
- Root claims should default to decomposable
- Or provide a `--decomposable` flag on `af create`
- Better documentation on mote states

---

### 2.4 Claiming Work

**Problem:** The `af claim` command threw a Java exception:

```
java.lang.ClassCastException: class java.lang.String cannot be cast to class clojure.lang.IFn
```

**Workaround:** Used `af ready --name <agent> --role <role>` instead, which auto-claims work.

**Friction Level:** High - A core command was broken.

**Suggested Improvement:** Fix the bug. The `claim` command should work as documented.

---

### 2.5 Proposing the Decomposition

**Command used:**
```bash
af propose 1 --session <token> \
  --claim "Assume sqrt(2) = p/q where p and q are coprime integers with q != 0" \
  --claim "If sqrt(2) = p/q then 2q^2 = p^2" \
  --claim "If 2q^2 = p^2 then p is even" \
  --claim "If p is even (p = 2k) and 2q^2 = p^2, then q is also even" \
  --claim "If both p and q are even, they share a common factor of 2, contradicting coprimality" \
  --claim "By contradiction, sqrt(2) is irrational"
```

**Experience:** Excellent. The multi-claim syntax with `--claim` flags was intuitive and worked perfectly.

**Friction Level:** Low.

---

### 2.6 Advisor Review (Subagent)

**Approach:** Spawned a Bash subagent to act as an advisor.

**Subagent Behavior:**
- Successfully claimed the advisor job
- Reviewed the proposal structure
- Approved with reasoning
- Terminated cleanly

**Friction Level:** Low - The subagent followed instructions well.

---

### 2.7 Parallel Verification (Multiple Subagents)

**Approach:** Spawned 6 verifier subagents simultaneously to verify claims 1.1 through 1.6.

**Results:**

| Intended Target | Actual Result | Notes |
|-----------------|---------------|-------|
| Mote 1.1 | Verified 1.4 | Got different mote |
| Mote 1.2 | Verified 1 (root!) | Unexpected - verified parent |
| Mote 1.3 | No work available | Mote already claimed |
| Mote 1.4 | Verified 1.1 | Got different mote |
| Mote 1.5 | Verified 1.2 | Got different mote |
| Mote 1.6 | Verified 1.3 | Got different mote |

**Critical Issue:** The `af ready` command assigns jobs non-deterministically. There's no way to request a specific mote.

**Consequences:**
1. Race conditions - multiple agents competed for the same motes
2. Unpredictable assignment - agents didn't get their intended targets
3. One agent verified the root prematurely (though this didn't cause issues)
4. One agent found no work and had to report back without completing a task

**Friction Level:** Very High - This is a fundamental limitation for orchestrating parallel agents.

---

### 2.8 Completing the Remaining Verifications

After the first batch, motes 1.5 and 1.6 still needed verification. Spawned 2 more agents.

**Result:** Both completed successfully.

**Total agents spawned:** 9 (1 advisor + 8 verifiers, though only 7 verifications were needed)

---

## 3. Friction Points Summary

### Critical Issues

| Issue | Severity | Impact |
|-------|----------|--------|
| Non-deterministic job assignment | Critical | Cannot orchestrate parallel agents reliably |
| `af claim` command broken | High | Core functionality unavailable |
| Root motes default to `fixed` | High | Confusing initial state |

### Medium Issues

| Issue | Severity | Impact |
|-------|----------|--------|
| `af workflow` command broken | Medium | Documentation unavailable |
| No mote targeting in `af ready` | Medium | Inefficient agent coordination |
| Session tokens are very long | Low | Verbose commands |

### Minor Issues

| Issue | Severity | Impact |
|-------|----------|--------|
| `needs-refinement` taint persists after verification | Low | Cosmetic clutter |
| No progress percentage during verification | Low | Less visibility |

---

## 4. Ease of Use Assessment

### What Works Well

1. **Clear command structure** - Commands are logically named (`create`, `propose`, `vote`, `done`)
2. **Helpful next-steps** - After each command, the tool suggests what to do next
3. **Role descriptions** - `af roles` clearly explains each role's purpose
4. **Session context** - When claiming work, the tool provides full context including allowed/forbidden commands
5. **Multiple output formats** - `--format json` is useful for programmatic parsing
6. **Tree visualization** - `af tree` provides a clear view of proof structure

### What Needs Improvement

1. **Onboarding** - No tutorial, getting started guide, or example workflow
2. **State machine documentation** - The relationship between mote states (fixed, verified, needs-verification) isn't explained
3. **Error messages** - Java stack traces are not user-friendly
4. **Agent coordination** - The tool assumes single-agent usage; multi-agent scenarios need better support

### Ease of Use Score: 6/10

The tool is usable but requires significant experimentation to understand. The broken commands and unclear state machine reduce the score.

---

## 5. Recommendations for Improvement

### For the Tool

1. **Add `--mote <id>` flag to `af ready`**
   ```bash
   af ready --name verifier-1 --role verifier --mote 1.3
   ```
   This would eliminate race conditions in parallel agent scenarios.

2. **Add a reservation system**
   ```bash
   af reserve 1.3 --name verifier-1  # Reserve without claiming
   af claim-reservation <token>       # Claim when ready
   ```

3. **Fix broken commands**
   - `af claim` - ClassCastException
   - `af workflow` - FileNotFoundException

4. **Improve mote creation defaults**
   - Root theorems should be decomposable
   - Or add explicit `--fixed` / `--decomposable` flags

5. **Add batch operations**
   ```bash
   af vote-all --for 1.1 1.2 1.3 --reason "Valid mathematical steps"
   ```

6. **Shorten session tokens**
   - Current: `158b6d50-72df-402e-ae5e-951ab5db502d-05b921fa-e5be-4381-93b1-018a0deb5056`
   - Suggested: `s-158b6d50` (use prefix + first segment)

### For Multi-Agent Workflows

1. **Orchestrator mode** - A special role that can see all pending work and assign specific motes to agents

2. **Work queue visibility** - `af jobs --all` to see all pending work with IDs, allowing orchestrators to plan assignments

3. **Agent namespacing** - Allow agents to filter work by tags or difficulty to reduce conflicts

4. **Locking mechanism** - Explicit lock/unlock to prevent race conditions

---

## 6. Multi-Agent Workflow Analysis

### What the Tool Assumes

The tool seems designed for a **pull-based single-agent model**:
- One agent runs `af ready`
- Gets assigned whatever is next in the queue
- Completes work and terminates
- Repeat with a new agent

### What I Needed

A **push-based multi-agent model**:
- Orchestrator sees all pending work
- Assigns specific motes to specific agents
- Agents work in parallel without conflicts
- Orchestrator monitors progress

### Gap Analysis

| Feature | Tool Provides | I Needed |
|---------|---------------|----------|
| Job listing | `af ready --no-claim` | `af jobs --all` with mote IDs |
| Job assignment | Auto-assign next available | Assign specific mote |
| Parallel safety | None (race conditions) | Reservations or locks |
| Progress monitoring | `af status` (aggregate) | Per-mote status |

---

## 7. Session Log Summary

| Timestamp | Action | Agent | Result |
|-----------|--------|-------|--------|
| T+0 | Initialize repository | - | Success |
| T+1 | Create root claim | - | Success (but fixed state) |
| T+2 | Claim as verifier | verifier-agent | Tainted as needs-refinement |
| T+3 | Claim as prover | prover-agent | Success |
| T+4 | Propose decomposition | prover-agent | 6 children created |
| T+5 | Advisor review | advisor-agent | Approved |
| T+6 | Parallel verification | verifier-1 to 6 | 5 of 6 successful |
| T+7 | Final verification | verifier-5b, 6b | Complete |
| T+8 | Integrity check | - | 7/7 validated |

---

## 8. Conclusion

Alethfeld is a promising tool for collaborative proof verification with a solid conceptual foundation. The role-based permission system, DAG structure, and quorum voting create a robust framework for distributed mathematical reasoning.

However, the tool has significant friction points that impede multi-agent workflows:

1. **Non-deterministic job assignment** is the biggest obstacle to parallel agent orchestration
2. **Broken core commands** (`af claim`, `af workflow`) reduce reliability
3. **Unclear state machine** makes onboarding difficult

For single-agent sequential workflows, the tool works reasonably well. For parallel multi-agent scenarios like the one I attempted, additional coordination logic is needed outside the tool.

### Final Verdict

| Aspect | Rating |
|--------|--------|
| Conceptual design | 8/10 |
| Implementation quality | 5/10 |
| Single-agent usability | 7/10 |
| Multi-agent usability | 4/10 |
| Documentation | 4/10 |
| **Overall** | **5.5/10** |

The proof was completed successfully, but the process required workarounds and generated inefficiencies that better tooling could eliminate.

---

## Appendix: Final Proof Tree

```
1 [verified] The square root of 2 is irrational
+-- 1.1 [verified] Assume sqrt(2) = p/q where p and q are coprime integers with q != 0
+-- 1.2 [verified] If sqrt(2) = p/q then 2q^2 = p^2
+-- 1.3 [verified] If 2q^2 = p^2 then p is even
+-- 1.4 [verified] If p is even (p = 2k) and 2q^2 = p^2, then q is also even
+-- 1.5 [verified] If both p and q are even, they share a common factor of 2, contradicting coprimality
\-- 1.6 [verified] By contradiction, sqrt(2) cannot be expressed as p/q, therefore irrational
```

**Proof Status:** 100% Verified (7/7 motes)
**DAG Integrity:** Validated
