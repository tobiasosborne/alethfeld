# Agent Discovery Test Report: Alethfeld (af) Tool

**Agent:** claude-3.5-sonnet (via general-purpose subagent)
**Run ID:** 001
**Date:** 2026-01-09
**Task:** Prove sqrt(2) is irrational using the `af` command
**Guidance Level:** Minimal (told tool exists, suggested `af` or `af help`)

---

## Executive Summary

The agent successfully completed the proof task in **76 commands**, but encountered significant friction discovering the correct role names for the collaborative workflow. The primary stuck point was role naming conventions—the agent tried 7 invalid role names before discovering the correct one (`advisor`) through an indirect method (`af ready --no-claim`).

| Metric | Value |
|--------|-------|
| Completed | Yes |
| Total Commands | 76 |
| Help Commands | 11 |
| Errors Encountered | 9+ |
| Desire Paths Identified | 8 |
| Major Stuck Points | 1 |

---

## 1. Initial Discovery Behavior

### First Command Attempted
```
af help
```
The agent chose `af help` rather than running `af` bare or `af --help`. This suggests a preference for explicit help invocations.

### Help Exploration Pattern
The agent systematically explored help for multiple subcommands:

| Order | Command | Purpose |
|-------|---------|---------|
| 1 | `af help` | Initial orientation |
| 2 | `af` | List all commands |
| 3 | `af init --help` | Learn initialization |
| 4 | `af create --help` | Learn claim creation |
| 5 | `af propose --help` | Learn proposal system |
| 6 | `af claim --help` | Learn claim/session system |
| 7 | `af approve --help` | Learn approval workflow |
| 8 | `af done --help` | Learn session termination |
| 9 | `af config --help` | Troubleshooting roles |
| 10 | `af show --help` | Inspect mote state |
| 11 | `af ready --help` | Discover available jobs |
| 12 | `af vote-all --help` | Batch voting |
| 13 | `af vote --help` | Individual voting |

**Observation:** The agent read help incrementally as needed rather than front-loading all documentation. This is an efficient just-in-time learning strategy.

---

## 2. Command Sequence Analysis

### Phase 1: Initialization (Commands 1-6)
```
af help                                          → Orientation
af                                               → Command listing
af init --help                                   → Learn syntax
af init --name "Sqrt2 Irrational Proof"          → Create project
af create --help                                 → Learn syntax
af create --root --claim "sqrt(2) is irrational" → Create root mote
```
**Result:** Smooth progression, no errors.

### Phase 2: Role Discovery Crisis (Commands 7-35)
This phase contained the most friction. The agent needed to:
1. Claim a mote to work on it
2. Propose a decomposition
3. Get the proposal approved
4. Get the claims verified

The agent understood the workflow but struggled with role names:

```
af claim 1 --agent prover --role decomposer  → ERROR: Invalid role
af claim 1 --agent prover --role prover      → Success (lucky guess)
af propose 1 --session ... (6 claims)        → Success
af approve 1 --session ...                   → ERROR: prover cannot approve
```

The agent then entered a trial-and-error loop trying to find a role that could approve:

| Attempt | Role Tried | Result |
|---------|-----------|--------|
| 1 | `reviewer` | Invalid role |
| 2 | `verifier` | Valid but cannot approve |
| 3 | `critic` | Invalid role |
| 4 | `judge` | Invalid role |
| 5 | `approver` | Invalid role |
| 6 | `admin` | Invalid role |
| 7 | `arbiter` | Invalid role |

**Breakthrough:** The agent ran `af ready --no-claim` which revealed:
```
Available job: mote 1, role: advisor
```

This exposed the correct role name, allowing progress to continue.

### Phase 3: Approval Workflow (Commands 36-42)
```
af claim 1 --agent advisor1 --role advisor   → Success
af approve 1 --session ... --reason ...      → First approval
af done --session ...                        → End session
af claim 1 --agent advisor2 --role advisor   → Second advisor
af approve 1 --session ... --reason ...      → Quorum met, children promoted
```
**Result:** Smooth once role was known.

### Phase 4: Verification Loop (Commands 43-74)
The agent efficiently verified all 6 child motes plus the root:

```
For each mote (1.1 through 1.6, then 1):
  af claim [mote] --agent verifier1 --role verifier
  af vote [mote] --session ... --for --reason ...
  af done --session ...
  af claim [mote] --agent verifier2 --role verifier
  af vote [mote] --session ... --for --propagate
  af done --session ...
```

**Optimization observed:** Agent started chaining commands with `&&` to reduce round-trips.

### Phase 5: Validation (Commands 75-76)
```
af show 1   → Confirmed status: verified
af check    → DAG validation passed
```

---

## 3. Errors Encountered

| # | Command | Error | Recovery Action |
|---|---------|-------|-----------------|
| 1 | `af claim --role decomposer` | Invalid role | Tried "prover" |
| 2 | `af approve` (as prover) | Role not permitted | Searched for approval role |
| 3 | `af claim --role reviewer` | Invalid role | Tried "verifier" |
| 4 | `af approve` (as verifier) | Role not permitted | Continued searching |
| 5 | `af claim --role critic` | Invalid role | Tried "judge" |
| 6 | `af claim --role judge` | Invalid role | Tried "approver" |
| 7 | `af claim --role approver` | Invalid role | Tried "admin" |
| 8 | `af claim --role admin` | Invalid role | Tried "arbiter" |
| 9 | `af claim --role arbiter` | Invalid role | Used `af ready` to discover |

### Error Recovery Strategies Employed

1. **Synonym guessing:** Tried semantically similar role names
2. **Config inspection:** Read `.alethfeld/config.edn` looking for role definitions
3. **Source code reading:** Read the `af` wrapper script to understand tool structure
4. **Job queue inspection:** Used `af ready --no-claim` to see what roles the system expected

**Most effective recovery:** `af ready --no-claim` provided the breakthrough by showing pending jobs with their required roles.

---

## 4. Desire Paths

These are commands or features the agent expected to exist but didn't:

| Expected Command | Agent's Mental Model |
|-----------------|---------------------|
| `af help roles` | List all valid role names |
| `af roles` | Show available roles |
| `--role reviewer` | A "reviewer" should review/approve things |
| `--role critic` | A "critic" should evaluate claims |
| `--role judge` | A "judge" should make decisions |
| `--role approver` | An "approver" should approve proposals |
| `--role admin` | An "admin" should have elevated access |
| `--role decomposer` | A "decomposer" should break down claims |

### Analysis

The agent's mental model mapped common English terms for review/approval activities onto expected role names. The actual roles (`prover`, `advisor`, `verifier`) follow a different naming convention that wasn't intuitive.

**Design Recommendation:** Consider adding:
- `af roles` command to list valid roles with descriptions
- Role aliases (e.g., `reviewer` → `advisor`)
- Better error messages: "Invalid role 'reviewer'. Valid roles: prover, advisor, verifier"

---

## 5. Stuck Points

### Primary Stuck Point: Role Discovery (Commands 16-35)

**Duration:** ~20 commands of trial and error

**Symptoms:**
- Repeated invalid role errors
- Guessing semantically similar names
- Reading source code and config files
- General confusion about workflow

**Root Cause:**
- No command to list valid roles
- Error messages didn't suggest valid alternatives
- Role names don't match common terminology

**Resolution:**
- `af ready --no-claim` revealed the expected role name

**Time Cost:** Approximately 25% of total commands were spent on role discovery

---

## 6. Workflow Understanding

The agent eventually understood the Alethfeld workflow:

```
┌─────────────────────────────────────────────────────────────┐
│                    ALETHFELD WORKFLOW                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. CREATE          af create --root --claim "..."          │
│       │                                                     │
│       ▼                                                     │
│  2. CLAIM           af claim [id] --role prover             │
│       │                                                     │
│       ▼                                                     │
│  3. PROPOSE         af propose [id] --session ... claims    │
│       │                                                     │
│       ▼                                                     │
│  4. APPROVE (x2)    af claim --role advisor                 │
│       │             af approve [id] --session ...           │
│       │             (requires 2 advisors for quorum)        │
│       ▼                                                     │
│  5. VERIFY (x2)     af claim --role verifier                │
│       │             af vote [id] --session ... --for        │
│       │             (requires 2 verifiers for quorum)       │
│       ▼                                                     │
│  6. PROPAGATE       Verification propagates to parent       │
│                     when all children verified              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 7. Proof Structure Created

The agent constructed a valid proof by contradiction:

```
ROOT (Mote 1): "sqrt(2) is irrational" [VERIFIED]
│
├── 1.1: Assume sqrt(2) = p/q in lowest terms (gcd(p,q) = 1) [VERIFIED]
│
├── 1.2: Squaring gives p² = 2q² [VERIFIED]
│
├── 1.3: Therefore p² is even, so p is even [VERIFIED]
│
├── 1.4: Let p = 2k for some integer k [VERIFIED]
│
├── 1.5: Substituting: 4k² = 2q², so q² = 2k², meaning q is even [VERIFIED]
│
└── 1.6: Both p,q even contradicts gcd(p,q) = 1. QED. [VERIFIED]
```

**Final DAG Status:**
- Total motes: 7
- Schema errors: 0
- DAG errors: 0
- Validation: Passed

---

## 8. Recommendations for Tool Improvement

### High Priority

1. **Add `af roles` command**
   ```
   $ af roles
   Available roles:
     prover    - Creates and decomposes claims
     advisor   - Reviews and approves proposals (2 required)
     verifier  - Verifies atomic claims (2 required)
   ```

2. **Improve error messages**
   ```
   Current:  "Invalid role"
   Better:   "Invalid role 'reviewer'. Did you mean 'advisor'?
             Run 'af roles' to see all valid roles."
   ```

3. **Add role aliases**
   - `reviewer` → `advisor`
   - `approver` → `advisor`
   - `validator` → `verifier`

### Medium Priority

4. **Include roles in main help output**
5. **Add `--list-roles` flag to `af claim`**
6. **Create onboarding tutorial:** `af tutorial`

### Low Priority

7. **Add tab completion for role names**
8. **Create `af workflow` command showing the state machine**

---

## 9. Metrics Summary

| Category | Count | % of Total |
|----------|-------|------------|
| Help/discovery commands | 13 | 17% |
| Setup commands | 6 | 8% |
| Role-discovery errors | 19 | 25% |
| Successful proof commands | 38 | 50% |
| **Total** | **76** | **100%** |

**Efficiency Analysis:**
- Without role discovery friction: ~45-50 commands estimated
- Overhead from poor discoverability: ~25-30 commands (35-40%)

---

## 10. Conclusions

### What Worked Well
- Help system was comprehensive once found
- `af ready --no-claim` provided crucial discoverability
- Workflow was logical once roles understood
- Error messages for workflow violations were clear

### What Needs Improvement
- Role names not discoverable
- No `af roles` or similar command
- Error messages don't suggest alternatives
- Role naming convention not intuitive

### Agent Behavior Insights
- Preferred `af help` over bare `af` for initial discovery
- Used just-in-time help rather than reading all docs upfront
- Employed synonym-guessing as primary error recovery
- Resorted to source code inspection when stuck
- `af ready` was the key breakthrough command

---

## Appendix: Raw Command Log

<details>
<summary>Click to expand full command sequence</summary>

```
1.  af help                                          → Help text
2.  af                                               → Command list
3.  af init --help                                   → Init usage
4.  af init --name "Sqrt2 Irrational Proof"          → Project created
5.  af create --help                                 → Create usage
6.  af create --root --claim "sqrt(2) is irrational" → Root mote id=1
7.  af propose --help                                → Propose usage
8.  af claim --help                                  → Claim usage
9.  af claim 1 --role decomposer                     → ERROR: Invalid role
10. af claim 1 --role prover                         → Success, got token
11. af propose 1 --session ... (6 claims)            → Proposal created
12. af approve --help                                → Approve usage
13. af approve 1 --session ...                       → ERROR: prover cannot approve
14. af done --help                                   → Done usage
15. af done --session ...                            → Session ended
16. af claim 1 --role reviewer                       → ERROR: Invalid role
17. af claim 1 --role verifier                       → Success
18. af approve 1 --session ...                       → ERROR: verifier cannot approve
19. af vote --help                                   → Vote usage
20. af done --session ...                            → Session ended
21. af claim 1 --role critic                         → ERROR: Invalid role
22. af claim 1 --role judge                          → ERROR: Invalid role
23. af config --help                                 → Config usage
24. af config list                                   → Config values
25. ls -la .alethfeld/                               → Directory listing
26. [Read config.edn]                                → Config contents
27. af claim 1 --role approver                       → ERROR: Invalid role
28. af show --help                                   → Show usage
29. af show 1                                        → Mote details
30. af claim 1 --role admin                          → ERROR: Invalid role
31. af claim 1 --role arbiter                        → ERROR: Invalid role
32. which af && file $(which af)                     → Found wrapper
33. [Read af wrapper script]                         → Script contents
34. af ready --help                                  → Ready usage
35. af ready --no-claim                              → Found: role advisor!
36. af claim 1 --role advisor                        → Success
37. af approve 1 --session ... --reason ...          → First approval
38. af done --session ...                            → Session ended
39. af claim 1 --agent advisor2 --role advisor       → Success
40. af approve 1 --session ... --reason ...          → Quorum met
41. af done --session ...                            → Session ended
42. af show 1                                        → Children visible
43. af show 1.1                                      → Needs verification
44. af vote-all --help                               → Vote-all usage
45-74. [Verification loop for motes 1.1-1.6 and 1]  → All verified
75. af show 1                                        → Status: verified
76. af check                                         → DAG valid
```

</details>

---

*Report generated: 2026-01-09*
*Test framework: Agent UX Discovery Study*
