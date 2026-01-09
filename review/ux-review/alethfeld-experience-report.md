# Alethfeld CLI Experience Report

**Date:** 2026-01-09
**Tool Version:** Alethfeld v0.1.0-SNAPSHOT
**Task:** Prove √2 is irrational using collaborative proof verification

---

## Executive Summary

Alethfeld is a CLI tool for collaborative theorem proving where proofs are structured as directed acyclic graphs (DAGs) of claims called "motes." Multiple agents with different roles work together to propose, review, and verify proof steps. While the underlying model is sound and well-designed, the CLI interface has significant usability friction that impedes adoption.

---

## 1. Discoveries

### 1.1 Core Architecture

Alethfeld implements a **distributed proof verification system** with the following components:

| Component | Description |
|-----------|-------------|
| **Motes** | Atomic claims with hierarchical Lamport-style IDs (e.g., `1`, `1.2`, `1.2.3`) |
| **DAG Structure** | Proofs form a tree where parent claims are supported by child claims |
| **Role-Based Access** | Six roles with distinct permissions control who can perform actions |
| **Quorum Voting** | Both proposals and verifications require configurable vote thresholds |
| **Session Locking** | Pessimistic concurrency via claimed sessions prevents conflicts |

### 1.2 Role System

The tool implements six distinct roles, discovered by extracting the schema from the JAR:

```clojure
(def Role
  "Agent role types."
  [:enum :proposer :advisor :prover :verifier :ref-checker :counterexample])
```

| Role | Allowed Actions |
|------|-----------------|
| `proposer` | `propose`, `done`, `taint-add` |
| `advisor` | `approve`, `reject`, `done`, `taint-add` |
| `verifier` | `vote`, `done`, `taint-add` |
| `prover` | Unknown (not tested) |
| `ref-checker` | Unknown (not tested) |
| `counterexample` | Unknown (not tested) |

### 1.3 Status Lifecycle

Motes transition through states based on votes and approvals:

```
┌──────────┐              ┌───────┐              ┌──────────┐
│ proposed │──(approve)──▶│ fixed │──(verify)───▶│ verified │
└──────────┘              └───────┘              └──────────┘
      │                        │
      │ (reject)               │ (refute)
      ▼                        ▼
┌──────────┐              ┌─────────┐
│ rejected │              │ refuted │
└──────────┘              └─────────┘
```

### 1.4 Taint Flags

Motes carry work-indicator flags that signal needed actions:

- `:needs-decomposition` — Claim needs to be broken into sub-claims
- `:needs-proposal-review` — Proposed children await approval
- `:needs-votes` — Claim has votes but hasn't reached quorum
- `:needs-verification` — Claim ready for verification voting
- `:needs-refs` — References need to be added
- `:needs-counterexample` — Counterexample search needed

### 1.5 Configuration

Default configuration discovered via `af config list`:

```clojure
{:project-name "Alethfeld Project"
 :version "0.1"
 :default-difficulty 3
 :vote-quorum 2
 :proposal-quorum 2
 :claim-timeout-minutes 30}
```

---

## 2. Friction Points

### 2.1 Critical: Role Discovery Failure

**Problem:** The `--help` output does not list valid role values. Users must guess.

**Experience:** I attempted six invalid roles before resorting to JAR extraction:

```bash
$ af claim 1 --agent reviewer1 --role reviewer
Failed to validate "--role reviewer": Invalid role

$ af claim 1 --agent reviewer1 --role author
Failed to validate "--role author": Invalid role

$ af claim 1 --agent reviewer1 --role judge
Failed to validate "--role judge": Invalid role

$ af claim 1 --agent reviewer1 --role arbiter
Failed to validate "--role arbiter": Invalid role

$ af claim 1 --agent reviewer1 --role assessor
Failed to validate "--role assessor": Invalid role

$ af claim 1 --agent reviewer1 --role curator
Failed to validate "--role curator": Invalid role
```

**Resolution:** Extracted `alethfeld/schema.clj` from the JAR to find valid roles.

**Recommendation:** Add `Valid roles: proposer, advisor, prover, verifier, ref-checker, counterexample` to help output.

### 2.2 High: Verbose Session Management

**Problem:** Every mutation requires three commands and manual UUID handling.

**Experience:** A single verification vote requires:

```bash
# Step 1: Claim (returns 72-character UUID)
$ af claim 1.1 --agent verifier1 --role verifier
{:session-id "f6c23d76-983c-4f3c-b68e-c747db975b3d-b8c85093-28e5-4b5f-8e93-629beb854c53", ...}

# Step 2: Act (must copy-paste UUID)
$ af vote 1.1 --session "f6c23d76-983c-4f3c-b68e-c747db975b3d-b8c85093-28e5-4b5f-8e93-629beb854c53" --for

# Step 3: Release (must copy-paste UUID again)
$ af done --session "f6c23d76-983c-4f3c-b68e-c747db975b3d-b8c85093-28e5-4b5f-8e93-629beb854c53"
```

**Impact:** Verifying 6 claims with 2 verifiers = 36 commands with 24 UUID copy-pastes.

**Recommendation:** Implement auto-session mode or session aliasing.

### 2.3 High: Hidden Quorum Requirements

**Problem:** Nothing indicates that 2 votes are needed until you see `:quorum-status :pending`.

**Experience:** After first vote:
```clojure
{:quorum-status :pending}  ; What does this mean? How many more needed?
```

Had to run `af config list` to discover `:vote-quorum 2`.

**Recommendation:** Show progress: `[1/2 votes needed]` in output.

### 2.4 Medium: Dual Voting Systems Confusion

**Problem:** Proposals and verifications use different commands and roles.

| Action | Command | Role Required |
|--------|---------|---------------|
| Approve decomposition | `af approve` | `advisor` |
| Reject decomposition | `af reject` | `advisor` |
| Verify claim valid | `af vote --for` | `verifier` |
| Refute claim | `af vote --against` | `verifier` |

**Experience:** Attempted to approve as verifier:
```bash
$ af approve 1 --session "..."
Error: Action not allowed for your role.
Your role: verifier
Attempted action: approve
Allowed actions: vote, done, taint-add
```

The error was helpful but came after trial-and-error.

**Recommendation:** Document role-action matrix in help or provide `af roles --verbose`.

### 2.5 Medium: EDN Output as Default

**Problem:** EDN (Extensible Data Notation) is Clojure-native but unfamiliar to most users.

**Experience:** Output like `#inst "2026-01-09T15:43:37.380-00:00"` and `:needs-decomposition` requires Clojure knowledge.

**Recommendation:** Human-readable default output with `--edn` or `--json` flags for scripts.

### 2.6 Low: No Tree Visualization

**Problem:** Understanding proof structure requires mentally parsing parent-child relationships.

**Experience:** Had to infer structure from IDs (1, 1.1, 1.2, etc.) rather than seeing it visually.

**Recommendation:** Add `af tree [ID]` command for ASCII tree visualization.

---

## 3. Key Concepts

### 3.1 Conceptual Model

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           ALETHFELD PROJECT                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         PROOF DAG                                │    │
│  │                                                                  │    │
│  │         ┌─────────────────────────────────────┐                 │    │
│  │         │  Mote 1: "√2 is irrational"         │                 │    │
│  │         │  status: :verified                  │                 │    │
│  │         │  votes: [{:agent "v1" :vote :for}   │                 │    │
│  │         │          {:agent "v2" :vote :for}]  │                 │    │
│  │         └──────────────────┬──────────────────┘                 │    │
│  │                            │                                     │    │
│  │    ┌───────────┬───────────┼───────────┬───────────┐            │    │
│  │    ▼           ▼           ▼           ▼           ▼            │    │
│  │ ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐           │    │
│  │ │ 1.1  │   │ 1.2  │   │ 1.3  │   │ 1.4  │   │ 1.5  │ ...       │    │
│  │ └──────┘   └──────┘   └──────┘   └──────┘   └──────┘           │    │
│  │                                                                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐         │
│  │     AGENTS      │  │    SESSIONS     │  │     CONFIG      │         │
│  │  - verifier1    │  │  - mote claims  │  │  - quorums      │         │
│  │  - verifier2    │  │  - timeouts     │  │  - difficulty   │         │
│  │  - advisor1     │  │  - locks        │  │  - project      │         │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Glossary

| Term | Definition |
|------|------------|
| **Mote** | A single claim in the proof, identified by hierarchical ID |
| **Claim** | The text assertion that a mote makes |
| **Status** | Lifecycle state: `proposed`, `rejected`, `fixed`, `verified`, `refuted`, `contested` |
| **Taint** | Work-indicator flags showing what actions are needed on a mote |
| **Proposal** | A suggested decomposition of a mote into child motes |
| **Session** | A claimed lock on a mote, identified by UUID, required for mutations |
| **Role** | An agent's capability type determining allowed actions |
| **Quorum** | Minimum number of votes/approvals needed for state transitions |
| **Propagation** | Automatic voting on parent when all children reach verified status |
| **DAG** | Directed Acyclic Graph — the proof structure where children support parents |

### 3.3 Action-Role-Status Matrix

| Action | Role | From Status | To Status | Quorum |
|--------|------|-------------|-----------|--------|
| `create` | any | — | `:fixed` | — |
| `propose` | `proposer` | `:fixed` | children `:proposed` | — |
| `approve` | `advisor` | children `:proposed` | children `:fixed` | 2 |
| `reject` | `advisor` | children `:proposed` | children `:rejected` | 2 |
| `vote --for` | `verifier` | `:fixed` | `:verified` | 2 |
| `vote --against` | `verifier` | `:fixed` | `:refuted` | 2 |

---

## 4. Workflow

### 4.1 Complete Workflow Diagram

```
                              ┌─────────────┐
                              │   af init   │
                              └──────┬──────┘
                                     │
                                     ▼
                    ┌────────────────────────────────┐
                    │  af create --root --claim "P"  │
                    │  Creates mote 1 with status    │
                    │  :fixed, taint :needs-decomp   │
                    └────────────────┬───────────────┘
                                     │
                                     ▼
         ┌───────────────────────────────────────────────────┐
         │  PROPOSER claims mote 1                           │
         │  af claim 1 --agent A --role proposer             │
         │                                                    │
         │  af propose 1 --session S                         │
         │      --claim "step 1" --claim "step 2" ...        │
         │                                                    │
         │  af done --session S                              │
         │                                                    │
         │  Result: Children 1.1, 1.2, ... created as        │
         │          :proposed with proposal pending          │
         └───────────────────────────┬───────────────────────┘
                                     │
                                     ▼
         ┌───────────────────────────────────────────────────┐
         │  ADVISORS approve proposal (need quorum: 2)       │
         │                                                    │
         │  Advisor 1:                                        │
         │    af claim 1 --agent B --role advisor            │
         │    af approve 1 --session S --reason "..."        │
         │    af done --session S                            │
         │                                                    │
         │  Advisor 2:                                        │
         │    af claim 1 --agent C --role advisor            │
         │    af approve 1 --session S --reason "..."        │
         │    af done --session S                            │
         │                                                    │
         │  Result: Children promoted to :fixed              │
         │          Parent taint cleared                     │
         └───────────────────────────┬───────────────────────┘
                                     │
                                     ▼
         ┌───────────────────────────────────────────────────┐
         │  VERIFIERS vote on each child (need quorum: 2)    │
         │                                                    │
         │  For each child mote:                             │
         │    Verifier 1:                                     │
         │      af claim 1.X --agent D --role verifier       │
         │      af vote 1.X --session S --for --reason "..." │
         │      af done --session S                          │
         │                                                    │
         │    Verifier 2:                                     │
         │      af claim 1.X --agent E --role verifier       │
         │      af vote 1.X --session S --for --propagate    │
         │      af done --session S                          │
         │                                                    │
         │  Result: Children become :verified                │
         │          --propagate auto-votes on parent         │
         └───────────────────────────┬───────────────────────┘
                                     │
                                     ▼
         ┌───────────────────────────────────────────────────┐
         │  VERIFY ROOT (if not auto-propagated)             │
         │                                                    │
         │  af claim 1 --agent F --role verifier             │
         │  af vote 1 --session S --for                      │
         │  af done --session S                              │
         │                                                    │
         │  (repeat until quorum reached)                    │
         └───────────────────────────┬───────────────────────┘
                                     │
                                     ▼
                    ┌────────────────────────────────┐
                    │  af check                      │
                    │  Validates DAG integrity       │
                    │                                │
                    │  af show 1                     │
                    │  Confirms status: :verified    │
                    └────────────────────────────────┘
```

### 4.2 Minimal Command Sequence (√2 Proof)

```bash
# Initialize
af init

# Create root claim
af create --root --claim "The square root of 2 is irrational"

# Propose decomposition (as proposer)
af claim 1 --agent prover --role proposer
af propose 1 --session $S1 \
  --claim "Assume √2 = p/q where p,q coprime, q≠0" \
  --claim "Squaring: p² = 2q²" \
  --claim "p² even ⟹ p even" \
  --claim "p=2k ⟹ q² even ⟹ q even" \
  --claim "Both even contradicts coprimality" \
  --claim "∴ √2 is irrational"
af done --session $S1

# Approve proposal (need 2 advisors)
af claim 1 --agent advisor1 --role advisor
af approve 1 --session $S2 --reason "Valid structure"
af done --session $S2

af claim 1 --agent advisor2 --role advisor
af approve 1 --session $S3 --reason "Sound approach"
af done --session $S3

# Verify each child (need 2 verifiers each, use loop)
for mote in 1.1 1.2 1.3 1.4 1.5 1.6; do
  for verifier in verifier1 verifier2; do
    S=$(af claim $mote --agent $verifier --role verifier -f json | jq -r '.["session-id"]')
    af vote $mote --session $S --for --reason "Valid" --propagate
    af done --session $S
  done
done

# Final verification of root (if needed)
S=$(af claim 1 --agent verifier1 --role verifier -f json | jq -r '.["session-id"]')
af vote 1 --session $S --for --reason "All children verified"
af done --session $S

# Validate
af check
af show 1
```

---

## 5. Common Mistakes

### 5.1 Mistakes Made During Testing

| # | Mistake | Symptom | Resolution |
|---|---------|---------|------------|
| 1 | Used invalid role names | `Failed to validate "--role X": Invalid role` | Extracted schema from JAR to find valid roles |
| 2 | Tried to approve as verifier | `Action not allowed for your role` | Changed to `advisor` role |
| 3 | Expected single vote to verify | `:quorum-status :pending` | Added second verifier vote |
| 4 | Skipped proposal approval | Children stuck in `:proposed` status | Used advisors to approve first |
| 5 | Forgot to release session | Could not claim same mote again | Added `af done` after each action |
| 6 | Expected auto-propagation | Parent not verified after children | Added explicit vote on parent |
| 7 | Used `af help <cmd>` syntax | Only showed "Show help" message | Used `af <cmd> --help` instead |

### 5.2 Anti-Patterns to Avoid

**Don't:** Try to verify before proposal is approved
```bash
af vote 1.1 --session $S --for  # Fails: mote still :proposed
```

**Don't:** Claim with wrong role for intended action
```bash
af claim 1 --agent X --role verifier
af approve 1 --session $S  # Fails: verifier can't approve
```

**Don't:** Forget session management
```bash
af claim 1 --agent X --role verifier
# ... do other things ...
af claim 1 --agent Y --role verifier  # Fails: already claimed
```

**Don't:** Assume one vote is enough
```bash
af vote 1.1 --session $S --for
# Mote still :fixed, not :verified — need second vote
```

---

## 6. Recommendations

### 6.1 Documentation Improvements

1. **List enum values in help:** All `--role`, `--status`, `--taint` options should show valid values
2. **Show quorum in output:** Display `[1/2 votes]` instead of just `:pending`
3. **Role-action matrix:** Document which roles can perform which actions
4. **Workflow tutorial:** Step-by-step guide for common proof patterns

### 6.2 UX Improvements

1. **Auto-session mode:** `af verify 1.1 --as agent1` handles claim/vote/done automatically
2. **Batch operations:** `af verify 1.1 1.2 1.3 --as agent1` for multiple motes
3. **Tree visualization:** `af tree` shows proof structure
4. **Status dashboard:** `af status` shows all motes needing attention
5. **Human-readable output:** Default to readable format, `--edn`/`--json` for scripts

### 6.3 Error Message Improvements

Current:
```
Failed to validate "--role reviewer": Invalid role
```

Proposed:
```
Invalid role: "reviewer"
Valid roles: proposer, advisor, prover, verifier, ref-checker, counterexample
```

---

## 7. Proposed CLI Redesign

Based on friction encountered, here is a redesigned command structure:

### 7.1 Command Overview

```
af init                                    # Initialize project
af create "claim" [--parent ID]            # Create claim (root if no parent)
af decompose ID "c1" "c2" ...              # Propose children
af approve ID [--reason R]                 # Approve proposal (auto-session)
af reject ID --reason R                    # Reject proposal
af verify ID [--reason R]                  # Vote for (auto-session)
af refute ID --reason R                    # Vote against
af show [ID]                               # Show mote details
af tree [ID]                               # Show proof tree
af status                                  # Show pending work
af check                                   # Validate DAG integrity
af config [key [value]]                    # Get/set configuration
af roles                                   # List valid roles
```

### 7.2 Example Session

```bash
# Initialize
$ af init
Initialized Alethfeld project
  vote-quorum: 2
  proposal-quorum: 2

# Create theorem
$ af create "√2 is irrational"
Created mote 1: "√2 is irrational"
Status: fixed | Needs: decomposition

# Decompose
$ af decompose 1 \
    "Assume √2 = p/q, p,q coprime" \
    "Then p² = 2q²" \
    "So p is even" \
    "So q is even" \
    "Contradiction" \
    "Therefore √2 irrational"
Proposed 6 children [needs approval: 0/2]

# Approve
$ af approve 1 --as alice
Approved [1/2]

$ af approve 1 --as bob
Approved [2/2] ✓ Children promoted

# Verify all children
$ af verify 1.1 1.2 1.3 1.4 1.5 1.6 --as alice
Voted for: 1.1 [1/2], 1.2 [1/2], 1.3 [1/2], 1.4 [1/2], 1.5 [1/2], 1.6 [1/2]

$ af verify 1.1 1.2 1.3 1.4 1.5 1.6 --as bob --propagate
Verified: 1.1 ✓, 1.2 ✓, 1.3 ✓, 1.4 ✓, 1.5 ✓, 1.6 ✓
Propagated to: 1 [1/2]

$ af verify 1 --as alice
Verified: 1 ✓

# Validate
$ af check
✓ DAG valid: 7 motes, 0 errors

$ af tree
1 [verified] √2 is irrational
├── 1.1 [verified] Assume √2 = p/q, p,q coprime
├── 1.2 [verified] Then p² = 2q²
├── 1.3 [verified] So p is even
├── 1.4 [verified] So q is even
├── 1.5 [verified] Contradiction
└── 1.6 [verified] Therefore √2 irrational
```

---

## 8. Conclusion

Alethfeld implements a sound conceptual model for collaborative proof verification. The DAG structure, role-based access control, and quorum voting provide a solid foundation for multi-agent theorem proving.

However, the current CLI has significant usability barriers:
- **Discovery friction:** Valid values for enums are not documented
- **Verbosity:** Session management requires 3 commands per action
- **Opacity:** Quorum requirements and progress are not visible
- **Output format:** EDN is unfamiliar to most users

With the recommended improvements—particularly auto-session management, enum documentation, and human-readable output—Alethfeld could become significantly more accessible while retaining its powerful collaborative verification model.

---

## Appendix A: Complete Command Reference

| Command | Description | Roles |
|---------|-------------|-------|
| `af init` | Initialize `.alethfeld/` directory | — |
| `af create --root --claim TEXT` | Create root mote | — |
| `af create PARENT --claim TEXT` | Create child mote | — |
| `af claim ID --agent NAME --role ROLE` | Claim mote, get session | — |
| `af done --session TOKEN` | Release session | — |
| `af propose ID --session S --claim C [--claim C ...]` | Propose decomposition | proposer |
| `af approve ID --session S [--reason R]` | Approve proposal | advisor |
| `af reject ID --session S --reason R` | Reject proposal | advisor |
| `af vote ID --session S --for [--reason R] [--propagate]` | Vote for validity | verifier |
| `af vote ID --session S --against --reason R` | Vote against validity | verifier |
| `af show [ID]` | Display mote details | — |
| `af check` | Validate DAG integrity | — |
| `af config list` | Show all configuration | — |
| `af config get KEY` | Get config value | — |
| `af config set KEY VALUE` | Set config value | — |

## Appendix B: Status Reference

| Status | Description |
|--------|-------------|
| `:proposed` | Newly proposed, awaiting approval |
| `:rejected` | Proposal rejected by advisors |
| `:fixed` | Approved and ready for verification |
| `:verified` | Verified as valid by quorum |
| `:refuted` | Refuted as invalid by quorum |
| `:contested` | Conflicting votes, needs resolution |

## Appendix C: Taint Reference

| Taint | Description |
|-------|-------------|
| `:needs-decomposition` | Claim should be broken into sub-claims |
| `:needs-proposal-review` | Has pending proposal awaiting approval |
| `:needs-verification` | Ready for verification voting |
| `:needs-votes` | Has votes but hasn't reached quorum |
| `:needs-refs` | References should be added |
| `:needs-counterexample` | Counterexample search needed |
