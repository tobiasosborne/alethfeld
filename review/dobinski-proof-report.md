# Alethfeld Experience Report: Proving Dobinski's Formula

**Date:** 2026-01-10
**Tool:** Alethfeld v0.2.0
**Task:** Prove Dobinski's Formula using collaborative proof verification
**Agent:** Claude Opus 4.5

---

## Executive Summary

I successfully proved Dobinski's formula using the Alethfeld CLI tool, achieving 100% verification across 6 motes. The experience revealed a well-designed collaborative proof system with some notable friction points that could be addressed to improve the agent workflow.

---

## 1. Tool Overview

Alethfeld is a DAG-based collaborative proof verification system with a role-based workflow:

- **Proposers** decompose claims into sub-claims
- **Advisors** review and approve/reject decompositions
- **Verifiers** vote on whether claims are valid
- **Provers** add references and justifications
- **Ref-checkers** validate external citations
- **Counterexample agents** find flaws and edge cases

The system uses "motes" (proof nodes) organized in a tree structure, with each mote having a lifecycle: `proposed → fixed → verified`.

---

## 2. Workflow Executed

### Phase 1: Initialization
```bash
af init
af create --root --claim "Dobinski's Formula: ..."
```

### Phase 2: Decomposition (Proposer Role)
```bash
af ready --name claude --role proposer
af propose 1 --session TOKEN --claim "..." --claim "..." ...
af done --session TOKEN
```

### Phase 3: Review (Advisor Role)
Spawned subagent to approve the decomposition.

### Phase 4: Verification (Verifier Role)
Spawned 5 parallel subagents to verify each lemma.

### Phase 5: Validation
```bash
af check  # DAG integrity validation
```

---

## 3. Friction Points

### 3.1 Session Token Management (High Friction)

**Problem:** The session token is a 73-character UUID that must be passed to every mutation command.

```bash
af propose 1 --session "4329b7a5-01eb-4819-874c-0bce5cef6718-c9a319eb-bb2e-4f58-8e42-b6d8ce5086ea" --claim "..."
```

**Impact:**
- Error-prone for agents and humans alike
- Requires reading session files from `.alethfeld/sessions/active/` to retrieve tokens
- Easy to use expired or wrong session tokens

**Suggested Improvement:**
- Auto-detect session when only one is active (partially implemented but inconsistent)
- Support short session aliases (e.g., `--session @latest` or `--session @mine`)
- Environment variable support: `AF_SESSION=...`

---

### 3.2 Claim Command Bug (Critical)

**Problem:** The `af claim` command throws a ClassCastException:

```
java.lang.ClassCastException: class java.lang.String cannot be cast to class clojure.lang.IFn
```

**Impact:** Cannot directly claim specific motes; must use `af ready` which auto-assigns work.

**Workaround:** Used `af ready --name X --role Y` instead, but this doesn't allow claiming a specific mote.

---

### 3.3 No Control Over Work Assignment (Medium Friction)

**Problem:** `af ready` auto-assigns the next available job based on internal queue logic. Agents cannot request a specific mote.

**Impact:** When I spawned 5 verifier subagents targeting motes 1.1-1.5, some were assigned different motes than intended. The system worked because all motes needed verification, but this would be problematic for targeted work.

**Suggested Improvement:**
- Add `af ready --mote 1.4` to request specific work
- Or fix `af claim` to allow direct mote claiming

---

### 3.4 Role Restrictions on References (Low Friction)

**Problem:** Verifiers cannot add references using `af add-ref`; this is restricted to prover/proposer/ref-checker roles.

**Impact:** Verification votes couldn't include formal citations. Verifiers had to include reference information in their vote reasoning instead.

**Suggested Improvement:**
- Allow verifiers to add references (read-only enrichment shouldn't require special roles)
- Or provide clear documentation about which roles can perform which actions

---

### 3.5 Sessions Command Crash

**Problem:** `af sessions` throws an assertion error:

```
java.lang.AssertionError: Assert failed: (distinct?* (remove nil? (map :short-opt %)))
```

**Impact:** Cannot list active sessions programmatically; must read `.alethfeld/sessions/active/` directory directly.

---

### 3.6 Workflow Command Missing Prompts

**Problem:** `af workflow` fails with FileNotFoundException for `prompts/workflow.md`.

**Impact:** No access to built-in workflow documentation/prompts that might help agents understand the process.

---

### 3.7 Verbose Output Formatting

**Problem:** Every command outputs "Next steps" suggestions, even when chaining commands programmatically.

**Example:**
```
Next steps:
  → af show 1    View mote details
  → af ready --agent <name>    Get assigned a task
  → af status    View project overview
```

**Impact:** Adds noise to programmatic output parsing.

**Suggested Improvement:**
- Add `--quiet` flag to suppress suggestions
- Or only show suggestions in interactive mode

---

## 4. Positive Experiences

### 4.1 Clean Conceptual Model

The mote/tree/DAG model is intuitive. Breaking proofs into claims, decomposing them, and verifying leaves is a natural way to structure mathematical arguments.

### 4.2 Role-Based Workflow

Separating proposer/advisor/verifier roles creates healthy checks and balances. The quorum system (configurable in `config.edn`) allows tuning rigor vs. speed.

### 4.3 Good CLI Help

`af <command> --help` provides clear, well-formatted help for each command. The `af roles` command explains the role system effectively.

### 4.4 EDN/JSON Output Formats

The `--format edn` and `--format json` options enable programmatic integration:

```bash
af show 1 --format json | jq '.claim'
```

### 4.5 Tree Visualization

`af tree <id>` provides a clean ASCII tree view of the proof structure:

```
1 [verified] Dobinski's Formula: ...
+-- 1.1 [verified] Definition: ...
+-- 1.2 [verified] Lemma (Bell Recurrence): ...
...
```

### 4.6 DAG Integrity Checking

`af check` validates the entire proof structure, catching orphaned motes or inconsistent states.

---

## 5. Agent-Specific Observations

### 5.1 Parallel Subagent Spawning Works Well

Spawning 5 verifier subagents in parallel was effective. The Alethfeld system handled concurrent sessions without conflicts.

### 5.2 Session Isolation

Each agent gets its own session, preventing interference. The 30-minute timeout (configurable) provides reasonable protection against abandoned sessions.

### 5.3 Discoverability

An agent can understand the system through:
- `af --help` (command list)
- `af <cmd> --help` (command details)
- `af roles` (role explanations)
- `af status` (current state)

This self-documenting design is agent-friendly.

---

## 6. Suggested Improvements Summary

| Priority | Issue | Suggestion |
|----------|-------|------------|
| Critical | `af claim` crashes | Fix ClassCastException |
| Critical | `af sessions` crashes | Fix assertion error |
| High | Session token UX | Short aliases, env vars, auto-detection |
| High | No targeted work assignment | Add `--mote` flag to `af ready` |
| Medium | Workflow prompts missing | Bundle prompts with distribution |
| Medium | Verifiers can't add refs | Allow reference addition by verifiers |
| Low | Verbose output | Add `--quiet` flag |

---

## 7. Overall Assessment

**Ease of Use: 7/10**

The tool has a solid foundation and clear conceptual model. The main barriers are:
- Bugs in `claim` and `sessions` commands
- Session token management friction
- Lack of targeted work assignment

**Agent Suitability: 8/10**

Alethfeld is well-suited for agent workflows:
- Clear command structure
- JSON/EDN output for parsing
- Role separation enables multi-agent collaboration
- Stateless commands (just need session token)

**Recommendation:**

With bug fixes and session UX improvements, Alethfeld would be an excellent tool for collaborative proof verification by AI agents. The current version is usable but requires workarounds.

---

## Appendix: Commands Used

```bash
# Initialization
af init
af create --root --claim "..."

# Proposer workflow
af ready --name claude --role proposer
af propose 1 --session TOKEN --claim "..." [--claim "..."]
af done --session TOKEN

# Advisor workflow
af ready --name advisor1 --role advisor
af approve --session TOKEN
af done --session TOKEN

# Verifier workflow
af ready --name verifier1 --role verifier
af vote --for --session TOKEN
af done --session TOKEN

# Inspection
af status
af tree 1
af show 1.1
af check
```

---

*Report generated by Claude Opus 4.5 after completing Dobinski's formula proof using Alethfeld v0.2.0*
