# CLAUDE.md - AI Assistant Guide for Alethfeld

## Critical Rules

1. **NEVER reference `./archive/` directory** — Contains deprecated v1 code with incompatible schemas
2. **Always read `handoff.md` at session start** — Contains current state, blockers, next steps
3. **Update `handoff.md` before ending session** — Record what you did and what's next
4. **Follow `docs/TECH-SPEC.md`** — The authoritative specification
5. **Follow `docs/IMPLEMENTATION-PLAN.md`** — The development roadmap

## Project Overview

**Alethfeld** is a Clojure-based CLI tool (`af`) for collaborative proof verification with AI agent swarms. It manages a DAG of proof steps ("motes") where agents query for work, perform verification tasks, and commit results using Git for ACID transactions.

**Current Version:** 0.2 (Phase C in progress — 40% complete)

**Architecture:**
- **Language:** Clojure 1.12.0
- **Persistence:** Git-backed EDN files (one mote per file)
- **Validation:** Malli schemas (23 types)
- **Concurrency:** Repository-level locking with rollback

## Quick Reference

### Build & Test
```bash
clj -M:run <command>              # Run CLI (development)
clj -M:test                       # Run all tests (957 tests)
clj -M:test --namespace alethfeld.foo-test  # Single namespace
clj -T:build uber                 # Build uberjar
./install.sh                      # Install to ~/.local/bin/af
```

### Issue Tracking (Beads)
```bash
bd ready                          # Find unblocked work
bd show <id>                      # View issue details
bd create "Title" --type task     # Create issue
bd close <id>                     # Complete work
bd sync                           # Sync with git (run at session end)
```

### Common af Commands
```bash
af init --name "Project"          # Initialize repository
af create --root --claim "..."    # Create root mote
af ready --agent alice --role verifier  # Get work
af vote 1.2 --for --session TOKEN # Cast vote
af done --session TOKEN           # End session
af status                         # Project summary
af tree 1 --depth 3               # View proof tree
af check                          # Validate DAG integrity
```

## Repository Structure

```
alethfeld/
├── src/alethfeld/           # Source code (17 modules, ~7000 LOC)
│   ├── cli.clj              # Entry point, argument parsing
│   ├── cmd.clj              # 20+ command implementations
│   ├── schema.clj           # Malli schemas (23 types)
│   ├── session.clj          # Role-based sessions, self-vote prevention
│   ├── verify.clj           # Voting, quorum, auto-propagation
│   ├── proposal.clj         # Proposal workflow
│   ├── tx.clj               # Transactions, locking, rollback
│   ├── store.clj            # Mote CRUD
│   ├── git.clj              # Git operations
│   ├── dag.clj              # DAG validation
│   ├── job.clj              # Job selection, role derivation
│   ├── mote.clj             # Mote constructors
│   ├── path.clj             # File path derivation
│   ├── io.clj               # EDN file I/O
│   ├── id.clj               # MoteId parsing
│   ├── prompt.clj           # Agent prompt templates
│   └── errors.clj           # Human-readable error formatting
├── test/alethfeld/          # Test suite (35 files, ~14500 LOC)
├── docs/                    # Documentation
│   ├── TECH-SPEC.md         # Authoritative technical spec
│   ├── IMPLEMENTATION-PLAN.md  # v0.2 roadmap
│   └── PRD.md               # Product requirements
├── .claude/commands/        # Claude Code slash commands
├── .beads/                  # Issue tracking metadata
├── archive/v1/              # DEPRECATED - never reference
├── handoff.md               # Session handoff document
└── deps.edn                 # Dependencies
```

## Core Concepts

### Motes
A **mote** is a proof step with:
- **id** — Hierarchical dot-separated ID (e.g., "1.2.3")
- **claim** — The mathematical statement
- **status** — `:proposed | :fixed | :verified | :rejected | :refuted | :contested`
- **taint** — Work flags: `:needs-decomposition`, `:needs-verification`, etc.
- **votes** — Verification votes from agents
- **contributors** — Tracks who created/proposed/refined (for self-vote prevention)

### Sessions
Role-based work sessions with:
- **Role-action matrix** — Verifiers can vote, proposers can propose, etc.
- **Self-vote prevention** — Agents cannot vote on their own work
- **30-minute expiration** — Auto-cleanup of stale sessions
- **Session token** — Dual-UUID (256 bits entropy)

### Workflow
1. Agent calls `af ready --agent NAME --role ROLE` to get work
2. System creates session and assigns motes
3. Agent performs actions (vote, propose, etc.) with session token
4. Agent calls `af done --session TOKEN` to end session
5. Git commits ensure ACID semantics

## Implementation Status

### v0.1 Core: 100% Complete
All 28 steps done — schema, persistence, transactions, commands, tests

### v0.2 Phase A (Session Enforcement): 100% Complete
8/8 steps — sessions, roles, self-vote prevention, contributor tracking

### v0.2 Phase B (UX Improvements): 100% Complete
4/4 steps — configurable quorum, tree view, status summary, error messages

### v0.2 Phase C (Quality/Safety): 40% Complete
- C.1 Batch Voting (`af vote-all`) — DONE
- C.2 Auto-Propagation (`--propagate`) — DONE
- C.3 Proposal Withdrawal — pending
- C.4 Cross-References — pending
- C.5 Atomic Markers — pending

## Module Guide

| Module | Lines | Purpose |
|--------|-------|---------|
| `cmd.clj` | 1845 | All command implementations |
| `session.clj` | 623 | Session lifecycle, role enforcement |
| `cli.clj` | 596 | Entry point, argument parsing |
| `prompt.clj` | 473 | Agent prompt templates |
| `tx.clj` | 339 | Transactions with rollback |
| `git.clj` | 340 | Git command wrappers |
| `proposal.clj` | 344 | Proposal workflow |
| `mote.clj` | 331 | Mote constructors |
| `verify.clj` | 279 | Voting, quorum logic |
| `errors.clj` | 260 | Error formatting (18 types) |
| `job.clj` | 246 | Job selection |
| `schema.clj` | 238 | Malli schemas |
| `store.clj` | 230 | Persistence CRUD |
| `dag.clj` | 227 | DAG validation |
| `path.clj` | 206 | Path derivation |
| `io.clj` | 183 | EDN file I/O |
| `id.clj` | 178 | ID parsing |

## Command Reference

### Sessionless (Read-Only)
| Command | Purpose |
|---------|---------|
| `init --name NAME` | Initialize repository |
| `show <id>` | Display mote details |
| `ready --agent --role --max N` | Get available jobs |
| `tree <id> --depth N` | View proof tree |
| `status` | Project summary |
| `check` | Validate DAG integrity |
| `log <id> --limit N` | Git history for mote |
| `config list\|get\|set` | Manage configuration |

### Session Required (Mutations)
| Command | Purpose |
|---------|---------|
| `create --claim TEXT` | Create new mote |
| `propose <id> --claim TEXT` | Propose child decomposition |
| `approve/reject <id>` | Vote on proposal |
| `vote <id> --for/--against` | Cast verification vote |
| `vote-all --for/--against` | Batch voting |
| `update <id> --status/--claim` | Edit mote fields |
| `taint <id> --add/--remove` | Modify taint flags |
| `claim/unclaim <id>` | Manage work claims |
| `done` | End session |

## Role-Action Matrix

| Role | Allowed Actions |
|------|-----------------|
| `:proposer` | propose, add-definition, add-assumption, add-ref, done |
| `:advisor` | approve, reject, done |
| `:prover` | propose, add-definition, add-assumption, add-ref, taint-remove, done |
| `:verifier` | vote, taint-add, done |
| `:ref-checker` | add-ref, taint-remove, done |
| `:counterexample` | vote, update-status, done |

## Testing

### Test Metrics
- **Total:** 957 tests, 2567 assertions
- **Coverage:** >90% on core modules
- **Known flaky:** 3-4 concurrency tests (pre-existing)

### Test Organization
```
test/alethfeld/
├── cli_test.clj           # CLI infrastructure (35 tests)
├── integration_test.clj   # End-to-end workflows
├── propagation_test.clj   # Auto-propagation (14 tests)
├── errors_test.clj        # Error formatting (26 tests)
├── cmd/                   # Command tests (16 files)
└── [module]_test.clj      # Unit tests per module
```

### Running Tests
```bash
clj -M:test                                    # All tests
clj -M:test --namespace alethfeld.verify-test  # Single module
```

## Key Patterns

### Pure Functions + Transaction Wrapper
```clojure
;; Pure function (testable)
(defn check-verification-quorum [mote quorum] ...)

;; Transaction wrapper (handles I/O)
(defn cast-vote! [repo-path mote-id agent vote ...]
  (tx/transact! repo-path
    (fn [...] (verify/cast-vote! ...))))
```

### Error Handling
All errors include type + actionable hints:
```clojure
{:type :self-vote
 :message "Agent 'alice' cannot vote on their own work."
 :hint "A different agent must verify this work."}
```

### File Path Rules
```
Root mote (1):
  :fixed    → .alethfeld/motes/1.edn
  :proposed → .alethfeld/proposed/1.edn

Child mote (1.2.3):
  :fixed    → .alethfeld/motes/1/1.2/1.2.3.edn
  :rejected → .alethfeld/archive/1.2/prop-UUID/1.2.3.edn
```

## Configuration

```clojure
;; .alethfeld/config.edn
{:project-name "My Proof"
 :version "0.1"
 :proposal-quorum 2        ; Votes to approve proposal
 :vote-quorum 2            ; Votes to verify mote
 :claim-timeout-minutes 30}
```

For solo work:
```bash
af config set proposal-quorum 1
af config set vote-quorum 1
```

## Dependencies

| Library | Version | Purpose |
|---------|---------|---------|
| `clojure` | 1.12.0 | Core language |
| `malli` | 0.16.4 | Schema validation |
| `tools.cli` | 1.1.230 | Argument parsing |
| `data.json` | 2.5.0 | JSON output |
| `babashka/process` | 0.5.22 | Git subprocess |
| `babashka/fs` | 0.5.22 | Filesystem ops |

## Common Tasks

### Start New Work
```bash
bd ready                    # Check for issues
cat handoff.md              # Read current state
clj -M:test                 # Verify tests pass
```

### End Session
```bash
clj -M:test                 # Run tests
# Update handoff.md with your work
bd sync                     # Sync issues
git add -A && git commit -m "description"
git push
```

### Add New Command
1. Add spec to `cli.clj` (options, summary)
2. Add handler to `cmd.clj` (cmd-NAME!)
3. Add tests to `test/alethfeld/cmd/name_test.clj`
4. Update `handoff.md`

### Fix Failing Test
1. Read the test assertion carefully
2. Check the module being tested
3. Use `clj -M:test --namespace alethfeld.X-test` to isolate
4. Fix and verify full suite passes

## Important Files

| File | Purpose |
|------|---------|
| `handoff.md` | Session context (READ FIRST!) |
| `docs/TECH-SPEC.md` | Authoritative specification |
| `docs/IMPLEMENTATION-PLAN.md` | Development roadmap |
| `src/alethfeld/schema.clj` | All type definitions |
| `src/alethfeld/cmd.clj` | Command implementations |
| `src/alethfeld/errors.clj` | Error types and hints |

## Git Workflow

- **Branch:** `main` (v2 development, private)
- **Default on GitHub:** `legacy` (v1, public)
- **Commits:** One per logical change, descriptive messages
- **ACID:** Every mutation = git commit with rollback on failure

---

*Last updated: January 2026*
*Version: 0.2 Phase C (40% complete)*
