# Alethfeld CLI Command Reference

Alethfeld (af) is a CLI tool for collaborative proof verification.

## Quick Start

```bash
af init --name "My Proof"              # Initialize project
af create --root --claim "Main theorem" # Create root claim
af ready --name alice                   # Get assigned work
af done --session TOKEN                 # Complete session
```

## Environment Variables

- `AF_NAME` - Default agent name (used when --name not provided)
- `AF_SESSION` - Default session token (used when --session not provided)
- `AF_AGENT` - Deprecated, use AF_NAME instead

---

## Project Initialization

### init

Initialize a new Alethfeld repository in the current directory.

**Synopsis:**
```
af init [--name NAME]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-n, --name NAME` | Project name (default: "Alethfeld Project") |
| `--dry-run` | Show what would be created without executing |

**Example:**
```bash
af init --name "Fermat's Last Theorem Proof"
```

Creates `.alethfeld/` directory with config, motes, sessions, and archive subdirectories.

---

## Mote Management

### create

Create a new mote (proof unit).

**Synopsis:**
```
af create <parent-id> --claim TEXT [OPTIONS]
af create --root --claim TEXT [OPTIONS]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-c, --claim TEXT` | The claim text (required) |
| `-r, --root` | Create as root mote (no parent) |
| `-d, --difficulty N` | Difficulty 1-5 (default: 3 or inherited from parent) |
| `-p, --priority P` | Priority p0-p4 (default: p2 or inherited from parent) |
| `-n, --name NAME` | Agent name for created-by field |
| `--dry-run` | Preview without creating |

**Examples:**
```bash
# Create root mote
af create --root --claim "For all n>2, x^n + y^n != z^n" --priority p0

# Create child mote
af create 1 --claim "Case n=3 by Euler's proof" --difficulty 2
```

### show

Display details of a mote.

**Synopsis:**
```
af show <id> [--verbose]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--verbose` | Show detailed output including votes, assumptions, definitions |

**Example:**
```bash
af show 1.1 --verbose
```

### update

Update mote fields (claim, priority, difficulty).

**Synopsis:**
```
af update <id> [OPTIONS]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-c, --claim TEXT` | New claim text |
| `-p, --priority P` | New priority (p0-p4) |
| `-d, --difficulty N` | New difficulty (1-5) |
| `-S, --session TOKEN` | Session token (required for mutations) |

**Example:**
```bash
af update 1.1 --claim "Refined claim statement" --session $AF_SESSION
```

### tree

Display a mote and its descendants as a tree structure.

**Synopsis:**
```
af tree <id> [--depth N] [--verbose]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-d, --depth N` | Maximum depth to display (default: unlimited) |
| `--verbose` | Show priority, difficulty, votes |

**Example:**
```bash
af tree 1 --depth 3 --verbose
```

---

## Job Assignment and Sessions

### ready

Get next job(s) for an agent. This is the primary entry point for agents.

**Synopsis:**
```
af ready [OPTIONS]
```

**Modes:**
1. **List mode** (no --name): Shows available jobs without claiming
2. **Claim mode** (with --name): Claims highest priority job
3. **Preview mode** (--name + --no-claim): Shows job without claiming

**Options:**
| Option | Description |
|--------|-------------|
| `-n, --name NAME` | Agent name (auto-claims job unless --no-claim) |
| `-r, --role ROLE` | Filter by role (proposer, advisor, prover, verifier, ref-checker, counterexample) |
| `-d, --difficulty SPEC` | Difficulty filter: "N" for exact, "N-M" for range |
| `-p, --priority SPEC` | Priority filter: "pN" for exact, "pN-pM" for range |
| `-m, --max N` | Max jobs to return (default: 10 for list, 1 for claim) |
| `--no-claim` | Don't auto-claim jobs |
| `--reserve` | Reserve job without claiming (for orchestrators) |
| `--claim-reservation TOKEN` | Claim a previously reserved job |

**Examples:**
```bash
# List available work
af ready

# Claim highest priority job as verifier
af ready --name alice --role verifier

# Claim specific job from list
af ready --name alice --job 1

# Filter by difficulty and priority
af ready --name bob --difficulty 1-3 --priority p0-p1
```

### claim

Manually claim a specific mote for work (lower-level than ready).

**Synopsis:**
```
af claim <id> --name NAME --role ROLE
```

**Options:**
| Option | Description |
|--------|-------------|
| `-n, --name NAME` | Agent name (required) |
| `-r, --role ROLE` | Role for this session (required) |
| `--dry-run` | Preview without claiming |

**Example:**
```bash
af claim 1.1 --name alice --role verifier
```

### unclaim

Release a claim on a mote (prefer using `done` instead).

**Synopsis:**
```
af unclaim <id> --session TOKEN
```

### done

End a session and release the claimed mote.

**Synopsis:**
```
af done --session TOKEN
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `--dry-run` | Preview without ending session |

**Example:**
```bash
af done --session abc123
# Or with environment variable:
AF_SESSION=abc123 af done
```

**Important:** After `af done`, the agent should terminate. New work requires a new agent.

### sessions

List all active sessions.

**Synopsis:**
```
af sessions [--verbose]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-v, --verbose` | Show additional session details |

Shows active sessions and stale sessions (expired or crashed). Stale sessions are automatically cleaned up when `af ready` is run.

---

## Verification Workflow

### vote

Cast a verification vote on a mote.

**Synopsis:**
```
af vote <id> --session TOKEN --for|--against [--reason TEXT] [--propagate]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `--for` | Vote that claim is valid |
| `--against` | Vote that claim is invalid |
| `-R, --reason TEXT` | Reason for vote |
| `--propagate` | Auto-vote on parents when all siblings verified |
| `-n, --name NAME` | Agent name (defaults to session agent) |

**Quorum Results:**
- All votes `--for`: mote becomes `:verified`
- All votes `--against`: mote becomes `:refuted`
- Mixed votes: mote becomes `:contested`

**Examples:**
```bash
af vote 1.1 --session $AF_SESSION --for --reason "Proof is sound"
af vote 1.2 --session $AF_SESSION --against --reason "Counterexample: n=4, x=2"
```

### vote-all

Batch vote on multiple motes.

**Synopsis:**
```
af vote-all --session TOKEN --for|--against [--reason TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `--for` | Vote for (valid) |
| `--against` | Vote against (invalid) |
| `-R, --reason TEXT` | Reason for all votes |
| `--pending` | Only vote on motes needing verification (default) |
| `--dry-run` | Preview without voting |

### taint

Add or remove taint flags from a mote.

**Synopsis:**
```
af taint <id> --session TOKEN --add TAINT | --remove TAINT
```

**Valid Taints:**
- `needs-decomposition` - Claim too complex, needs substeps
- `needs-proposal-review` - Proposal pending advisor review
- `needs-refinement` - Missing definitions/assumptions
- `needs-verification` - Ready for verifier review
- `needs-refs` - External references need checking
- `needs-votes` - Awaiting more votes
- `needs-counterexample` - Adversarial review needed

**Examples:**
```bash
af taint 1.1 --session $AF_SESSION --add needs-decomposition
af taint 1.1 --session $AF_SESSION --remove needs-refinement
```

---

## Proposal Workflow

### propose

Propose decomposition of a mote into children.

**Synopsis:**
```
af propose <parent-id> --session TOKEN --claim TEXT [--difficulty N] [--claim TEXT ...]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-c, --claim TEXT` | Claim text (repeatable for multiple children) |
| `-d, --difficulty N` | Difficulty for claims (repeatable, positional) |
| `-n, --name NAME` | Agent name (defaults to session agent) |
| `--dry-run` | Preview without creating |

**Example:**
```bash
af propose 1 --session $AF_SESSION \
  --claim "Step 1: Prove base case" --difficulty 1 \
  --claim "Step 2: Prove induction" --difficulty 3
```

Alternative syntax with difficulty in claim:
```bash
af propose 1 --session $AF_SESSION "Base case @1" "Induction step @3"
```

### approve

Vote to approve a proposal.

**Synopsis:**
```
af approve <parent-id> --session TOKEN [--reason TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-R, --reason TEXT` | Reason for approval |
| `-n, --name NAME` | Agent name (defaults to session agent) |

When quorum is reached, proposed children become `:fixed` status.

### approve-all

Approve all pending proposals in scope.

**Synopsis:**
```
af approve-all --session TOKEN [--reason TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-R, --reason TEXT` | Reason for all approvals |
| `--dry-run` | Preview without approving |

### reject

Vote to reject a proposal.

**Synopsis:**
```
af reject <parent-id> --session TOKEN [--reason TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-R, --reason TEXT` | Reason for rejection |

When quorum is reached, proposed children are archived and parent gets `needs-decomposition` taint.

### withdraw

Withdraw your own pending proposal.

**Synopsis:**
```
af withdraw <parent-id> --session TOKEN
```

Only the original proposer can withdraw their proposal.

---

## Reference Management

### add-ref

Add an external reference (citation) to a mote.

**Synopsis:**
```
af add-ref <id> --session TOKEN --ref CITATION [--note TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-r, --ref REF` | Citation/reference text (required) |
| `-n, --note TEXT` | Note explaining what the reference provides |

**Example:**
```bash
af add-ref 1.1 --session $AF_SESSION \
  --ref "Wiles, A. (1995). Modular elliptic curves and Fermat's Last Theorem" \
  --note "Provides main result"
```

### add-assumption

Add an internal assumption (reference to another mote).

**Synopsis:**
```
af add-assumption <id> --session TOKEN --ref MOTE-ID [--note TEXT]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-r, --ref ID` | Referenced mote ID (required) |
| `-n, --note TEXT` | Note explaining why this assumption is needed |

**Example:**
```bash
af add-assumption 1.2 --session $AF_SESSION --ref 1.1 --note "Depends on base case"
```

### add-definition

Add a symbol definition to a mote.

**Synopsis:**
```
af add-definition <id> --session TOKEN --symbol SYM --meaning TEXT
```

**Options:**
| Option | Description |
|--------|-------------|
| `-S, --session TOKEN` | Session token (required) |
| `-s, --symbol SYM` | Symbol to define (required) |
| `-m, --meaning TEXT` | Meaning of symbol (required) |

**Example:**
```bash
af add-definition 1.1 --session $AF_SESSION \
  --symbol "n" --meaning "A positive integer greater than 2"
```

### add-dep

Add a dependency link between motes.

**Synopsis:**
```
af add-dep <id> --depends-on MOTE-ID [--reason TEXT] --session TOKEN
```

**Options:**
| Option | Description |
|--------|-------------|
| `-s, --session TOKEN` | Session token (required) |
| `-d, --depends-on ID` | Mote ID that this mote depends on (required) |
| `-r, --reason TEXT` | Reason for dependency |

---

## Project Status and Utilities

### status

Display project status summary.

**Synopsis:**
```
af status [--verbose]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--verbose` | Show detailed breakdown by status, taints, and roles |

**Example Output:**
```
My Proof - 42% verified (5/12)
Ready work: 3 motes (2 verifier, 1 proposer)
```

### check

Validate DAG integrity.

**Synopsis:**
```
af check [--verbose]
```

Validates:
- All parent refs exist
- All children refs exist and point back
- No cycles in assumption graph
- All internal assumption refs exist
- Schema validation on all motes

### repair

Detect and repair DAG inconsistencies.

**Synopsis:**
```
af repair [--dry-run | --auto]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--dry-run` | Show what would be fixed without fixing |
| `--auto` | Automatically fix all repairable issues |

### log

Show git history for a mote.

**Synopsis:**
```
af log <id> [--limit N] [--verbose]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-l, --limit N` | Max entries to show (default: 10) |
| `--verbose` | Show author and date |

### sync

Synchronize local changes with remote git repository.

**Synopsis:**
```
af sync [--no-push]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--no-push` | Skip the push step (for offline work) |
| `--dry-run` | Preview without executing |

Equivalent to: `git pull --rebase && git add .alethfeld/ && git commit && git push`

---

## Configuration

### config

Manage project configuration.

**Synopsis:**
```
af config list                    # Show all config
af config get <key>               # Get a value
af config set <key> <value>       # Set a value
```

**Valid Keys:**
| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `project-name` | string | "Unnamed Proof" | Project name |
| `version` | string | "0.1" | Version string |
| `default-difficulty` | int (1-5) | 3 | Default difficulty for new motes |
| `proposal-quorum` | int (>=1) | 1 | Votes needed to approve/reject proposal |
| `vote-quorum` | int (>=1) | 1 | Votes needed for verification quorum |
| `claim-timeout-minutes` | int (>=1) | 30 | How long before claims expire |

**Example:**
```bash
af config set vote-quorum 3
af config get proposal-quorum
```

---

## Information Commands

### workflow

Display the proof workflow steps.

**Synopsis:**
```
af workflow
```

Shows the step-by-step process for using Alethfeld.

### roles

Show available agent roles and their descriptions.

**Synopsis:**
```
af roles
```

### help

Show help information.

**Synopsis:**
```
af help [command]
```

**Examples:**
```bash
af help           # Global help
af help vote      # Help for vote command
af vote --help    # Same as above
```

---

## Command Aliases

| Alias | Target | Description |
|-------|--------|-------------|
| `list` | `status` | Show project status |
| `verify` | `vote --for` | Shortcut for voting in favor |
| `refute` | `vote --against` | Shortcut for voting against |
| `decompose` | `propose` | Alternative name for propose |
| `jobs` | `ready --no-claim` | List available work without claiming |

---

## Global Options

These options work with all commands:

| Option | Description |
|--------|-------------|
| `-f, --format FORMAT` | Output format: text (default), edn, or json |
| `--verbose` | Show detailed error messages with stack traces |
| `--dry-run` | Preview changes without executing (where supported) |
| `-h, --help` | Show help |
| `-v, --version` | Show version |

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | General error |
| 2 | Invalid arguments |
| 3 | Not found |
| 4 | Validation error |
| 5 | Conflict |
