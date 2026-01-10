# Alethfeld

Collaborative proof verification with AI agent swarms.

**Version:** 0.2.1

## Overview

Alethfeld is a CLI tool (`af`) for managing DAGs of proof steps ("motes"). AI agents query for work, perform verification tasks, and commit results. Git provides persistence and ACID semantics.

**v0.2 introduces a verifier-first workflow** where verifiers act as gatekeepers, deciding whether claims can be verified directly or need decomposition into substeps. See [V02-REVISION-PLAN.md](docs/V02-REVISION-PLAN.md) for detailed changes.

## Installation

### Requirements

- Java 11 or higher
- Clojure CLI tools (for building from source)
- Git

### Quick Install

```bash
# Clone the repository
git clone https://github.com/yourusername/alethfeld.git
cd alethfeld

# Install (builds and installs to ~/.local/bin)
./install.sh
```

### Custom Install Location

```bash
# Install to /usr/local (requires sudo for write permissions)
sudo ./install.sh /usr/local

# Or any custom prefix
./install.sh /opt/alethfeld
```

### PATH Setup

After installation, ensure the bin directory is in your PATH:

```bash
# For ~/.local/bin (default install)
export PATH="$HOME/.local/bin:$PATH"

# Add to ~/.bashrc or ~/.zshrc to persist
```

### Manual Build

If you prefer to manage the jar yourself:

```bash
# Build the uberjar
clj -T:build uber

# Run directly
java -jar target/alethfeld-0.2.1-SNAPSHOT.jar --help
```

## Quick Start

The Alethfeld workflow follows a **verifier-first** approach:

1. **Initialize** - Create project and root claim
2. **Verify** - Verifiers decide if claims need decomposition
3. **Decompose** - Proposers break complex claims into substeps
4. **Review** - Advisors approve decompositions
5. **Repeat** - Children go back to verifiers

```bash
# Initialize a new project
cd my-proof-project
af init --name "My Proof"

# Create a root mote with the main claim
af create --root --claim "The main theorem holds"

# Check project status
af status

# View the proof tree
af tree 1

# See what work is available
af ready

# Claim work as a verifier (creates a session)
af ready --name alice --role verifier

# Use the session token to perform actions
af vote 1 --for --reason "Claim is self-evident" --session <token>

# End session when done
af done --session <token>

# Validate the DAG
af check
```

## Commands

### Core Commands

| Command | Description |
|---------|-------------|
| `af init` | Initialize .alethfeld/ in current directory |
| `af create` | Create a root or child mote |
| `af show <id>` | Display mote details |
| `af tree <id>` | Display proof structure as tree |
| `af status` | Display project status summary |
| `af check` | Validate DAG integrity |

### Workflow Commands

| Command | Description |
|---------|-------------|
| `af ready` | Get next job(s) for an agent |
| `af done` | End session and release mote |
| `af workflow` | Display the proof workflow steps |
| `af roles` | Show available roles and descriptions |

### Verification Commands

| Command | Description |
|---------|-------------|
| `af vote` | Cast verification vote (--for or --against) |
| `af vote-all` | Batch vote on multiple motes |
| `af taint` | Add/remove taint flags (needs-decomposition, etc.) |

### Proposal Commands

| Command | Description |
|---------|-------------|
| `af propose` | Propose decomposition into children |
| `af approve` | Vote to approve a proposal |
| `af approve-all` | Approve all pending proposals in session |
| `af reject` | Vote to reject a proposal |
| `af withdraw` | Withdraw own proposal |

### Refinement Commands

| Command | Description |
|---------|-------------|
| `af add-assumption` | Add internal assumption |
| `af add-definition` | Add definition |
| `af add-ref` | Add external reference |
| `af add-dep` | Add dependency link |
| `af update` | Update mote fields |

### Session & Admin Commands

| Command | Description |
|---------|-------------|
| `af sessions` | List all active sessions |
| `af claim` | Claim mote for work |
| `af unclaim` | Release claim on mote |
| `af config` | Manage project configuration |
| `af repair` | Detect and repair DAG inconsistencies |
| `af log` | Show git history for mote |
| `af sync` | Pull, commit, push |

### Command Aliases

| Alias | Maps To |
|-------|---------|
| `af verify` | `af vote --for` |
| `af refute` | `af vote --against` |
| `af decompose` | `af propose` |
| `af jobs` | `af ready` |
| `af list` | `af status` |

Run `af <command> --help` for command-specific options.

## Global Options

| Option | Description |
|--------|-------------|
| `--format text\|edn\|json` | Output format (default: text) |
| `--verbose` | Show detailed error messages with stack traces |
| `--help` | Show help |
| `--version` | Show version |

## Example Session Transcript

This example shows a complete mini proof workflow, proving that "1 + 1 = 2".

```bash
# 1. Initialize the project
$ af init --name "Simple Arithmetic"
Initialized Alethfeld project: Simple Arithmetic
Created: .alethfeld/

# 2. Create the root claim
$ af create --root --claim "1 + 1 = 2"
Created mote: 1
Claim: 1 + 1 = 2

# 3. Check project status
$ af status
Simple Arithmetic

Motes: 1 total
  needs-verification: 1

Next: af ready --name <you> --role verifier

# 4. View the tree
$ af tree 1
1 [needs-verification] 1 + 1 = 2

# 5. Claim work as a verifier
$ af ready --name alice --role verifier
Claimed mote 1 as verifier

Session: a1b2c3d4-e5f6-7890-abcd-ef1234567890-...
Mote: 1
Role: verifier
Claim: 1 + 1 = 2

ALLOWED:
  af vote 1 --for --reason "..." --session <token>
  af vote 1 --against --reason "..." --session <token>
  af taint 1 --add needs-decomposition --session <token>
  af done --session <token>

# 6. Vote to verify (claim is simple enough)
$ af vote 1 --for --reason "Trivial arithmetic" --session a1b2c3d4-...
Voted FOR mote 1
Reason: Trivial arithmetic
Status: verified

# 7. End the session
$ af done --session a1b2c3d4-...
Session ended.
Mote 1 released.

# 8. Check final status
$ af status
Simple Arithmetic

Motes: 1 total
  verified: 1 (100%)

Proof complete!

# 9. View the verified tree
$ af tree 1
1 [verified] 1 + 1 = 2
```

### Multi-Step Proof Example

For complex claims that need decomposition:

```bash
# Verifier demands decomposition
$ af taint 1 --add needs-decomposition --session <token>

# Proposer breaks it into substeps
$ af ready --name bob --role proposer
$ af propose 1 --claim "Step 1" --claim "Step 2" --session <token>

# Advisor approves the decomposition
$ af ready --name carol --role advisor
$ af approve 1 --reason "Valid breakdown" --session <token>

# Children now need verification
$ af tree 1
1 [fixed] Main claim
+-- 1.1 [needs-verification] Step 1
+-- 1.2 [needs-verification] Step 2
```

## Troubleshooting

### Common Issues

#### "Session not found or expired"

Sessions expire after 30 minutes by default. Get a new session:

```bash
af ready --name <your-name> --role <role>
```

To check active sessions:

```bash
af sessions
```

#### "Action not allowed for role"

Each role has specific permissions. Check what your role can do:

```bash
af roles
```

Common role-action mappings:
- **verifier**: vote, taint (add/remove)
- **proposer**: propose, add-ref, add-definition, add-assumption
- **advisor**: approve, reject

#### "Mote already claimed"

Another session has claimed this mote. Options:

1. Wait for the other session to finish or expire
2. Check active sessions: `af sessions`
3. Work on a different mote: `af ready --name <you> --role <role>`

#### "Cannot vote on own work" (Self-vote prevention)

You cannot verify work you created or proposed. This prevents conflicts of interest. Ask another agent to verify.

#### "DAG validation failed"

Run diagnostics and repair:

```bash
af check           # See what's wrong
af repair --dry-run  # Preview fixes
af repair --auto     # Apply automatic fixes
```

#### "No jobs available"

All current work may be claimed or the proof may be complete:

```bash
af status   # Check overall progress
af sessions # See who has claimed what
af tree 1   # View proof structure
```

### Environment Variables

| Variable | Description |
|----------|-------------|
| `AF_SESSION` | Default session token (avoids --session flag) |

Example:

```bash
export AF_SESSION=$(af ready --name alice --role verifier --format edn | grep :session-id | cut -d'"' -f2)
af vote 1 --for --reason "Valid"  # Uses AF_SESSION automatically
```

### Configuration

Adjust quorum and timeouts via `af config`:

```bash
# Show all config
af config list

# Single-agent mode (quorum of 1)
af config set vote-quorum 1
af config set proposal-quorum 1

# Longer session timeout (60 minutes)
af config set session-timeout 60
```

## Development

```bash
# Run CLI directly (development mode)
clj -M:run --help

# Run tests
clj -M:test

# Build uberjar
clj -T:build uber
```

## Documentation

- [PRD](docs/PRD.md) - Product Requirements Document
- [Tech Spec](docs/TECH-SPEC.md) - Technical Specification
- [Implementation Plan](docs/IMPLEMENTATION-PLAN.md) - Development roadmap
- [V0.2 Revision Plan](docs/V02-REVISION-PLAN.md) - Verifier-first workflow changes

## License

MIT
