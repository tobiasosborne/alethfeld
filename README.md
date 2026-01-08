# Alethfeld

Collaborative proof verification with AI agent swarms.

**Version:** 0.1.0

## Overview

Alethfeld is a CLI tool (`af`) for managing DAGs of proof steps ("motes"). AI agents query for work, perform verification tasks, and commit results. Git provides persistence and ACID semantics.

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
java -jar target/alethfeld-0.1.0-SNAPSHOT.jar --help
```

## Quick Start

```bash
# Initialize a new project
cd my-proof-project
af init --name "My Proof"

# Create a root mote
af create --root --claim "The main theorem holds"

# View mote details
af show 1

# Create child motes
af create 1 --claim "Lemma 1" --difficulty 2
af create 1 --claim "Lemma 2" --difficulty 3

# Get work for an agent
af ready --agent prover-bot

# Validate the DAG
af check
```

## Commands

| Command | Description |
|---------|-------------|
| `af init` | Initialize .alethfeld/ in current directory |
| `af show <id>` | Display mote details |
| `af create` | Create a root or child mote |
| `af ready` | Get next job(s) for an agent |
| `af propose` | Propose decomposition into children |
| `af approve` | Vote to approve a proposal |
| `af reject` | Vote to reject a proposal |
| `af vote` | Cast verification vote |
| `af claim` | Claim mote for work |
| `af unclaim` | Release claim on mote |
| `af check` | Validate DAG integrity |
| `af log` | Show git history for mote |
| `af sync` | Pull, commit, push |

Run `af <command> --help` for command-specific options.

## Global Options

| Option | Description |
|--------|-------------|
| `--format edn\|json` | Output format (default: edn) |
| `--verbose` | Show detailed error messages with stack traces |
| `--help` | Show help |
| `--version` | Show version |

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

## License

MIT
