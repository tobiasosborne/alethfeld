# Alethfeld Architecture

Alethfeld is a CLI tool for collaborative proof verification using AI agent swarms. It manages a directed acyclic graph (DAG) of proof steps called *motes*, where agents query for work, perform verification tasks, and commit results atomically to git.

## Design Principles

1. **Functional core, imperative shell.** Pure transformations in data modules; I/O isolated to dedicated layers.
2. **Git as database.** Every mutation is an atomic commit. History is auditability.
3. **Schema-first.** Malli validation gates all persistence. Invalid data never reaches disk.
4. **Role-based dispatch.** Taint flags on motes map to agent roles. Work finds the right specialist.
5. **Session enforcement.** Agents bind to motes via sessions; role dictates allowed actions.

## System Layers

```
┌─────────────────────────────────────────────────────────────┐
│                         CLI (cli.clj)                       │
│              Argument parsing, output formatting            │
└──────────────────────────┬──────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                     Commands (cmd.clj)                      │
│              Business logic orchestration                   │
└──────────────────────────┬──────────────────────────────────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
┌───────▼───────┐  ┌───────▼───────┐  ┌───────▼───────┐
│   Sessions    │  │    Jobs       │  │   Proposals   │
│ (session.clj) │  │  (job.clj)    │  │(proposal.clj) │
│               │  │               │  │               │
│ Role binding  │  │ Work dispatch │  │ Decomposition │
│ Action matrix │  │ Taint→Role    │  │ Voting        │
└───────┬───────┘  └───────┬───────┘  └───────┬───────┘
        │                  │                  │
        └──────────────────┼──────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                   Verification (verify.clj)                 │
│                    Quorum logic, voting                     │
└──────────────────────────┬──────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                  Transaction (tx.clj)                       │
│           ACID operations, per-repo locking                 │
└──────────────────────────┬──────────────────────────────────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
┌───────▼───────┐  ┌───────▼───────┐  ┌───────▼───────┐
│   DAG         │  │   Store       │  │   Git         │
│  (dag.clj)    │  │ (store.clj)   │  │  (git.clj)    │
│               │  │               │  │               │
│ Validation    │  │ CRUD          │  │ Commit        │
│ Cycle detect  │  │ Load/Save     │  │ Push/Pull     │
└───────┬───────┘  └───────┬───────┘  └───────┬───────┘
        │                  │                  │
        └──────────────────┼──────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                     I/O (io.clj)                            │
│                 EDN file operations                         │
└──────────────────────────┬──────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                    Filesystem + Git                         │
└─────────────────────────────────────────────────────────────┘
```

## Data Flow: Read Path

When an agent requests work:

```
af ready --agent verifier-1 --role verifier
           │
           ▼
    cmd/cmd-ready
           │
           ├─→ store/load-all-motes     Load mote graph
           │
           ├─→ job/select-jobs          Filter by status, taint, role
           │         │
           │         └─→ mote->roles    Derive eligible roles from taints
           │
           ├─→ prompt/render-job        Assemble role-specific prompt
           │
           └─→ session/create-session!  Bind agent to mote+role
                      │
                      ▼
               JSON output with job object
```

## Data Flow: Write Path

When an agent casts a vote:

```
af vote 1.2 --for --agent verifier-1
           │
           ▼
    cmd/cmd-vote
           │
           ├─→ session/validate-action   Check role permits :vote
           │
           ▼
    tx/with-validation
           │
           ├─→ Acquire repo lock         ReentrantLock per repository
           │
           ├─→ store/load-mote           Read current state
           │
           ├─→ mote/add-vote             Pure transformation
           │
           ├─→ dag/validate-dag          Ensure graph integrity
           │
           ├─→ store/save-mote!          Write to disk
           │
           ├─→ git/git-add! + commit!    Atomic persistence
           │
           ├─→ verify/check-quorum       Update status if threshold met
           │
           └─→ Release lock
                      │
                      ▼
               Success output
```

## Concurrency Model

Alethfeld uses per-repository locking to serialize mutations:

- **Lock scope.** One `ReentrantLock` per repository path, stored in a `ConcurrentHashMap`.
- **Path normalization.** Canonical paths handle symlinks and relative paths.
- **Transaction boundary.** `with-validation` macro acquires lock, validates, writes, commits.
- **Race window.** ~100ms between validation and commit completion. Process crash during this window leaves validated but uncommitted changes on disk. Recovery: `git add . && git commit -m 'recovery'`.

Multiple agents can safely work concurrently—lock contention is brief since all operations are local filesystem + git.

## Repository Layout

```
.alethfeld/
├── config.edn              Project configuration
├── motes/                  Approved motes (hierarchical)
│   ├── 1.edn
│   └── 1/
│       ├── 1.1.edn
│       └── 1.2/
│           └── 1.2.1.edn
├── proposed/               Pending proposals
├── archive/                Rejected proposals
└── sessions/
    ├── active/             Running agent sessions
    └── completed/          Finished sessions
```

Mote file paths mirror the ID hierarchy. ID `1.2.3` lives at `motes/1/1.2/1.2.3.edn`.

## Extension Points

- **Roles.** Add new role prompts in `prompts/` and map taints in `job.clj`.
- **Taints.** Define new work flags in `schema.clj`, handle in role derivation.
- **Quorum rules.** Adjust thresholds in `verify.clj` and `proposal.clj`.
- **Output formats.** CLI supports EDN and JSON; add formats in `cli.clj`.
