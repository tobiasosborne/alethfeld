# Alethfeld Conceptual Documentation

This document explains the key concepts behind Alethfeld's collaborative proof verification system.

---

## Table of Contents

1. [Workflow](#workflow)
2. [Agents](#agents)
3. [Proposals](#proposals)
4. [Sessions](#sessions)
5. [Motes](#motes)

---

## Workflow

Alethfeld uses a **verification-first workflow** where claims must be evaluated by verifiers before they can be decomposed. This ensures that the proof structure is sound at every level.

### The Verification-First Process

```
1. INITIALIZE
   ↓
2. VERIFY (verifier evaluates claim)
   ↓
3. DECOMPOSE (proposer breaks into substeps)
   ↓
4. REVIEW (advisor approves/rejects)
   ↓
   (repeat 2-4 for each substep)
   ↓
5. VALIDATE (check overall structure)
```

### Step 1: Initialize

Create a new proof project and establish the root claim:

```bash
af init --name "My Proof"
af create --root --claim "Main theorem to prove"
```

The root mote starts with `needs-verification` taint, signaling that a verifier needs to evaluate it.

### Step 2: Verify (Gatekeeper)

The verifier is the gatekeeper. They evaluate each claim and decide its fate:

```bash
af ready --name alice --role verifier
```

The verifier has three options:

**Option A: Vote** - The claim is verifiable as-is
```bash
# If valid (logically sound, no counterexamples):
af vote 1 --for --session $AF_SESSION --reason "Proof is sound"

# If invalid (counterexample found):
af vote 1 --against --session $AF_SESSION --reason "Counterexample: x=2"
```

**Option B: Request Decomposition** - Too complex
```bash
af taint 1 --add needs-decomposition --session $AF_SESSION
```
A proposer will then break it into smaller substeps.

**Option C: Request Refinement** - Missing details
```bash
af taint 1 --add needs-refinement --session $AF_SESSION
```
A prover will add missing assumptions, definitions, or references.

### Step 3: Decompose (Proposer)

When a claim has `needs-decomposition` taint, a proposer breaks it down:

```bash
af ready --name bob --role proposer
af propose 1 --session $AF_SESSION \
  --claim "Step 1: Base case n=3" --difficulty 2 \
  --claim "Step 2: Induction step" --difficulty 4
```

**Decomposition Guidelines:**
- Create 2-5 substeps that TOGETHER prove the parent claim
- Substeps should be mutually exclusive (no overlap)
- Substeps should be collectively exhaustive (complete coverage)
- Each substep must be independently verifiable

### Step 4: Review (Advisor)

Proposed decompositions need advisor approval before becoming official:

```bash
af ready --name carol --role advisor
```

**Evaluation Criteria:**
1. Do substeps together imply the claim? (completeness)
2. Any gaps or missing cases? (exhaustiveness)
3. Any overlap between substeps? (mutual exclusivity)
4. Appropriate difficulty ratings?

```bash
# Approve if sound:
af approve 1 --session $AF_SESSION --reason "Complete and well-structured"

# Reject if flawed:
af reject 1 --session $AF_SESSION --reason "Missing case for n=0"
```

### Step 5: Validate

Throughout the process, validate the proof structure:

```bash
af check        # Verify DAG integrity
af tree 1       # View proof structure
af status       # Overall progress
```

### Quorum

Multiple votes may be required depending on configuration:

```bash
af config set vote-quorum 3      # 3 votes for verification
af config set proposal-quorum 2  # 2 votes for proposal approval
```

---

## Agents

Agents are the participants in the proof verification process. Each agent has a specific role that determines what actions they can take.

### Roles

#### Verifier
**Purpose:** Evaluate claims and act as gatekeeper

**Use when:** A mote has `needs-verification` taint

**Actions:**
- Vote for/against claims
- Add taints (request decomposition or refinement)
- Complete session

**Commands:**
```bash
af vote <id> --for --session TOKEN --reason "..."
af vote <id> --against --session TOKEN --reason "..."
af taint <id> --add needs-decomposition --session TOKEN
af taint <id> --add needs-refinement --session TOKEN
af done --session TOKEN
```

#### Proposer
**Purpose:** Break claims into substeps (decomposition)

**Use when:** A mote has `needs-decomposition` taint

**Actions:**
- Propose decompositions
- Add definitions and assumptions
- Add external references
- Complete session

**Commands:**
```bash
af propose <id> --session TOKEN --claim "..." --claim "..."
af add-definition <id> --session TOKEN --symbol "x" --meaning "..."
af add-assumption <id> --session TOKEN --ref <mote-id> --note "..."
af add-ref <id> --session TOKEN --ref "citation" --note "..."
af done --session TOKEN
```

#### Advisor
**Purpose:** Review and approve/reject proposals

**Use when:** A proposal is pending approval

**Actions:**
- Approve proposals
- Reject proposals
- Complete session

**Commands:**
```bash
af approve <id> --session TOKEN --reason "..."
af reject <id> --session TOKEN --reason "..."
af approve-all --session TOKEN --reason "..."
af done --session TOKEN
```

#### Prover
**Purpose:** Add references, definitions, and assumptions

**Use when:** A mote has `needs-refinement` taint or needs more detail

**Actions:**
- Propose additions
- Add definitions
- Add internal assumptions
- Add external references
- Remove taints
- Complete session

**Commands:**
```bash
af add-definition <id> --session TOKEN --symbol "n" --meaning "..."
af add-assumption <id> --session TOKEN --ref <mote-id> --note "..."
af add-ref <id> --session TOKEN --ref "citation" --note "..."
af taint <id> --remove needs-refinement --session TOKEN
af done --session TOKEN
```

#### Ref-Checker
**Purpose:** Validate external references exist and apply

**Use when:** A mote has references that need checking

**Actions:**
- Add/update references
- Remove taints
- Complete session

**Commands:**
```bash
af add-ref <id> --session TOKEN --ref "corrected citation" --note "..."
af taint <id> --remove needs-refs --session TOKEN
af done --session TOKEN
```

#### Counterexample
**Purpose:** Find flaws and counterexamples (adversarial review)

**Use when:** Adversarial review is needed

**Actions:**
- Vote on claims
- Update status
- Complete session

**Commands:**
```bash
# If counterexample found:
af vote <id> --against --session TOKEN --reason "Counterexample: ..."

# If claim survives:
af vote <id> --for --session TOKEN --reason "No counterexample found"
af taint <id> --remove needs-counterexample --session TOKEN
af done --session TOKEN
```

### Agent Lifecycle

1. **Get Work:** `af ready --name alice --role verifier`
2. **Receive Session:** A session token is assigned
3. **Perform Task:** Execute role-specific actions
4. **Complete:** `af done --session TOKEN`
5. **Terminate:** Agent exits (new work = new agent)

**Important:** After calling `af done`, the agent should terminate. Each unit of work gets a fresh agent instance.

### Getting Assigned Work

```bash
# List available work (no claiming)
af ready

# Auto-claim highest priority job
af ready --name alice

# Filter by role
af ready --name alice --role verifier

# Filter by difficulty
af ready --name alice --difficulty 1-3

# Claim specific job from list
af ready --name alice --job 2
```

---

## Proposals

Proposals are the mechanism for decomposing complex claims into simpler substeps.

### Proposal Lifecycle

```
1. NEEDS-DECOMPOSITION taint added (by verifier)
   ↓
2. Proposer creates proposal with substeps
   ↓
3. Proposal gets PENDING status, parent gets NEEDS-PROPOSAL-REVIEW taint
   ↓
4. Advisors vote to approve/reject
   ↓
5a. APPROVED: Children become FIXED, ready for verification
5b. REJECTED: Children archived, parent gets NEEDS-DECOMPOSITION back
```

### Creating Proposals

```bash
# Get assigned to mote needing decomposition
af ready --name bob --role proposer

# Create proposal with multiple children
af propose 1 --session $AF_SESSION \
  --claim "First substep" --difficulty 2 \
  --claim "Second substep" --difficulty 3 \
  --claim "Third substep" --difficulty 2
```

### Proposal Requirements

Good decompositions should be:

1. **Complete:** Substeps together imply the parent claim
2. **Exhaustive:** No gaps or missing cases
3. **Mutually Exclusive:** Minimal overlap between substeps
4. **Independently Verifiable:** Each substep can be evaluated alone
5. **Appropriately Sized:** 2-5 substeps per decomposition

### Reviewing Proposals

```bash
# Get assigned to mote with pending proposal
af ready --name carol --role advisor

# View the proposal
af show 1 --verbose

# Approve if sound
af approve 1 --session $AF_SESSION --reason "Well-structured decomposition"

# Or reject if flawed
af reject 1 --session $AF_SESSION --reason "Missing edge case for n=0"
```

### Batch Operations

```bash
# Approve all pending proposals you can vote on
af approve-all --session $AF_SESSION --reason "All look good"

# Preview what would be approved
af approve-all --dry-run
```

### Withdrawing Proposals

A proposer can withdraw their own pending proposal:

```bash
af withdraw 1 --session $AF_SESSION
```

This archives the proposed children and restores `needs-decomposition` taint.

### Quorum

The number of votes needed to approve or reject a proposal is configurable:

```bash
af config set proposal-quorum 2  # Requires 2 advisor votes
```

When quorum is reached:
- **All approve:** Children promoted to `:fixed` status
- **All reject:** Children archived, parent gets `needs-decomposition`
- Mixed votes continue until quorum in one direction

---

## Sessions

Sessions are time-bounded work units that track what an agent is doing.

### Session Lifecycle

```
1. CLAIM: Agent claims mote with role
   ↓
2. ACTIVE: Session is active, agent performs work
   ↓
3. DONE: Agent completes session, mote released
   ↓
4. ARCHIVED: Session recorded for history
```

### Creating Sessions

Sessions are typically created via `af ready`:

```bash
af ready --name alice --role verifier
# Returns session token, e.g., abc123-def456
```

Or manually via `af claim`:

```bash
af claim 1.1 --name alice --role verifier
```

### Session Tokens

The session token is your credential for making changes:

```bash
# Pass directly
af vote 1.1 --for --session abc123-def456

# Or use environment variable
export AF_SESSION=abc123-def456
af vote 1.1 --for
```

### Session Enforcement

Most mutating commands require a valid session:
- Vote, approve, reject
- Propose, withdraw
- Add references, definitions, assumptions
- Taint modifications

Read-only commands don't require sessions:
- show, tree, status, check
- ready (in list mode)

### Session Duration

Sessions have a configurable timeout:

```bash
af config set session-timeout-minutes 30  # Default: 30
```

Expired sessions are automatically cleaned up when `af ready` runs.

### Viewing Sessions

```bash
af sessions           # List all active sessions
af sessions --verbose # Show additional details
```

Output shows:
- Session ID (truncated)
- Agent name
- Role
- Mote being worked on
- Time since started
- Status (active, expired, stale)

### Ending Sessions

Always end your session when work is complete:

```bash
af done --session $AF_SESSION
```

**Critical:** After `af done`, the agent should terminate. New work requires spawning a new agent.

### Stale Session Cleanup

If an agent crashes without calling `af done`, the session becomes stale.

Stale sessions are detected by:
- Expired timeout
- Heartbeat failure (future feature)

Cleanup happens automatically when `af ready` runs.

---

## Motes

A **mote** is the fundamental unit of proof in Alethfeld. Each mote represents a single claim that can be verified.

### Mote Structure

```clojure
{:id "1.2.1"                    ; Hierarchical ID
 :claim "The base case holds"   ; The statement to prove
 :status :fixed                 ; Current status
 :priority :p1                  ; Urgency (p0=highest, p4=lowest)
 :difficulty 3                  ; Complexity (1=trivial, 5=very hard)
 :taint #{:needs-verification}  ; Work needed
 :parent "1.2"                  ; Parent mote ID
 :children ["1.2.1.1" "1.2.1.2"] ; Child mote IDs
 :votes []                      ; Verification votes
 :assumptions []                ; Internal and external refs
 :definitions []                ; Symbol definitions
 :depends-on []                 ; Dependency links
 :created-by "alice"            ; Creator agent
 :created-at #inst "..."        ; Creation timestamp
 :claimed-by "bob"              ; Currently claimed by (if any)
}
```

### Mote IDs

Mote IDs are hierarchical, reflecting the proof structure:
- `1` - First root mote
- `1.1` - First child of mote 1
- `1.1.3` - Third child of mote 1.1
- `2` - Second root mote

### Mote Status

| Status | Meaning |
|--------|---------|
| `:fixed` | Active claim, ready for work |
| `:proposed` | Proposed but not yet approved |
| `:verified` | Verified by quorum (proof complete for this node) |
| `:refuted` | Disproven by quorum |
| `:contested` | Mixed votes, needs resolution |
| `:rejected` | Proposal was rejected |

### Mote Taints

Taints signal what work is needed:

| Taint | Meaning |
|-------|---------|
| `:needs-verification` | Ready for verifier evaluation |
| `:needs-decomposition` | Too complex, needs substeps |
| `:needs-refinement` | Missing definitions/assumptions |
| `:needs-proposal-review` | Has pending proposal |
| `:needs-refs` | External refs need checking |
| `:needs-votes` | More votes needed for quorum |
| `:needs-counterexample` | Adversarial review requested |

### Mote Priority

| Priority | Meaning |
|----------|---------|
| `:p0` | Critical - blocking work |
| `:p1` | High - important |
| `:p2` | Medium - normal (default) |
| `:p3` | Low - when time permits |
| `:p4` | Minimal - nice to have |

### Mote Difficulty

| Difficulty | Meaning |
|------------|---------|
| 1 | Trivial - obvious or definitional |
| 2 | Easy - straightforward |
| 3 | Medium - requires thought (default) |
| 4 | Hard - significant effort |
| 5 | Very Hard - major challenge |

### Viewing Motes

```bash
af show 1.1              # Basic view
af show 1.1 --verbose    # Detailed view
af tree 1                # Tree from mote 1
af tree 1 --depth 2      # Limited depth
```

### Mote DAG

Motes form a **directed acyclic graph (DAG)**:
- Parent-child relationships from decomposition
- Dependency links between related motes
- Internal assumptions referencing other motes

The DAG structure ensures:
- No circular dependencies
- Complete coverage of proof
- Traceable verification path

### Verifying DAG Integrity

```bash
af check           # Validate all constraints
af repair --auto   # Fix any issues
```

Validation includes:
- All parent refs exist
- All children refs point back
- No cycles in assumption graph
- Schema validation on all motes
