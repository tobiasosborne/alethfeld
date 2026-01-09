# Agent Workflow

Agents are autonomous processes (typically AI) that perform specialized verification tasks. Alethfeld orchestrates their work through jobs, sessions, and role-based permissions.

## Roles

Six specialized roles, each with distinct responsibilities:

| Role | Purpose | Taints Handled |
|------|---------|----------------|
| **proposer** | Decompose complex claims into sub-claims | `:needs-decomposition` |
| **advisor** | Review and approve/reject proposals | `:needs-advisor-review` |
| **prover** | Construct formal proofs | `:needs-proof` |
| **verifier** | Cast verification votes | `:needs-verification` |
| **ref-checker** | Validate external references | `:needs-ref-check` |
| **counterexample** | Find counterexamples to false claims | `:needs-counterexample` |

## Work Acquisition

### Request a Job

```bash
af ready --agent verifier-1 --role verifier --format json
```

Returns a job if work is available:

```json
{
  "job-id": "job-20260107-143052-a7f3",
  "mote-id": "1.2.3",
  "role": "verifier",
  "priority": "p1",
  "difficulty": 3,
  "mote": { ... },
  "parent": { ... },
  "siblings": [ ... ],
  "prompt": "You are a VERIFIER. Your task is to..."
}
```

### Job Selection Logic

1. **Filter by status.** Only `:fixed` motes need verification.
2. **Filter by taint.** Mote must have role-appropriate taint.
3. **Filter by claim.** Skip claimed motes (unless expired).
4. **Sort by priority.** `:p0` before `:p1` before `:p2`.
5. **Sort by difficulty.** Lower difficulty first (configurable).

### Session Binding

Receiving a job creates an active session:

```clojure
{:session-id "uuid1-uuid2"
 :mote-id    "1.2.3"
 :role       :verifier
 :agent      "verifier-1"
 :started-at #inst "..."
 :expires-at #inst "..."      ; Default 30 minutes
 :actions    []}
```

The agent is now bound to this mote+role until session completes or expires.

## Performing Actions

### Role-Action Matrix

| Role | Allowed Actions |
|------|-----------------|
| proposer | `propose`, `add-child`, `update-claim` |
| advisor | `approve-proposal`, `reject-proposal` |
| prover | `add-proof`, `add-assumption`, `add-definition` |
| verifier | `vote` |
| ref-checker | `validate-ref`, `add-ref` |
| counterexample | `refute`, `add-counterexample` |

Attempting an action outside your role throws `:permission-denied`.

### Voting Example

```bash
af vote 1.2.3 --for --agent verifier-1
```

Validation steps:
1. Agent has active session for mote `1.2.3`.
2. Session role is `:verifier`.
3. Agent did not create or propose this mote.
4. Session has not expired.

### Completing Work

```bash
af done --agent verifier-1
```

Marks session complete, releases claim, records audit trail.

## Conflict Prevention

### Self-Voting Prohibition

Contributors cannot vote on their own work:

- `created-by` cannot vote on that mote.
- `proposed-by` cannot approve their own proposal.
- This is enforced at the session layer.

### Claim Expiration

Claims expire after configurable timeout (default 30 min):

```clojure
(mote/claim-expired? mote timeout-ms)
```

Expired claims are ignored during job selection. Another agent can claim the mote.

### Session Expiration

Sessions expire similarly. Expired session → actions rejected.

## Prompt Templates

Each role has a prompt template in `prompts/`:

```
prompts/
├── roles.edn           # Role definitions
├── proposer.md
├── advisor.md
├── prover.md
├── verifier.md
├── ref-checker.md
├── counterexample.md
└── session-context.md  # Common context
```

`prompt/render-job` assembles the final prompt:

1. Load role template.
2. Interpolate mote claim, assumptions, definitions.
3. Include parent and sibling context.
4. Add vote summary if applicable.
5. Append session context.

## Workflow: Verification

```
                    ┌─────────────┐
                    │ Mote        │
                    │ status:fixed│
                    │ taint:needs-│
                    │ verification│
                    └──────┬──────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ▼                 ▼                 ▼
   ┌──────────┐      ┌──────────┐      ┌──────────┐
   │verifier-1│      │verifier-2│      │verifier-3│
   │ vote:for │      │ vote:for │      │vote:for  │
   └────┬─────┘      └────┬─────┘      └────┬─────┘
         │                 │                 │
         └─────────────────┼─────────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │ Quorum      │
                    │ reached     │
                    │ status →    │
                    │ verified    │
                    └─────────────┘
```

## Workflow: Decomposition

```
┌─────────────────┐
│ Mote            │
│ status: fixed   │
│ taint: needs-   │
│ decomposition   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Proposer        │
│ af propose      │
│ children: [a,b] │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Parent mote     │
│ proposal:{...}  │
│ taint: needs-   │
│ advisor-review  │
└────────┬────────┘
         │
    ┌────┴────┐
    ▼         ▼
┌───────┐ ┌───────┐
│Advisor│ │Advisor│
│approve│ │approve│
└───┬───┘ └───┬───┘
    │         │
    └────┬────┘
         │
         ▼
┌─────────────────┐
│ Proposal        │
│ approved        │
│                 │
│ Children moved  │
│ to motes/       │
│                 │
│ Parent.children │
│ updated         │
└─────────────────┘
```

## Quorum Rules

### Verification Quorum

Default: 3 votes of same type.

```clojure
{:for 3}     → status :verified
{:against 3} → status :refuted
{:for 2 :against 2} → status :contested
```

### Proposal Quorum

Default: 2 approvals.

```clojure
{:approve 2} → proposal approved, children promoted
{:reject 2}  → proposal rejected, children archived
```

Thresholds configurable in `.alethfeld/config.edn`.

## Multi-Agent Coordination

Agents work independently, coordinated only through:

1. **Git sync.** Each agent pulls latest before work, commits after.
2. **Claims.** Prevent duplicate work on same mote.
3. **Sessions.** Enforce role permissions.
4. **Quorum.** Aggregate independent judgments.

No central coordinator. Convergence through eventual consistency.
