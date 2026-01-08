# Alethfeld: Technical Specification

**Version:** 0.1  
**Date:** January 2026

---

## 1. Overview

Alethfeld is a CLI tool (`af`) for managing a DAG of proof steps (motes). Agents query for work, perform tasks, commit results. Git provides persistence and ACID semantics. No external dependencies beyond the filesystem.

---

## 2. Data Model

### 2.1 Mote

The fundamental unit. One EDN file per mote.

```clojure
{:id            "1.2.3"                    ; Hierarchical Lamport-style ID
 :claim         "For all ε > 0, ..."       ; The mathematical statement
 :status        :fixed                     ; See §2.2
 :taint         #{:needs-verification}     ; See §2.3
 :priority      :p1                        ; p0 (critical) → p4 (someday)
 :difficulty    3                          ; 1 (trivial) → 5 (research-level)
 
 ;; Structure
 :parent        "1.2"                      ; Parent mote ID (nil for roots)
 :children      ["1.2.3.1" "1.2.3.2"]      ; Approved children only
 :proposal      nil                        ; Active proposal, see §2.5
 
 ;; Content
 :assumptions   [{:type :internal :ref "1.2.1" :note "Continuity"}
                 {:type :external :ref "arXiv:2301.00001" :note "Thm 3.2"}]
 :definitions   [{:symbol "ε" :meaning "tolerance parameter"}]
 :votes         [{:agent "verifier-1" :vote :for :reason "..." :timestamp #inst "..."}]
 
 ;; Work tracking
 :claimed-by    "prover-agent-1"           ; nil if unclaimed
 :claimed-at    #inst "2026-01-07T..."
 
 ;; Metadata
 :created-by    "proposer-1"
 :created-at    #inst "2026-01-07T..."
 :updated-at    #inst "2026-01-07T..."}
```

### 2.2 Status Enum

```clojure
:proposed    ; Exists in a proposal, pending advisor approval
:rejected    ; Proposal rejected, mote archived
:fixed       ; Structure locked, content can be worked
:verified    ; Proven correct by quorum
:refuted     ; Counterexample found
:contested   ; Conflicting votes, needs arbitration
```

**State transitions:**
```
proposed  ─┬─► fixed ─┬─► verified
           │          ├─► refuted
           │          └─► contested
           └─► rejected
```

### 2.3 Taint Flags

Composable set of work indicators:

```clojure
:needs-decomposition      ; Proposer should create children
:needs-proposal-review    ; Advisor should vote on pending proposal
:needs-refinement         ; Prover should add details/assumptions
:needs-verification       ; Verifier should check correctness
:needs-refs               ; Ref-checker should validate citations
:needs-votes              ; Quorum not yet reached
:needs-counterexample     ; Adversarial check requested
```

### 2.4 Role → Taint Mapping

| Role             | Processes taints            |
|------------------|-----------------------------|
| `proposer`       | `:needs-decomposition`      |
| `advisor`        | `:needs-proposal-review`    |
| `prover`         | `:needs-refinement`         |
| `verifier`       | `:needs-verification`       |
| `ref-checker`    | `:needs-refs`               |
| `counterexample` | `:needs-counterexample`     |

### 2.5 Proposal

Tracks a proposed decomposition awaiting advisor approval:

```clojure
{:id           "prop-20260107-a7f3"
 :proposed-by  "proposer-1"
 :proposed-at  #inst "2026-01-07T..."
 :children     ["1.2.1" "1.2.2" "1.2.3"]   ; Proposed child IDs
 :votes        [{:agent "advisor-1" :vote :approve :reason "..." :timestamp #inst "..."}]
 :status       :pending}                    ; :pending | :approved | :rejected
```

**Invariant:** All children in a proposal are approved or rejected atomically.

### 2.6 Priority & Difficulty

**Priority** (work urgency):
- `:p0` — Critical, blocking everything
- `:p1` — High, needed soon
- `:p2` — Medium (default)
- `:p3` — Low, when time permits
- `:p4` — Someday, backlog

**Difficulty** (agent capability required):
- `1` — Trivial, any agent
- `2` — Easy
- `3` — Medium (default)
- `4` — Hard
- `5` — Research-level, expert agents only

Difficulty is inherited from parent unless overridden.

---

## 3. File Structure

```
.alethfeld/
├── config.edn                    # Project configuration
├── motes/
│   ├── 1.edn                     # Root mote
│   ├── 1/
│   │   ├── 1.1.edn
│   │   ├── 1.2.edn
│   │   └── 1.2/
│   │       ├── 1.2.1.edn
│   │       └── 1.2.2.edn
│   └── 2.edn                     # Another root
├── proposed/                     # Proposed motes (pending approval)
│   ├── 1.2.3.edn
│   └── 1.2.4.edn
└── archive/                      # Rejected proposals
    └── 1.2/
        └── prop-20260106-xyz/
            ├── 1.2.1.edn
            └── 1.2.2.edn
```

### 3.1 Path Derivation

```clojure
(defn mote-id->path [id status]
  (let [parts (str/split id #"\.")
        parent-path (str/join "/" (butlast parts))
        filename (str id ".edn")]
    (case status
      :proposed (str "proposed/" filename)
      :rejected (str "archive/" parent-path "/" filename)  ; + proposal-id
      (if (= 1 (count parts))
        (str "motes/" filename)
        (str "motes/" parent-path "/" filename)))))

;; Examples:
;; "1"       :fixed    → "motes/1.edn"
;; "1.2"     :fixed    → "motes/1/1.2.edn"
;; "1.2.3"   :fixed    → "motes/1/1.2/1.2.3.edn"
;; "1.2.3"   :proposed → "proposed/1.2.3.edn"
```

### 3.2 Config

```clojure
;; config.edn
{:project-name     "My Proof"
 :version          "0.1"
 :default-difficulty 3
 :vote-quorum      2              ; Votes needed for verification
 :proposal-quorum  2              ; Votes needed for proposal approval
 :claim-timeout-minutes 30}       ; Auto-unclaim after timeout
```

---

## 4. Malli Schemas

```clojure
(ns alethfeld.schema
  (:require [malli.core :as m]))

(def MoteId [:string {:min 1}])

(def Status
  [:enum :proposed :rejected :fixed :verified :refuted :contested])

(def Taint
  [:enum
   :needs-decomposition :needs-proposal-review :needs-refinement
   :needs-verification :needs-refs :needs-votes :needs-counterexample])

(def Priority [:enum :p0 :p1 :p2 :p3 :p4])

(def Difficulty [:int {:min 1 :max 5}])

(def Role
  [:enum :proposer :advisor :prover :verifier :ref-checker :counterexample])

(def InternalRef
  [:map
   [:type [:= :internal]]
   [:ref MoteId]
   [:note {:optional true} :string]])

(def ExternalRef
  [:map
   [:type [:= :external]]
   [:ref :string]
   [:note {:optional true} :string]])

(def Assumption [:or InternalRef ExternalRef])

(def Definition
  [:map
   [:symbol :string]
   [:meaning :string]])

(def Vote
  [:map
   [:agent :string]
   [:vote [:enum :for :against]]
   [:reason {:optional true} :string]
   [:timestamp inst?]])

(def ProposalVote
  [:map
   [:agent :string]
   [:vote [:enum :approve :reject]]
   [:reason {:optional true} :string]
   [:timestamp inst?]])

(def Proposal
  [:map
   [:id :string]
   [:proposed-by :string]
   [:proposed-at inst?]
   [:children [:vector MoteId]]
   [:votes [:vector ProposalVote]]
   [:status [:enum :pending :approved :rejected]]])

(def Mote
  [:map
   [:id MoteId]
   [:claim :string]
   [:status Status]
   [:taint [:set Taint]]
   [:priority Priority]
   [:difficulty Difficulty]
   
   [:parent {:optional true} MoteId]
   [:children [:vector MoteId]]
   [:proposal {:optional true} Proposal]
   
   [:assumptions [:vector Assumption]]
   [:definitions [:vector Definition]]
   [:votes [:vector Vote]]
   
   [:claimed-by {:optional true} :string]
   [:claimed-at {:optional true} inst?]
   
   [:created-by :string]
   [:created-at inst?]
   [:updated-at inst?]
   [:meta {:optional true} [:map-of :keyword :any]]])

(def Job
  [:map
   [:job-id :string]
   [:mote-id MoteId]
   [:role Role]
   [:difficulty Difficulty]
   [:priority Priority]
   [:mote Mote]
   [:parent {:optional true} Mote]
   [:siblings [:vector Mote]]
   [:prompt :string]])

(def DifficultyRange
  [:or
   Difficulty
   [:tuple Difficulty Difficulty]])

(def PriorityRange
  [:or
   Priority
   [:tuple Priority Priority]])

(def ReadyOptions
  [:map
   [:agent {:optional true} :string]
   [:role {:optional true} Role]
   [:difficulty {:optional true} DifficultyRange]
   [:priority {:optional true} PriorityRange]
   [:max {:optional true} [:int {:min 1}]]
   [:no-claim {:optional true} :boolean]
   [:format {:optional true} [:enum :edn :json]]])
```

---

## 5. CLI Specification

### 5.1 Command Summary

```
af init                              Initialize .alethfeld/ in current directory
af ready [OPTIONS]                   Get next job(s) for an agent
af show <id>                         Display mote details
af create <parent-id> [OPTIONS]      Create child mote (fixed)
af create --root [OPTIONS]           Create root mote

af propose <parent-id> [OPTIONS]     Propose decomposition into children
af approve <parent-id> [OPTIONS]     Vote to approve proposal
af reject <parent-id> [OPTIONS]      Vote to reject proposal

af update <id> [OPTIONS]             Update mote fields
af vote <id> [OPTIONS]               Cast verification vote
af taint <id> [OPTIONS]              Add/remove taint flags
af claim <id> --agent <name>         Claim mote for work
af unclaim <id>                      Release claim

af add-ref <id> [OPTIONS]            Add external reference
af add-assumption <id> [OPTIONS]     Add internal assumption
af add-definition <id> [OPTIONS]     Add definition

af check                             Validate DAG integrity
af log <id>                          Show git history for mote
af sync                              Pull, commit, push
```

### 5.2 Global Options

```
--format edn|json                    Output format (default: edn)
--help                               Show help
--version                            Show version
```

### 5.3 Command Details

#### `af init`

```bash
af init [--name <project-name>]
```

Creates `.alethfeld/` directory with `config.edn`. Initializes git repo if not present.

#### `af ready`

```bash
af ready [--agent <name>]            # Auto-claim for agent
         [--role <role>]             # Filter by role
         [--difficulty <n|n-m>]      # Filter by difficulty (exact or range)
         [--priority <p|p-q>]        # Filter by priority (exact or range)
         [--max <n>]                 # Return up to n jobs (default: 1)
         [--no-claim]                # Don't auto-claim
         [--format edn|json]
```

Returns `Job` (single) or `[Job ...]` (if `--max > 1`).

**Selection algorithm:**
1. Filter by status (not `:verified`, `:rejected`)
2. Filter by unclaimed (or claim expired)
3. Filter by role (if specified)
4. Filter by difficulty range (if specified)
5. Filter by priority range (if specified)
6. Sort by: priority (p0 first), then difficulty (lower first)
7. Take first N

#### `af show`

```bash
af show <id> [--format edn|json]
```

Returns full `Mote` including resolved parent/children.

#### `af create`

```bash
af create <parent-id> --claim <text>
          [--difficulty <n>]         # Default: inherit from parent
          [--priority <p>]           # Default: inherit from parent
          [--agent <name>]           # created-by
          [--format edn|json]

af create --root --claim <text>
          [--difficulty <n>]         # Default: 3
          [--priority <p>]           # Default: :p2
          [--agent <name>]
          [--format edn|json]
```

Creates mote with status `:fixed` and taint `#{:needs-decomposition}`.

#### `af propose`

```bash
af propose <parent-id>
           --claim <text> [--difficulty <n>] [--claim <text> ...]
           --agent <name>
           [--format edn|json]
```

Creates multiple proposed children and a `Proposal` on the parent. Sets parent taint to `:needs-proposal-review`.

**Example:**
```bash
af propose 1.2 \
  --claim "First substep" --difficulty 2 \
  --claim "Second substep" --difficulty 3 \
  --claim "Third substep" --difficulty 2 \
  --agent proposer-1
```

#### `af approve` / `af reject`

```bash
af approve <parent-id> --agent <name> [--reason <text>]
af reject <parent-id> --agent <name> [--reason <text>]
```

Casts proposal vote. If quorum reached:
- **approve**: Children move to `:fixed`, parent gets `:children` populated
- **reject**: Children move to `:rejected` (archived), parent gets `:needs-decomposition`

#### `af update`

```bash
af update <id> [--status <status>]
               [--priority <p>]
               [--difficulty <n>]
               [--claim <text>]
               [--format edn|json]
```

#### `af vote`

```bash
af vote <id> --for|--against
             --agent <name>
             [--reason <text>]
             [--format edn|json]
```

Casts verification vote. If quorum reached, updates status to `:verified` or `:contested`.

#### `af taint`

```bash
af taint <id> --add <taint> [--add <taint> ...]
af taint <id> --remove <taint> [--remove <taint> ...]
```

#### `af claim` / `af unclaim`

```bash
af claim <id> --agent <name>
af unclaim <id>
```

#### `af add-ref` / `af add-assumption` / `af add-definition`

```bash
af add-ref <id> --ref <citation> [--note <text>]
af add-assumption <id> --ref <mote-id> [--note <text>]
af add-definition <id> --symbol <sym> --meaning <text>
```

#### `af check`

Validates:
1. All parent refs exist
2. All children refs exist and point back
3. No cycles in assumption graph
4. All internal assumption refs exist
5. Schema validation on all motes

Returns exit code 0 if valid, 1 if errors (with details).

#### `af log`

```bash
af log <id> [--limit <n>]
```

Runs `git log` on the mote's file.

#### `af sync`

```bash
af sync
```

Equivalent to:
```bash
git pull --rebase
git add .alethfeld/
git commit -m "af sync $(date -Iseconds)" --allow-empty
git push
```

---

## 6. Job Dispatch & Prompts

### 6.1 Job Structure

```clojure
{:job-id    "job-20260107-143052-a7f3"
 :mote-id   "1.2.3"
 :role      :verifier
 :difficulty 3
 :priority  :p1
 :mote      {... full mote ...}
 :parent    {... parent mote or nil ...}
 :siblings  [{... sibling motes ...}]
 :prompt    "You are a VERIFIER agent..."}
```

### 6.2 Prompt Templates

Role-specific prompts include:
- Context (mote, parent, siblings, assumptions, definitions)
- Task description
- Available `af` commands
- Completion instructions

See Appendix A for full prompt templates.

---

## 7. Transactions & ACID

### 7.1 Write Protocol

Every mutation:
1. Load affected motes
2. Validate changes (schema, DAG integrity)
3. Write mote files
4. `git add -A .alethfeld/`
5. `git commit -m "<af command description>"`

```clojure
(defn transact! [description & write-fns]
  (doseq [f write-fns] (f))
  (shell "git" "add" "-A" ".alethfeld/")
  (shell "git" "commit" "-m" (str "af: " description)))
```

### 7.2 ACID Guarantees

| Property    | Mechanism                                    |
|-------------|----------------------------------------------|
| Atomicity   | Single git commit per CLI invocation         |
| Consistency | Schema + DAG validation before write         |
| Isolation   | File-per-mote; conflicts only on same mote   |
| Durability  | Git commit to disk; `af sync` for remote     |

### 7.3 Conflict Resolution

Git merge conflicts occur only when two agents modify the same mote file. Resolution:
1. Agent with conflict runs `af sync`
2. Git reports conflict
3. Agent (or human) resolves manually
4. Commits resolution

Minimized by: claiming before work, one file per mote.

### 7.4 Known Limitations

**Race Window:** There is a small window (~<100ms) between DAG validation passing and git commit completing. If the process crashes during this window:
- Files on disk are validated and consistent
- Git history does not reflect the changes
- Other agents using `git pull` won't see uncommitted changes

This is acceptable because:
1. Validated changes are never rolled back (data integrity preserved)
2. Manual recovery: `git add . && git commit -m 'recovery'`
3. The window is brief for typical operations

Future work may add startup recovery to detect and commit orphaned validated changes.

---

## 8. DAG Invariants

1. **Acyclic**: No cycles through `:parent` or `:assumptions` refs
2. **Parent-child consistency**: If A has child B, then B has parent A
3. **Ref integrity**: All `:internal` assumption refs exist
4. **Proposal atomicity**: Proposed children share fate (all approved or all rejected)
5. **Status consistency**: Children cannot be `:verified` if parent is `:proposed`

Enforced by `af check` and on every write.

---

## 9. Dependencies

```clojure
;; deps.edn
{:paths ["src"]
 :deps {org.clojure/clojure   {:mvn/version "1.12.0"}
        metosin/malli         {:mvn/version "0.16.4"}
        org.clojure/data.json {:mvn/version "2.5.0"}
        babashka/process      {:mvn/version "0.5.22"}
        babashka/fs           {:mvn/version "0.5.22"}}
 :aliases
 {:run {:main-opts ["-m" "alethfeld.cli"]}
  :build {:deps {io.github.clojure/tools.build {:mvn/version "0.10.5"}}
          :ns-default build}}}
```

---

## 10. Module Structure

```
src/alethfeld/
├── schema.clj          # Malli schemas
├── mote.clj            # Mote I/O (read, write, path derivation)
├── dag.clj             # DAG operations (validate, find cycles, traverse)
├── job.clj             # Job selection, filtering, sorting
├── prompt.clj          # Prompt templates and rendering
├── git.clj             # Git operations (commit, log, sync)
├── cli.clj             # CLI entry point, arg parsing
└── util.clj            # Timestamps, ID generation, formatting
```

---

## Appendix A: Prompt Templates

### A.1 Proposer

```
You are a PROPOSER agent. Your task is to DECOMPOSE this mote into substeps.

MOTE: {{mote-id}}
CLAIM: {{claim}}
PRIORITY: {{priority}}
DIFFICULTY: {{difficulty}}

PARENT: {{#parent}}{{id}} — {{claim}}{{/parent}}{{^parent}}(root){{/parent}}

ASSUMPTIONS:
{{#assumptions}}
- [{{type}}] {{ref}}{{#note}}: {{note}}{{/note}}
{{/assumptions}}
{{^assumptions}}(none){{/assumptions}}

TASK:
1. Decompose into 2-5 substeps that TOGETHER prove the claim
2. Substeps must be mutually exclusive and collectively exhaustive
3. Each substep must be independently verifiable
4. Assign difficulty (1-5) to each substep

COMMAND:
af propose {{mote-id}} \
  --claim "<substep 1>" --difficulty <n> \
  --claim "<substep 2>" --difficulty <n> \
  ... \
  --agent <your-name>

When done: af unclaim {{mote-id}}
```

### A.2 Advisor

```
You are an ADVISOR agent. Your task is to EVALUATE a proposed decomposition.

MOTE: {{mote-id}}
CLAIM: {{claim}}

PROPOSED CHILDREN:
{{#proposal.children}}
{{i}}. {{id}}: {{claim}} (difficulty {{difficulty}})
{{/proposal.children}}

PROPOSED BY: {{proposal.proposed-by}}
VOTES: {{proposal.vote-summary}}

EVALUATE:
1. Do substeps together imply the claim? (completeness)
2. Any gaps or missing cases? (exhaustiveness)
3. Any overlap between substeps? (mutual exclusivity)
4. Appropriate difficulty ratings?

COMMANDS:
af approve {{mote-id}} --agent <your-name> --reason "<why>"
af reject {{mote-id}} --agent <your-name> --reason "<flaw>"

When done: af unclaim {{mote-id}}
```

### A.3 Prover

```
You are a PROVER agent. Your task is to REFINE this mote.

MOTE: {{mote-id}}
CLAIM: {{claim}}
PRIORITY: {{priority}}
DIFFICULTY: {{difficulty}}

CHILDREN:
{{#children}}
- {{id}}: {{claim}} [{{status}}]
{{/children}}
{{^children}}(none — may need decomposition first){{/children}}

ASSUMPTIONS:
{{#assumptions}}
- [{{type}}] {{ref}}{{#note}}: {{note}}{{/note}}
{{/assumptions}}

TASK:
1. Add missing assumptions (internal refs to other motes)
2. Add external references (citations)
3. Add definitions for symbols used
4. Ensure claim is precisely stated

COMMANDS:
af add-assumption {{mote-id}} --ref <mote-id> --note "<why>"
af add-ref {{mote-id}} --ref "<citation>" --note "<what it provides>"
af add-definition {{mote-id}} --symbol "<sym>" --meaning "<meaning>"
af taint {{mote-id}} --remove needs-refinement
af taint {{mote-id}} --add needs-verification

When done: af unclaim {{mote-id}}
```

### A.4 Verifier

```
You are a VERIFIER agent. Your task is to VALIDATE this mote.

MOTE: {{mote-id}}
CLAIM: {{claim}}
PRIORITY: {{priority}}
DIFFICULTY: {{difficulty}}

CHILDREN (substeps):
{{#children}}
- {{id}}: {{claim}} [{{status}}]
{{/children}}

ASSUMPTIONS:
{{#assumptions}}
- [{{type}}] {{ref}}{{#note}}: {{note}}{{/note}}
{{/assumptions}}

DEFINITIONS:
{{#definitions}}
- {{symbol}}: {{meaning}}
{{/definitions}}

VOTES SO FAR: {{vote-summary}}

TASK:
1. Check if substeps logically entail the claim
2. Verify all assumptions are justified
3. Look for gaps, errors, unjustified leaps
4. Cast your vote with reasoning

COMMANDS:
af vote {{mote-id}} --for --agent <your-name> --reason "<why valid>"
af vote {{mote-id}} --against --agent <your-name> --reason "<flaw>"
af taint {{mote-id}} --add needs-counterexample  (if suspicious)
af taint {{mote-id}} --add needs-refinement      (if incomplete)

When done: af unclaim {{mote-id}}
```

### A.5 Ref-Checker

```
You are a REF-CHECKER agent. Your task is to VALIDATE external references.

MOTE: {{mote-id}}
CLAIM: {{claim}}

EXTERNAL REFERENCES:
{{#external-refs}}
- {{ref}}{{#note}}: "{{note}}"{{/note}}
{{/external-refs}}

TASK:
1. Verify each reference exists
2. Confirm cited result supports the claim as stated
3. Flag misquotations or misattributions
4. Note preprint vs peer-reviewed status

COMMANDS:
af add-ref {{mote-id}} --ref "<corrected>" --note "<update>"  (to fix)
af taint {{mote-id}} --remove needs-refs                      (when done)

When done: af unclaim {{mote-id}}
```

### A.6 Counterexample

```
You are a COUNTEREXAMPLE agent. Your task is to FIND FLAWS.

MOTE: {{mote-id}}
CLAIM: {{claim}}

ASSUMPTIONS:
{{#assumptions}}
- [{{type}}] {{ref}}{{#note}}: {{note}}{{/note}}
{{/assumptions}}

DEFINITIONS:
{{#definitions}}
- {{symbol}}: {{meaning}}
{{/definitions}}

TASK:
1. Construct counterexamples
2. Find edge cases where claim fails
3. Check boundary conditions
4. Verify claim isn't vacuously true

IF COUNTEREXAMPLE FOUND:
af update {{mote-id}} --status refuted
af vote {{mote-id}} --against --agent <your-name> --reason "Counterexample: <desc>"

IF CLAIM SURVIVES:
af taint {{mote-id}} --remove needs-counterexample
af vote {{mote-id}} --for --agent <your-name> --reason "No counterexample found"

When done: af unclaim {{mote-id}}
```

---

## Appendix B: Example Session

```bash
# Initialize
$ af init --name "Epsilon-Delta Proof"

# Create root mote
$ af create --root --claim "lim(x→a) f(x) = L" --agent human --priority p1
{:id "1" :status :fixed :taint #{:needs-decomposition} ...}

# Proposer gets work
$ af ready --agent proposer-1 --role proposer
{:job-id "..." :mote-id "1" :role :proposer :prompt "You are a PROPOSER..."}

# Proposer creates decomposition
$ af propose 1 \
    --claim "f is defined on open interval containing a" --difficulty 1 \
    --claim "For all ε>0 there exists δ>0 such that..." --difficulty 3 \
    --agent proposer-1

# Advisor reviews
$ af ready --agent advisor-1 --role advisor
{:job-id "..." :mote-id "1" :role :advisor :prompt "You are an ADVISOR..."}

$ af approve 1 --agent advisor-1 --reason "Complete decomposition"

# Second advisor approves (quorum = 2)
$ af approve 1 --agent advisor-2 --reason "Agree"

# Children now fixed, verifier gets work
$ af ready --agent verifier-1 --role verifier
{:job-id "..." :mote-id "1.1" :role :verifier ...}

$ af vote 1.1 --for --agent verifier-1 --reason "Trivially satisfied by hypothesis"

# ... continues until root is verified
```
