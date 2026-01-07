# Alethfeld CLI Requirements Specification v2.3

**Status**: Draft  
**Date**: 2026-01-07  
**Target**: Clojure + Babashka implementation  
**Revision Note**: Adds context emission system to reduce orchestrator prompt size

---

## Changelog from v2.2

### New Features
- **Context emission system**: `context`, `next`, `help` commands emit phase-specific prompts
- **Self-documenting CLI**: Reduces orchestrator prompt from ~24KB to ~3KB
- **Transition hooks**: `fsm transition` emits instructions for new phase
- **Schema introspection**: `schema` command for on-demand schema lookup

### Philosophy Change
- CLI becomes a **co-pilot** that guides the agent, not just a passive tool
- Static workflow knowledge moved from prompt to CLI
- Agent pulls context on demand rather than loading everything upfront

---

## 1. Executive Summary

The Alethfeld CLI is the sole interface for manipulating semantic proof graphs. Version 2.3 adds:

1. **Context emission** — `context` command emits phase-specific prompt fragments
2. **Next action suggestions** — `next` command suggests optimal next action
3. **On-demand help** — `help` command provides command syntax when needed
4. **Transition hooks** — Phase transitions emit instructions for new phase
5. **Schema introspection** — `schema` command for EDN format lookup

The goal is to enable a minimal orchestrator prompt (~3KB) that pulls detailed instructions from the CLI as needed.

---

## 2. Design Principles

### 2.1 Core Invariants

1. **Graph is canonical**: The `.edn` file is the single source of truth
2. **Operations are atomic**: Each command succeeds completely or fails with no side effects
3. **IDs are permanent**: Node IDs are never reused; deleted nodes are archived
4. **Taint propagates**: Verification status changes cascade to dependents automatically
5. **FSM is enforced**: Invalid phase transitions are rejected at CLI level
6. **Output is EDN**: All command output is valid EDN (with `--human` flag for formatting)
7. **Stdin-first**: All commands with EDN input support `--stdin` or `-`
8. **Self-documenting**: CLI provides its own documentation via `help` and `context`

### 2.2 Context Emission Philosophy

The CLI emits context in three modes:

| Mode | Command | Purpose |
|------|---------|---------|
| **Phase context** | `context` | What to do in current phase |
| **Next suggestion** | `next` | Optimal next action with rationale |
| **Command help** | `help <cmd>` | Syntax and examples for specific command |

This enables:
- Minimal orchestrator prompt (behavioral principles only)
- Accurate, state-aware instructions (generated from actual graph state)
- Easier updates (change CLI, not prompts)

---

## 3. Context Emission Commands (NEW)

### 3.1 context

Emit phase-specific prompt fragment with current task instructions.

```
alethfeld context <graph-file> [options]

Options:
  --format <fmt>      Output format: markdown | edn (default: markdown)
  --include-schema    Include relevant EDN schemas
  --verbose           Include full command syntax

Output (markdown, example for expand-verify-loop):
```

**Example output for `expand-verify-loop` phase:**

```markdown
## Current Phase: expand-verify-loop

### Your Task
Process pending work in priority order:
1. If subgraphs are `:in-progress`: continue processing them
2. Else if expansion queue non-empty: expand next node
3. Else if verification queue non-empty: verify next node (triple-verifier)
4. When all queues empty and subgraphs done: transition to reference-check

### Current State
- Expansions pending: [:2-a1b2c3, :2-d4e5f6]
- Verifications pending: [:2-e7f8a9]
- Subgraphs: sub-001 (in-progress), sub-002 (pending)

### Available Commands
```bash
# Pop and expand
alethfeld fsm queue graph.edn --pop-expansion
alethfeld add-node graph.edn --stdin

# Pop and verify (triple)
alethfeld fsm queue graph.edn --pop-verification  
alethfeld verify record-vote graph.edn <node> V1 <verdict> --reason "..."
alethfeld verify record-vote graph.edn <node> V2 <verdict> --reason "..."
alethfeld verify record-vote graph.edn <node> V3 <verdict> --reason "..."
alethfeld verify tally graph.edn <node>
alethfeld update-status graph.edn <node> <status>

# Transition when done
alethfeld fsm transition graph.edn reference-check
```

### Expand Protocol
1. Pop node: `alethfeld fsm queue graph.edn --pop-expansion`
2. SPAWN Prover with: `{:request :expand :step-id <id> :context <deps>}`
3. For each substep in response:
   ```bash
   echo '<node-edn>' | alethfeld add-node graph.edn --stdin
   ```

### Triple-Verify Protocol
1. Pop node: `alethfeld fsm queue graph.edn --pop-verification`
2. Get context: `alethfeld show graph.edn <node-id>`
3. SPAWN Verifier V1 (skeptical): focus on type checking, definition expansion
4. SPAWN Verifier V2 (adversarial): focus on counterexamples, boundary cases
5. SPAWN Verifier V3 (pedantic): focus on quantifiers, scope, domain
6. Record votes and tally:
   ```bash
   alethfeld verify record-vote graph.edn <node> V1 <verdict> --reason "..."
   alethfeld verify record-vote graph.edn <node> V2 <verdict> --reason "..."
   alethfeld verify record-vote graph.edn <node> V3 <verdict> --reason "..."
   alethfeld verify tally graph.edn <node>
   ```
7. Apply outcome:
   - `:accept` → `update-status <node> verified`
   - `:challenge` → `fsm queue --add-expansion <node>`, `verify reset <node>`
   - `:reject` → `update-status <node> rejected`, SPAWN Prover for revision

### Voting Rules (Enforced by CLI)
1. Any `:reject` → outcome is `:reject`
2. Else if 3/3 `:accept` → outcome is `:accept`
3. Else → outcome is `:challenge`

### Per-Node Iteration Tracking
Node :2-a1b2c3 has 3/7 verification attempts (approaching limit)
Node :2-d4e5f6 has 1/7 verification attempts

### Valid Transitions
- `reference-check`: When all queues empty and nodes terminal
- `decomposition`: If new subgraph candidates found (requires all subgraphs merged/pending)
- `escalated`: If verification iterations exceed limit
```

**Output (EDN format):**

```clojure
{:phase :expand-verify-loop
 :task "Process pending expansions and verifications"
 :state {:expansions [:2-a1b2c3 :2-d4e5f6]
         :verifications [:2-e7f8a9]
         :subgraphs {:sub-001 :in-progress :sub-002 :pending}}
 :protocols
 {:expand {:steps ["Pop node" "Spawn Prover" "Add substeps"]
           :prover-input {:request :expand :step-id "<id>" :context "<deps>"}}
  :verify {:steps ["Pop node" "Spawn V1 V2 V3" "Record votes" "Tally" "Apply"]
           :voting-rules {:reject-any true :accept-unanimous true}}}
 :valid-transitions [:reference-check :decomposition :escalated]
 :warnings ["Node :2-a1b2c3 at 3/7 attempts"]}
```

---

### 3.2 next

Suggest optimal next action with rationale.

```
alethfeld next <graph-file> [options]

Options:
  --format <fmt>      Output format: edn | human (default: edn)

Output (EDN):
  {:suggestion :pop-verification
   :reason "Verification queue has 3 items; expansion queue empty"
   :command "alethfeld fsm queue graph.edn --pop-verification"
   :node-id :2-a1b2c3
   :node-context {:statement "For all x, P(x) implies Q(x)"
                  :dependencies [:1-d4e5f6]
                  :status :proposed
                  :verification-attempts 1}}

Output (human):
  Next: Verify node :2-a1b2c3
  
  Reason: Verification queue has 3 items; expansion queue empty
  
  Command:
    alethfeld fsm queue graph.edn --pop-verification
  
  Node context:
    Statement: For all x, P(x) implies Q(x)
    Dependencies: :1-d4e5f6
    Status: proposed
    Verification attempts: 1/7
```

**Decision logic for `next`:**

```clojure
(defn suggest-next [graph]
  (let [{:keys [phase]} (:fsm graph)
        {:keys [expansions verifications]} (get-in graph [:fsm :pending])
        subgraphs (get-subgraph-statuses graph)]
    (cond
      ;; Terminal phases
      (#{:complete :escalated} phase)
      {:suggestion :none :reason "Workflow complete"}
      
      ;; Phase-specific logic
      (= phase :expand-verify-loop)
      (cond
        (some #(= :in-progress (:status %)) subgraphs)
        {:suggestion :process-subgraph
         :reason "In-progress subgraph needs attention"
         :subgraph (first (filter #(= :in-progress (:status %)) subgraphs))}
        
        (seq expansions)
        {:suggestion :pop-expansion
         :reason "Expansion queue non-empty"
         :node-id (first expansions)
         :command "alethfeld fsm queue graph.edn --pop-expansion"}
        
        (seq verifications)
        {:suggestion :pop-verification
         :reason "Verification queue non-empty"
         :node-id (first verifications)
         :command "alethfeld fsm queue graph.edn --pop-verification"}
        
        :else
        {:suggestion :transition
         :reason "All queues empty"
         :command "alethfeld fsm transition graph.edn reference-check"})
      
      ;; Other phases have simpler logic
      :else
      (get-phase-suggestion phase graph))))
```

---

### 3.3 help

Provide command syntax and examples on demand.

```
alethfeld help [command] [subcommand]

Arguments:
  [command]           Command name (optional, lists all if omitted)
  [subcommand]        Subcommand name (e.g., "fsm status")

Output (no args):
  Alethfeld CLI v2.3
  
  Commands:
    init              Create new proof graph
    add-node          Add a node to the graph
    update-status     Update node verification status
    replace-node      Replace a rejected node
    delete-node       Remove a leaf node
    extract-lemma     Extract subgraph as lemma
    external-ref      Manage external references
    validate          Check graph integrity
    lint              Semantic analysis
    recompute         Recalculate derived values
    stats             Show graph statistics
    show              Display node or structure
    diff              Compare graphs
    fsm               Workflow state machine
    subgraph          Subgraph operations
    checkpoint        Save/restore state
    verify            Multi-verifier operations
    export            Export to other formats
    context           Emit phase-specific prompt (NEW)
    next              Suggest next action (NEW)
    help              Show this help
    schema            Show EDN schemas (NEW)
  
  Run 'alethfeld help <command>' for details.

Output (specific command):
  alethfeld add-node <graph-file> [options]
  
  Add a node to the proof graph.
  
  Options:
    --stdin             Read node EDN from stdin (RECOMMENDED)
    --file <path>       Read node EDN from file
  
  Node EDN format:
    {:type <keyword>           ; required: :claim :assumption :definition etc.
     :statement "<LaTeX>"      ; required
     :dependencies #{...}      ; optional, default #{}
     :justification <keyword>  ; required: :modus-ponens :case-split etc.
     :external-citation {...}} ; optional, auto-creates ref
  
  Example:
    echo '{:type :claim 
           :statement "P implies Q" 
           :dependencies #{:1-a1b2c3}
           :justification :modus-ponens}' | alethfeld add-node graph.edn --stdin
  
  Output:
    {:ok true :node-id :2-d4e5f6 :version 15 :taint :clean}
  
  Exit codes:
    0  Success
    1  Validation error
    4  Invalid FSM state
    5  Precondition failed
```

---

### 3.4 schema

Show EDN schemas for input/output formats.

```
alethfeld schema <type>

Arguments:
  <type>              Schema type:
                      - node          Node EDN for add-node
                      - prover-input  Input format for Prover subagent
                      - prover-output Output format from Prover
                      - verifier-input  Input for Verifier
                      - verifier-output Output from Verifier
                      - adviser-input   Input for Adviser
                      - adviser-output  Output from Adviser
                      - audit-result    Result format for audit
                      - strategy-result Result format for strategy
                      - graph          Full graph schema
                      - ref            External reference format

Output (example for 'node'):
  Node EDN Schema (for add-node --stdin)
  
  Required fields:
    :type           #{:assumption :local-assume :local-discharge 
                      :definition :claim :lemma-ref :external-ref :qed}
    :statement      String, LaTeX format
    :justification  #{:assumption :modus-ponens :case-split :induction-base
                      :induction-step :algebraic-rewrite :admitted ...}
  
  Optional fields:
    :dependencies   Set of node ID keywords, e.g., #{:1-a1b2c3}
    :scope          Set of local-assume IDs currently in scope
    :parent         Parent node ID (for substeps)
    :discharges     Node ID (required if type = :local-discharge)
    :external-citation
      {:doi "..."              ; DOI string
       :claimed-statement "..."} ; What the reference claims
  
  Example:
    {:type :claim
     :statement "For all $x > 0$, $\\log(x)$ is defined"
     :dependencies #{:0-a1b2c3 :1-d4e5f6}
     :justification :universal-intro}

Output (example for 'verifier-input'):
  Verifier Input Schema (what to send to Verifier subagent)
  
  {:step :<node-id>
   :claim "<LaTeX statement>"
   :using [:<dep-id> ...]
   :justification <keyword>
   :context {:symbols {...}
             :assumptions [...]
             :relevant-nodes [...]}}
  
  Example:
    {:step :2-a1b2c3
     :claim "The sum is bounded by $n^2$"
     :using [:1-d4e5f6 :1-e7f8a9]
     :justification :algebraic-rewrite
     :context {:symbols {:n {:type "ℕ" :constraint "n ≥ 1"}}
               :assumptions ["$n \\geq 1$"]
               :relevant-nodes [{:id :1-d4e5f6 :statement "..."}]}}

Output (example for 'verifier-output'):
  Verifier Output Schema (expected from Verifier subagent)
  
  {:step :<node-id>
   :verdict :accept | :challenge | :reject
   :reason "<string>"           ; required for challenge/reject
   :suggested-check "<string>"  ; optional, for challenge
   :confidence <float>}         ; optional, 0.0-1.0
  
  Example:
    {:step :2-a1b2c3
     :verdict :challenge
     :reason "The bound n^2 is not justified; need to show sum ≤ n^2"
     :suggested-check "Expand the induction step explicitly"
     :confidence 0.7}
```

---

### 3.5 fsm transition (Enhanced)

Phase transitions now emit instructions for the new phase.

```
alethfeld fsm transition <graph-file> <target-phase> [--reason <text>]

Output (success, v2.3 enhanced):
  {:ok true
   :from :skeleton
   :to :skeleton-review
   :version 15
   :instructions "
## Entering Phase: skeleton-review

### Your Task
Have Adviser review the skeleton before expansion.

### Steps
1. Get skeleton nodes:
   ```bash
   alethfeld show graph.edn pending
   ```

2. SPAWN Adviser:
   ```clojure
   {:request :review-skeleton
    :theorem \"<theorem statement>\"
    :skeleton <depth-1-nodes>}
   ```

3. Parse response → {:verdict :weaknesses}

4. Record result:
   ```bash
   echo '<result>' | alethfeld fsm record graph.edn skeleton-review --stdin
   ```

5. Transition based on verdict:
   - :promising or :risky → decomposition
   - :flawed (retries left) → skeleton
   - :doomed or limit reached → escalated

### Valid Next Transitions
- decomposition (if verdict promising/risky)
- skeleton (if verdict flawed, iterations < 5)
- escalated (if verdict doomed or iterations >= 5)
"}
```

**Instructions are phase-specific and generated from current state.**

---

## 4. Minimal Orchestrator Prompt

With context emission, the orchestrator prompt shrinks to ~3KB:

```markdown
# Alethfeld Orchestrator

You drive proof verification using the `alethfeld` CLI. The CLI manages all state and provides guidance.

## Core Principles
- Graph is canonical truth (never modify directly)
- CLI enforces valid transitions
- Detection over sycophancy: finding errors is success
- Triple-verifier with precedence: reject > challenge > accept
- Checkpoint before risky operations

## Main Loop
```bash
# See current task and available actions
alethfeld context graph.edn

# See suggested next action
alethfeld next graph.edn

# Get command syntax when needed
alethfeld help <command>

# Get schema for subagent I/O
alethfeld schema <type>
```

## Subagent Spawning
You spawn subagents (Adviser, Prover, Verifier) as separate conversations.
- Get input format: `alethfeld schema <type>-input`
- Get output format: `alethfeld schema <type>-output`

## Verifier Stance (CRITICAL)
When spawning Verifiers, each must ask before accepting:
1. Could the theorem itself be false?
2. Is prover explaining away a contradiction?
3. Did prover find ONE solution or ALL solutions?
4. Are domain restrictions justified?
5. Is optimization truly exhaustive?

## Error Handling
- Invalid subagent output: Retry up to 3 times with clarification
- FSM blocked: Check `result.blockers` for what's missing
- Verification deadlock: Checkpoint and spawn Adviser for diagnosis

## Begin
```bash
alethfeld context graph.edn
```
Follow the instructions provided.
```

---

## 5. Context Templates by Phase

### 5.1 Template: init

```markdown
## Current Phase: init

### Your Task
Graph initialized. Transition to theorem-audit to begin.

### Command
```bash
alethfeld fsm transition graph.edn theorem-audit
```
```

### 5.2 Template: theorem-audit

```markdown
## Current Phase: theorem-audit

### Your Task
Sanity-check the theorem before investing effort.

### Steps
1. SPAWN Adviser:
   ```clojure
   {:request :theorem-audit
    :theorem "<THEOREM_STATEMENT>"
    :source <SOURCE>}
   ```

2. Parse response → {:plausibility :recommendation :concerns}

3. Record result:
   ```bash
   echo '<result>' | alethfeld fsm record graph.edn audit --stdin
   ```

4. Transition:
   - recommendation :proceed or :verify-first → strategy
   - recommendation :refuse or :suspicious → escalated

### Adviser Output Schema
```clojure
{:plausibility :high | :medium | :low | :suspicious
 :concerns ["..." ...]
 :recommendation :proceed | :verify-first | :refuse}
```
```

### 5.3 Template: strategy

```markdown
## Current Phase: strategy

### Your Task
Evaluate proof approach before committing.

### Iteration Count
Strategy attempts: <N>/<LIMIT>

### Steps
1. SPAWN Adviser:
   ```clojure
   {:request :evaluate-strategy
    :theorem "<THEOREM>"
    :proposed-approach "<DESCRIPTION>"}
   ```

2. Parse response → {:verdict :assessment :suggestions}

3. Record result:
   ```bash
   echo '<result>' | alethfeld fsm record graph.edn strategy --stdin
   ```

4. Transition:
   - verdict :promising or :risky → skeleton
   - verdict :flawed (retries left) → stay, try new approach
   - verdict :doomed or limit reached → escalated

### Adviser Output Schema
```clojure
{:verdict :promising | :risky | :flawed | :doomed
 :assessment "..."
 :suggestions [{:type <kw> :description "..."}]
 :confidence <float>}
```
```

### 5.4 Template: skeleton

```markdown
## Current Phase: skeleton

### Your Task
Establish top-level proof structure.

### Steps
1. SPAWN Prover:
   ```clojure
   {:request :skeleton
    :theorem "<THEOREM>"
    :adviser-suggestions <SUGGESTIONS>}
   ```

2. Parse response → {:steps [...]}

3. For each step, add node:
   ```bash
   echo '<node-edn>' | alethfeld add-node graph.edn --stdin
   ```

4. Transition:
   ```bash
   alethfeld fsm transition graph.edn skeleton-review
   ```

### Prover Output Schema
```clojure
{:steps
 [{:type :claim | :external-ref | ...
   :claim "LaTeX statement"
   :using [:<dep-id> ...]
   :justification <keyword>
   :substeps [...]}]}  ; substeps for nested structure
```

### Transform Prover Step to Node
```clojure
;; Prover:
{:claim "P" :using [:0-a1b2c3] :justification :modus-ponens}

;; Node EDN:
{:type :claim
 :statement "P"
 :dependencies #{:0-a1b2c3}
 :justification :modus-ponens}
```
```

### 5.5 Template: skeleton-review

```markdown
## Current Phase: skeleton-review

### Your Task
Have Adviser validate skeleton before expansion.

### Skeleton Nodes
<LIST_OF_DEPTH_1_NODES>

### Steps
1. SPAWN Adviser:
   ```clojure
   {:request :review-skeleton
    :theorem "<THEOREM>"
    :skeleton <SKELETON_NODES>}
   ```

2. Parse response → {:verdict :weaknesses}

3. Record result:
   ```bash
   echo '<result>' | alethfeld fsm record graph.edn skeleton-review --stdin
   ```

4. Transition:
   - :promising or :risky → decomposition
   - :flawed (retries < <LIMIT>) → skeleton
   - :doomed or limit reached → escalated
```

### 5.6 Template: decomposition

```markdown
## Current Phase: decomposition

### Your Task
Split into independent subproblems BEFORE deep expansion.

### Precondition Check
All subgraphs must be :pending or :merged (none :in-progress).
Current: <SUBGRAPH_STATUS_LIST>

### Steps
1. Analyze for candidates:
   ```bash
   alethfeld subgraph analyze graph.edn --min-benefit 0.4
   ```

2. For each good candidate:
   ```bash
   # Check independence
   alethfeld subgraph check graph.edn --root <id> --nodes <ids>
   
   # MANDATORY: Checkpoint first
   alethfeld checkpoint save graph.edn pre-split-<id>
   
   # Split with checkpoint tag
   alethfeld subgraph split graph.edn \
       --root <id> --nodes <ids> \
       --output subgraph-<id>.edn \
       --checkpoint-tag pre-split-<id> \
       --assign-model <model>
   ```

3. Record analysis:
   ```bash
   echo '<analysis>' | alethfeld fsm record graph.edn decomposition --stdin
   ```

4. Transition:
   ```bash
   alethfeld fsm transition graph.edn expand-verify-loop
   ```

### Benefit Score Interpretation
- > 0.7: Excellent candidate
- 0.5-0.7: Good candidate
- 0.4-0.5: Marginal
- < 0.4: Not worth splitting
```

### 5.7 Template: expand-verify-loop

(See section 3.1 for full example)

### 5.8 Template: reference-check

```markdown
## Current Phase: reference-check

### Your Task
Verify all external references.

### External References
<LIST_OF_REFS_WITH_STATUS>

### Steps
1. Get references:
   ```bash
   alethfeld show graph.edn external-refs
   ```

2. For each :pending ref, SPAWN Reference-Checker:
   ```clojure
   {:references [{:id :<ref-id> :doi "..." :claimed-statement "..."}]}
   ```

3. Update each ref:
   ```bash
   echo '<update>' | alethfeld external-ref update graph.edn <ref-id> --stdin
   ```

4. Transition:
   - All verified, none mismatch → finalization
   - Any mismatch → expand-verify-loop (nodes auto-rejected)

### Reference Update Schema
```clojure
{:verification-status :verified | :mismatch | :not-found | :metadata-only
 :found-statement "<actual statement>"|nil
 :bibdata {:authors [...] :title "..." :year <int>}|nil}
```
```

### 5.9 Template: finalization

```markdown
## Current Phase: finalization

### Your Task
Final validation before completion.

### Finalization Checklist
- [ ] Validation passed: <VALIDATION_STATUS>
- [ ] Lint passed: <LINT_STATUS>
- [ ] Exports generated: <EXPORT_LIST>

### Steps
1. Run validation:
   ```bash
   alethfeld validate graph.edn --strict
   ```

2. Run lint:
   ```bash
   alethfeld lint graph.edn --severity error
   ```

3. (Optional) Generate exports:
   ```bash
   alethfeld export lean-skeleton graph.edn --output proof.lean
   alethfeld export dot graph.edn --output proof.dot
   ```

4. Transition:
   ```bash
   alethfeld fsm transition graph.edn complete
   ```

### Completion Message
"Proof complete. Direct user to LaTeX-er and Leanifier prompts."

### Summary Output
```bash
alethfeld stats graph.edn --human
alethfeld show graph.edn obligations
```
```

---

## 6. Command Categories (Updated)

| Category | Commands |
|----------|----------|
| **Context (NEW)** | `context`, `next`, `help`, `schema` |
| **Initialization** | `init` |
| **Node Operations** | `add-node`, `update-status`, `replace-node`, `delete-node` |
| **Lemma Operations** | `extract-lemma` |
| **Reference Operations** | `external-ref add`, `external-ref update` |
| **Validation** | `validate`, `lint`, `recompute` |
| **Information** | `stats`, `show`, `diff` |
| **FSM** | `fsm status`, `fsm transition`, `fsm record`, `fsm queue`, `fsm history` |
| **Subgraph** | `subgraph analyze`, `subgraph check`, `subgraph split`, `subgraph merge`, `subgraph list`, `subgraph update-status`, `subgraph update-model` |
| **Checkpoint** | `checkpoint save`, `checkpoint restore`, `checkpoint list`, `checkpoint diff` |
| **Verification** | `verify record-vote`, `verify tally`, `verify reset` |
| **Export** | `export cytoscape`, `export dot`, `export lean-skeleton` |

---

## 7. Graph File Format

(Unchanged from v2.2 — see cli-requirements-v2.2.md section 3)

---

## 8-14. Existing Commands

(Unchanged from v2.2 — see cli-requirements-v2.2.md sections 5-14)

---

## 15. Exit Codes

| Code | Category | Description | Commands |
|------|----------|-------------|----------|
| 0 | Success | Operation completed | All |
| 1 | Validation | Schema/integrity error | validate, add-node, replace-node |
| 2 | IO | File not found | All |
| 3 | Parse | Invalid EDN | All with EDN input |
| 4 | FSM | Invalid phase transition | fsm transition, add-node |
| 5 | Precondition | Operation precondition failed | All mutating |
| 6 | Consistency | Subgraph/merge consistency failure | subgraph merge |

---

## 16. Configuration

### 16.1 Config File

Optional `~/.alethfeld/config.edn`:

```clojure
{:defaults
 {:proof-mode :strict-mathematics
  :output-format :edn
  :context-format :markdown}     ; v2.3: default format for context

 :limits
 {:strategy-attempts 2
  :skeleton-revisions 5
  :verification-rounds 50
  :expansion-per-step 5
  :verification-per-step 7}

 :context-budget
 {:max-tokens 80000
  :warning-threshold 0.7}

 :subgraph
 {:min-nodes 2
  :max-nodes 15
  :min-benefit 0.4}

 :weak-delegation
 {:depth-threshold 3
  :node-threshold 5
  :weak-model "claude-3-haiku"
  :strong-model "claude-sonnet-4-20250514"}

 :verifier-count 3

 :context-emission                ; v2.3
 {:include-schemas true
  :include-examples true
  :verbosity :normal}}           ; :minimal :normal :verbose
```

---

## 17. Implementation Notes

### 17.1 Context Template System

Templates are stored as EDN/Markdown files in the CLI distribution:

```
~/.alethfeld/templates/
  init.md
  theorem-audit.md
  strategy.md
  skeleton.md
  skeleton-review.md
  decomposition.md
  expand-verify-loop.md
  reference-check.md
  finalization.md
  complete.md
  escalated.md
```

Templates support interpolation:
- `<THEOREM_STATEMENT>` — from graph
- `<N>/<LIMIT>` — from iteration counts
- `<SUBGRAPH_STATUS_LIST>` — computed from graph
- `<LIST_OF_REFS_WITH_STATUS>` — computed from graph

### 17.2 Schema Storage

Schemas stored as Malli specs, rendered on demand:

```clojure
(def schemas
  {:node [:map
          [:type [:enum :assumption :claim ...]]
          [:statement :string]
          [:justification [:enum :modus-ponens ...]]]
   :verifier-input [:map ...]
   :verifier-output [:map ...]
   ...})

(defn render-schema [schema-key format]
  (case format
    :edn (malli/form (get schemas schema-key))
    :human (malli->human-readable (get schemas schema-key))))
```

### 17.3 Technology Stack

- **Language**: Clojure (for graph operations) + Babashka (for CLI wrapper)
- **Schema**: Malli for validation and schema rendering
- **Templates**: Selmer or simple string interpolation
- **Hashing**: SHA-256 for content hashes and node ID generation

---

## 18. Testing Requirements

### 18.1 Unit Tests

- Every command has positive and negative test cases
- Schema validation edge cases
- FSM transition matrix coverage
- Context emission for each phase

### 18.2 Integration Tests

1. Full workflow with minimal prompt using only `context`/`next`/`help`
2. Verify `context` output is sufficient for each phase
3. Verify `next` suggestions are optimal
4. Verify `help` covers all commands
5. Verify `schema` covers all subagent I/O

### 18.3 Context Emission Tests

For each phase:
1. `context` output contains all necessary information
2. `context` output contains valid commands
3. Interpolation produces correct values
4. Both markdown and EDN formats work

---

## Appendix A: FSM Transition Matrix

(Unchanged from v2.2)

---

## Appendix B: Example Session with Context Emission

```bash
# Start with context
$ alethfeld context graph.edn
## Current Phase: init

### Your Task
Graph initialized. Transition to theorem-audit to begin.

### Command
```bash
alethfeld fsm transition graph.edn theorem-audit
```

# Follow the instruction
$ alethfeld fsm transition graph.edn theorem-audit
{:ok true :from :init :to :theorem-audit :version 2
 :instructions "## Entering Phase: theorem-audit ..."}

# Get next suggestion
$ alethfeld next graph.edn
{:suggestion :spawn-adviser
 :reason "theorem-audit requires Adviser audit"
 :adviser-input {:request :theorem-audit
                 :theorem "For all n ≥ 1, sum = n(n+1)/2"
                 :source :textbook}}

# Get schema for Adviser output
$ alethfeld schema adviser-output
Adviser Output Schema...
{:plausibility :high|:medium|:low|:suspicious
 :concerns [...]
 :recommendation :proceed|:verify-first|:refuse}

# Record result after spawning Adviser
$ echo '{:plausibility :high :recommendation :proceed :concerns []}' | \
    alethfeld fsm record graph.edn audit --stdin
{:ok true :recorded :audit :enables-transitions [:strategy]}

# Continue...
$ alethfeld next graph.edn
{:suggestion :transition
 :reason "Audit recorded with :proceed recommendation"
 :command "alethfeld fsm transition graph.edn strategy"}
```

---

## Appendix C: Minimal Orchestrator Prompt (Complete)

```markdown
# Alethfeld Orchestrator

You drive proof verification using the `alethfeld` CLI.

## Principles
- Graph is canonical truth
- CLI enforces valid transitions
- Detection over sycophancy
- Triple-verifier: reject > challenge > accept
- Checkpoint before risk

## Loop
```bash
alethfeld context graph.edn  # See current task
alethfeld next graph.edn     # Get suggestion
alethfeld help <cmd>         # Get syntax
alethfeld schema <type>      # Get I/O format
```

## Subagents
Spawn Adviser, Prover, Verifier as separate conversations.
Use `alethfeld schema <type>-input` and `<type>-output` for formats.

## Verifier Questions (CRITICAL)
Before accepting, each verifier must ask:
1. Could the theorem be false?
2. Is prover explaining away a contradiction?
3. ONE solution or ALL solutions?
4. Domain restrictions justified?
5. Optimization exhaustive?

## Begin
```bash
alethfeld context graph.edn
```
```

---

*End of CLI Requirements Specification v2.3*
