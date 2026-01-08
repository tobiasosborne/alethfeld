# Alethfeld CLI: Comprehensive Guide

This document provides complete documentation of the `alethfeld` CLI tool, including architecture, design principles, module structure, and usage.

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Module Design](#module-design)
4. [Data Flow](#data-flow)
5. [Command Reference](#command-reference)
6. [Workflows](#workflows)
7. [Extending the CLI](#extending-the-cli)

---

## Overview

The Alethfeld CLI is a Clojure-based command-line tool for manipulating semantic proof graphs. It provides atomic, validated operations that maintain graph invariants (referential integrity, acyclicity, scope validity, taint propagation).

### Design Principles

1. **Immutable Graphs**: All operations take a graph and return a new graph. The original is never mutated.

2. **Atomic Writes**: File writes use temp-file-then-rename to prevent corruption.

3. **Result Types**: All operations return `{:ok data}` or `{:error errors}`, enabling composable error handling.

4. **Separation of Concerns**:
   - `ops/` modules contain pure business logic
   - `commands/` modules handle CLI parsing and I/O
   - `schema/` modules define data validation
   - `graph.clj` provides query functions

5. **Fail-Fast Validation**: Operations validate preconditions before making changes.

### Installation

```bash
cd cli

# Recommended: Use pre-built wrapper (fast startup)
./scripts/alethfeld <command> [options]

# Alternative: Build uberjar
clojure -T:build uber
java -jar target/alethfeld.jar <command> [options]

# Development (slower startup)
clojure -M:run <command> [options]
```

---

## Architecture

### Layer Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                         CLI Layer                            │
│  core.clj - Entry point, command dispatch                   │
│  commands/*.clj - Parse args, format output                 │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                     Operations Layer                         │
│  ops/*.clj - Business logic, precondition checks            │
│  Returns: {:ok new-graph} or {:error errors}                │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      Query Layer                             │
│  graph.clj - DAG traversal, taint computation, scope        │
│  validators.clj - Semantic validation                       │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                     Schema Layer                             │
│  schema/*.clj - Malli schemas for all data types            │
│  Primitives, Enums, Node, Graph, Verification               │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                       I/O Layer                              │
│  io.clj - EDN reading/writing, atomic file operations       │
│  config.clj - Constants, ID generation, timestamps          │
└─────────────────────────────────────────────────────────────┘
```

### Project Structure

```
cli/
├── src/alethfeld/
│   ├── core.clj              # CLI entry point, command registry
│   ├── schema.clj            # Main schema (re-exports submodules)
│   ├── schema/               # Domain-grouped schemas
│   │   ├── primitives.clj    # NodeId, ContentHash, ISO8601, LaTeXString
│   │   ├── enums.clj         # NodeType, Justification, NodeStatus, etc.
│   │   ├── node.clj          # Node, NodePartial, Provenance
│   │   ├── graph.clj         # SemanticGraph, Symbol, ExternalRef, Lemma
│   │   └── verification.clj  # VerificationLog and related
│   ├── validators.clj        # Semantic validation (integrity, cycles, scope)
│   ├── graph.clj             # Pure query functions (ancestors, descendants)
│   ├── io.clj                # EDN I/O with atomic writes
│   ├── config.clj            # Configuration, ID generation
│   ├── result.clj            # Result type utilities (ok, err, let-ok)
│   ├── ops/                  # Pure operations (business logic)
│   │   ├── init.clj          # Create new graph
│   │   ├── add_node.clj      # Add node with validation
│   │   ├── update_status.clj # Change node status, propagate taint
│   │   ├── delete_node.clj   # Archive leaf nodes
│   │   ├── replace_node.clj  # Replace rejected with revision
│   │   ├── extract_lemma.clj # Extract verified subgraph
│   │   └── external_ref.clj  # Manage citations
│   └── commands/             # CLI commands (I/O + formatting)
│       ├── init.clj
│       ├── add_node.clj
│       ├── update_status.clj
│       ├── delete_node.clj
│       ├── replace_node.clj
│       ├── extract_lemma.clj
│       ├── external_ref.clj
│       ├── validate.clj
│       ├── stats.clj
│       ├── recompute.clj
│       └── convert.clj
├── test/alethfeld/           # Tests mirror src structure
├── bench/alethfeld/          # Performance benchmarks
└── deps.edn                  # Dependencies and aliases
```

---

## Module Design

### Core Entry Point (`core.clj`)

The CLI uses a registry-based command dispatch:

```clojure
(def commands
  {"validate"      {:fn validate/run :desc "..." :options validate/cli-options}
   "add-node"      {:fn add-node/run :desc "..." :options add-node/cli-options}
   ...})

(defn -main [& args]
  (let [{:keys [options arguments]} (parse-opts args global-options :in-order true)]
    (cond
      (:help options) (println (global-usage))
      :else
      (let [cmd-name (first arguments)
            cmd-info (get commands cmd-name)]
        (let [result ((:fn cmd-info) (rest arguments) parsed-options)]
          (System/exit (:exit-code result)))))))
```

**Key design choices:**
- Commands are pure functions returning `{:exit-code N :message S}`
- Global options parsed first, then command-specific options
- Unknown commands produce helpful error messages

### Operations Layer (`ops/*.clj`)

Operations are pure functions with this signature:

```clojure
(defn operation-name
  "Docstring explaining preconditions and effects."
  [graph & args]
  ;; 1. Validate preconditions
  (if-let [errors (validate-preconditions graph args)]
    {:error errors}
    ;; 2. Perform operation
    (let [new-graph (transform graph args)]
      {:ok new-graph})))
```

**Example: `add-node`**

```clojure
(defn add-node [graph node]
  ;; Schema validation
  (let [schema-result (schema/validate-partial-node node)]
    (if (not (:valid schema-result))
      {:error [{:type :schema-validation :errors (:errors schema-result)}]}
      ;; Semantic preconditions
      (if-let [errors (validate-preconditions graph node)]
        {:error errors}
        ;; Success: complete node and add
        (let [completed (complete-node graph node)
              new-graph (-> graph
                            (assoc-in [:nodes (:id node)] completed)
                            (graph/increment-version)
                            (graph/update-last-modified))]
          {:ok new-graph}))))))
```

**Preconditions checked by `add-node`:**
- ID must be unique
- All dependencies must exist
- Scope must be valid (subset of in-scope local-assumes)
- No cycles created
- Type-specific fields present (e.g., `:introduces` for `:local-assume`)

### Result Type (`result.clj`)

All operations use a consistent result type:

```clojure
;; Constructors
(ok value)      ; => {:ok value}
(err errors)    ; => {:error errors}

;; Predicates
(ok? result)    ; => true if {:ok ...}
(err? result)   ; => true if {:error ...}

;; Monadic binding (short-circuits on error)
(let-ok [graph (io/read-graph path)
         node  (io/read-edn node-path)
         result (ops/add-node graph node)]
  (io/write-graph path result))
```

**Exit codes:**
- `0` - Success
- `1` - Operation failed (logic error, precondition violation)
- `2` - Input error (file not found, parse error)

### Graph Queries (`graph.clj`)

Pure query functions for DAG operations:

```clojure
;; Traversal
(get-ancestors graph node-id)     ; All transitive dependencies
(get-descendants graph node-id)   ; All nodes depending on this one
(topological-sort graph)          ; Nodes in dependency order

;; Scope
(compute-valid-scope graph node-id)  ; Valid local-assumes for a node
(compute-all-scopes graph)           ; Batch computation for all nodes

;; Taint
(compute-taint graph node-id)        ; Expected taint based on deps
(recompute-all-taints graph)         ; Update all taint values
```

**Performance notes:**
- `get-ancestors`: O(n) with iterative DFS
- `topological-sort`: O(n²) full, O(k) partial (where k = closure size)
- `compute-all-scopes`: O(n²), uses batched ancestor computation

### Schema System (`schema/*.clj`)

Schemas are organized by domain:

| Module | Contents |
|--------|----------|
| `primitives.clj` | `NodeId`, `ContentHash`, `ISO8601`, `LaTeXString` |
| `enums.clj` | `NodeType`, `Justification`, `NodeStatus`, `TaintStatus`, etc. |
| `node.clj` | `Provenance`, `Node`, `NodePartial` |
| `graph.clj` | `SemanticGraph`, `Symbol`, `ExternalRef`, `Lemma`, `Metadata` |
| `verification.clj` | `VerificationLog`, `VerificationResult`, etc. |

The main `schema.clj` re-exports all schemas for backward compatibility:

```clojure
(ns alethfeld.schema
  (:require [alethfeld.schema.primitives :as primitives]
            [alethfeld.schema.enums :as enums]
            ...))

(def Node node/Node)
(def SemanticGraph graph/SemanticGraph)

(defn validate-schema [graph]
  (if (m/validate SemanticGraph graph)
    {:valid true}
    {:valid false :errors (me/humanize (m/explain SemanticGraph graph))}))
```

---

## Data Flow

### Adding a Node

```
┌──────────┐    ┌─────────────┐    ┌────────────┐    ┌────────────┐
│  CLI     │───▶│  Command    │───▶│  Operation │───▶│  I/O       │
│  args    │    │  Parse      │    │  Logic     │    │  Write     │
└──────────┘    └─────────────┘    └────────────┘    └────────────┘
     │                │                   │                │
     ▼                ▼                   ▼                ▼
  graph.edn     {:ok node}         {:ok new-graph}    graph.edn
  node.edn      from stdin         with node added    (atomic)
```

**Step by step:**

1. **CLI Layer** (`core.clj`): Parse global options, dispatch to `add-node` command
2. **Command Layer** (`commands/add_node.clj`):
   - Read graph from file
   - Read node from file or stdin
   - Call operation
   - Format result and write back
3. **Operation Layer** (`ops/add_node.clj`):
   - Validate node against `NodePartial` schema
   - Check preconditions (unique ID, deps exist, no cycles)
   - Complete node (compute hash, set taint, add provenance)
   - Return new graph
4. **I/O Layer** (`io.clj`): Atomic write to file

### Taint Propagation

When a node's status changes:

```
Status Change → Compute Self-Taint → Propagate to Descendants
                     │
        ┌────────────┼────────────┐
        ▼            ▼            ▼
   :admitted    :rejected    :verified
        │            │            │
        ▼            ▼            ▼
  :self-admitted  :tainted    :clean (if deps clean)
```

```clojure
(defn compute-taint [graph node-id]
  (let [node (get-node graph node-id)
        status (:status node)]
    (cond
      (= :admitted status) :self-admitted
      (= :rejected status) :tainted
      :else
      (let [dep-taints (map #(get-in graph [:nodes % :taint]) (:dependencies node))]
        (if (some #{:tainted :self-admitted} dep-taints)
          :tainted
          :clean)))))
```

---

## Command Reference

### Global Options

| Option | Description |
|--------|-------------|
| `-h, --help` | Show help message |
| `-V, --version` | Show version (0.1.0) |

### Commands

#### `init` - Create New Graph

```bash
cli init [options] <output.edn>
```

| Option | Description | Default |
|--------|-------------|---------|
| `-t, --theorem STMT` | Theorem statement (required) | - |
| `-m, --mode MODE` | Proof mode | `strict-mathematics` |
| `-g, --graph-id ID` | Custom graph ID | auto-generated |
| `-T, --max-tokens N` | Context budget | 100000 |

**Proof modes:** `strict-mathematics`, `formal-physics`, `algebraic-derivation`

**Example:**
```bash
./scripts/alethfeld init proof.edn -t "For all \$n\$, \$n^2 \\geq 0\""
```

#### `validate` - Check Graph Integrity

```bash
cli validate [options] <graph.edn>
```

| Option | Description |
|--------|-------------|
| `-v, --verbose` | Detailed errors |
| `-q, --quiet` | Exit code only |
| `-s, --schema-only` | Skip semantic checks |

**Validation includes:**
- Schema validation (Malli)
- Referential integrity (all refs exist)
- Acyclicity (no dependency cycles)
- Scope validity (local-assumes in scope)
- Taint correctness (propagation matches status)

#### `add-node` - Add Node to Graph

```bash
cli add-node [options] <graph.edn> [node.edn]
cli add-node --stdin [options] <graph.edn>
```

| Option | Description |
|--------|-------------|
| `-s, --stdin` | Read node from stdin |
| `-d, --dry-run` | Validate only |
| `-o, --output FILE` | Write to different file |

**Node format:**
```clojure
{:id :1-abc123
 :type :claim
 :statement "For all $\\varepsilon > 0$..."
 :dependencies #{:A1 :1-def456}
 :scope #{}
 :justification :modus-ponens
 :depth 1
 :display-order 5}
```

**Node types:** `:assumption`, `:local-assume`, `:local-discharge`, `:definition`, `:claim`, `:lemma-ref`, `:external-ref`, `:qed`

**Justifications:** `:assumption`, `:modus-ponens`, `:universal-elim`, `:universal-intro`, `:existential-intro`, `:existential-elim`, `:equality-rewrite`, `:algebraic-rewrite`, `:case-split`, `:induction-base`, `:induction-step`, `:contradiction`, `:conjunction-intro`, `:conjunction-elim`, `:disjunction-intro`, `:disjunction-elim`, `:implication-intro`, `:lemma-application`, `:external-application`, `:admitted`, `:qed`

#### `update-status` - Change Node Status

```bash
cli update-status [options] <graph.edn> <node-id> <status>
```

**Statuses:** `proposed`, `verified`, `admitted`, `rejected`

| Option | Description |
|--------|-------------|
| `-d, --dry-run` | Validate only |
| `-o, --output FILE` | Write to different file |

**Effects:**
- Updates node status
- Recomputes taint for node and all descendants
- If `admitted`, marks taint as `:self-admitted`

#### `replace-node` - Replace Rejected Node

```bash
cli replace-node [options] <graph.edn> <old-id> <new-node.edn>
```

**Preconditions:**
- Old node must have status `:rejected`

**Effects:**
- Archives old node
- Adds new node with `:revision-of` in provenance
- Rewrites all dependencies from old to new

#### `delete-node` - Archive Node

```bash
cli delete-node [options] <graph.edn> <node-id>
```

**Preconditions:**
- Node must exist
- No other nodes may depend on it

**Effects:**
- Moves node to `:archived-nodes`

#### `extract-lemma` - Extract Verified Subgraph

```bash
cli extract-lemma [options] <graph.edn> <root-node-id>
```

| Option | Description |
|--------|-------------|
| `-n, --name NAME` | Lemma name (required) |
| `-N, --nodes IDS` | Explicit nodes (comma-separated) |
| `-d, --dry-run` | Validate only |
| `-o, --output FILE` | Write to different file |

**Independence criteria:**
1. Root is in node set
2. All nodes have status `:verified` (or `:admitted` for tainted lemma)
3. Only root has external dependents
4. Scope is balanced (local-assume/discharge pairs)

**Effects:**
- Creates lemma record in `:lemmas`
- Creates `:lemma-ref` node replacing root
- Archives extracted nodes
- Rewrites external dependencies

#### `external-ref` - Manage Citations

**Add reference:**
```bash
cli external-ref --add [options] <graph.edn> [ref.edn]
```

**Update after verification:**
```bash
cli external-ref --update <ref-id> [options] <graph.edn> [result.edn]
```

**Reference format:**
```clojure
{:doi "10.1234/example"
 :arxiv "2301.12345"
 :claimed-statement "The theorem states..."}
```

**Verification result:**
```clojure
{:status :verified  ; or :mismatch, :not-found, :metadata-only
 :verified-statement "Actual text..."
 :bibdata {:authors ["Author"] :title "Title" :year 2024}}
```

#### `stats` - Display Statistics

```bash
cli stats [options] <graph.edn>
```

| Option | Description |
|--------|-------------|
| `-j, --json` | Output as JSON |
| `-q, --quiet` | Minimal output |

**Output includes:**
- Node counts by type and status
- Taint summary
- Dependency statistics
- Context budget usage

#### `recompute` - Fix Taint Values

```bash
cli recompute [options] <graph.edn>
```

Traverses nodes in topological order and recomputes all taint values. Use after manual edits.

#### `convert` - Migrate Legacy Format

```bash
cli convert <input.edn> <output.edn>
```

Converts older proof formats to the current v4 schema.

---

## Workflows

### Complete Proof Development Cycle

```bash
# 1. Initialize
./scripts/alethfeld init proof.edn -t "Theorem statement"

# 2. Add assumptions (from orchestrator)
echo '{:id :A1 :type :assumption ...}' | cli add-node --stdin proof.edn

# 3. Prover adds steps
cli add-node proof.edn step1.edn

# 4. Verifier accepts/rejects
cli update-status proof.edn :1-abc123 verified
# OR
cli update-status proof.edn :1-abc123 rejected

# 5. If rejected, prover revises
cli replace-node proof.edn :1-abc123 step1-revised.edn

# 6. Extract verified subgraphs as lemmas
cli extract-lemma proof.edn :2-qed456 -n "Main Result"

# 7. Validate final graph
cli validate proof.edn -v

# 8. Get statistics
cli stats proof.edn
```

### Piping with AI Agents

```bash
# Agent generates node, CLI validates and adds
python prover_agent.py | cli add-node --stdin proof.edn

# Check validation
if cli validate proof.edn -q; then
    echo "Valid"
else
    echo "Invalid"
    cli validate proof.edn -v
fi
```

---

## Extending the CLI

### Adding a New Command

1. **Create operation** (`ops/my_operation.clj`):
```clojure
(ns alethfeld.ops.my-operation
  (:require [alethfeld.graph :as graph]))

(defn my-operation [graph & args]
  ;; Validate preconditions
  ;; Transform graph
  {:ok new-graph})
```

2. **Create command** (`commands/my_operation.clj`):
```clojure
(ns alethfeld.commands.my-operation
  (:require [alethfeld.io :as io]
            [alethfeld.ops.my-operation :as op]))

(def cli-options
  [["-d" "--dry-run" "Validate only"]
   ["-h" "--help" "Show help"]])

(defn usage [])

(defn run [args options]
  (cond
    (:help options) {:exit-code 0 :message (usage)}
    :else
    (let [result (op/my-operation ...)]
      (if (:ok result)
        {:exit-code 0 :message "Success"}
        {:exit-code 1 :message (format-errors (:error result))}))))))
```

3. **Register in `core.clj`**:
```clojure
(def commands
  {...
   "my-operation" {:fn my-operation/run
                   :desc "Description"
                   :options my-operation/cli-options}})
```

4. **Add tests** (`test/alethfeld/ops/my_operation_test.clj`)

### Adding a New Schema Type

1. **Add to appropriate schema module** (`schema/enums.clj`, etc.)
2. **Re-export from `schema.clj`** if needed externally
3. **Run tests**: `clojure -M:test`

---

## Performance

See [PERFORMANCE.md](PERFORMANCE.md) for detailed benchmarks.

**Key metrics (500-node graph):**
| Operation | Time |
|-----------|------|
| `get-ancestors` | 243 us |
| `topological-sort` (full) | 50 ms |
| `topological-sort` (partial) | 129 ns |
| `validate-schema` | 747 us |
| `validate-semantics` | 219 ms |

**Startup time:**
- Uberjar: ~1.1s
- Clojure CLI: ~3.3s

---

## Error Reference

| Error Type | Exit Code | Meaning |
|------------|-----------|---------|
| `:duplicate-id` | 1 | Node ID already exists |
| `:missing-dependency` | 1 | Referenced node doesn't exist |
| `:invalid-scope` | 1 | Scope contains invalid entries |
| `:would-create-cycle` | 1 | Operation would create cycle |
| `:not-verified` | 1 | Node not verified (extraction) |
| `:has-dependents` | 1 | Node has dependents (deletion) |
| `:not-rejected` | 1 | Node not rejected (replacement) |
| `:schema-validation` | 1 | Malli schema failed |
| File not found | 2 | Input file doesn't exist |
| Parse error | 2 | Invalid EDN syntax |