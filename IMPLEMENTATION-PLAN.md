# Alethfeld CLI Implementation Plan

**Goal**: Build a complete Clojure CLI tool for semantic proof graph operations, extending the existing `validate-graph` tool into a unified `alethfeld` CLI.

**Constraints**: Each phase should be completable in 20-40% of Claude Code context (~30-60k tokens of work).

**Testing Philosophy**: Every function has unit tests. Every command has integration tests. Edge cases are first-class citizens.

---

## Architecture Overview

```
alethfeld/
├── deps.edn
├── src/alethfeld/
│   ├── core.clj              # CLI entry point, command dispatch
│   ├── schema.clj            # Malli schemas (from validate-graph)
│   ├── validators.clj        # Validation logic (from validate-graph)
│   ├── config.clj            # Constants, defaults (from validate-graph)
│   ├── io.clj                # EDN read/write, atomic file ops
│   ├── graph.clj             # Pure graph query functions
│   ├── ops/
│   │   ├── add_node.clj      # AddNode operation
│   │   ├── update_status.clj # UpdateNodeStatus operation
│   │   ├── replace_node.clj  # ReplaceNode operation
│   │   ├── delete_node.clj   # DeleteNode operation
│   │   ├── extract_lemma.clj # ExtractLemma operation
│   │   ├── external_ref.clj  # Add/Update external refs
│   │   └── init.clj          # Initialize new graph
│   └── commands/
│       ├── validate.clj      # validate command
│       ├── add_node.clj      # add-node command
│       ├── update_status.clj # update-status command
│       ├── replace_node.clj  # replace-node command
│       ├── delete_node.clj   # delete-node command
│       ├── extract_lemma.clj # extract-lemma command
│       ├── external_ref.clj  # external-ref command
│       ├── init.clj          # init command
│       ├── stats.clj         # stats command
│       └── recompute.clj     # recompute-taint command
├── test/alethfeld/
│   ├── fixtures.clj          # Shared test fixtures
│   ├── schema_test.clj
│   ├── validators_test.clj
│   ├── io_test.clj
│   ├── graph_test.clj
│   ├── ops/
│   │   ├── add_node_test.clj
│   │   ├── update_status_test.clj
│   │   ├── replace_node_test.clj
│   │   ├── delete_node_test.clj
│   │   ├── extract_lemma_test.clj
│   │   ├── external_ref_test.clj
│   │   └── init_test.clj
│   └── integration/
│       ├── cli_test.clj      # Full CLI integration tests
│       └── workflow_test.clj # Multi-command workflow tests
└── resources/
    └── test-fixtures/        # EDN files for integration tests
```

---

## Phase 1: Project Restructure & Core Infrastructure
**Estimated effort**: 25% context
**Deliverables**: New project structure, IO module, migrated validate-graph code

### 1.1 Create new project structure

**Task**: Set up `alethfeld/` as a new Clojure project, copying and reorganizing code from `scripts/validate-graph/`.

```bash
mkdir -p alethfeld/src/alethfeld/{ops,commands}
mkdir -p alethfeld/test/alethfeld/{ops,integration}
mkdir -p alethfeld/resources/test-fixtures
```

**deps.edn**:
```clojure
{:paths ["src" "resources"]
 :deps {org.clojure/clojure {:mvn/version "1.12.0"}
        metosin/malli {:mvn/version "0.16.4"}
        org.clojure/tools.cli {:mvn/version "1.1.230"}
        org.clojure/data.json {:mvn/version "2.5.0"}}
 :aliases
 {:test {:extra-paths ["test"]
         :extra-deps {io.github.cognitect-labs/test-runner
                      {:git/tag "v0.5.1" :git/sha "dfb30dd"}}
         :main-opts ["-m" "cognitect.test-runner"]}
  :run {:main-opts ["-m" "alethfeld.core"]}}}
```

### 1.2 Implement io.clj

**Purpose**: Centralized EDN I/O with atomic writes.

```clojure
(ns alethfeld.io
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]))

(defn read-graph [path] ...)        ; Returns {:ok graph} or {:error msg}
(defn write-graph [path graph] ...) ; Atomic write (temp + rename)
(defn read-node-edn [path] ...)     ; For add-node input
(defn format-edn [data] ...)        ; Pretty-print EDN string
```

**Tests (io_test.clj)**:
- Read valid EDN file
- Read missing file → error
- Read malformed EDN → error
- Read empty file → error
- Write and read back preserves data
- Atomic write doesn't corrupt on failure (simulate with mock)
- Unicode in statements preserved

### 1.3 Migrate schema.clj and validators.clj

**Task**: Copy from `validate-graph`, update namespace to `alethfeld.*`.

**Changes**:
- Namespace rename
- Add `NodePartial` schema for add-node input (fewer required fields)
- Export individual validator functions for use in ops

### 1.4 Implement graph.clj (pure query functions)

**Purpose**: Stateless functions for querying graph structure.

```clojure
(ns alethfeld.graph)

;; Node queries
(defn node-ids [graph] ...)
(defn get-node [graph id] ...)
(defn nodes-of-type [graph type] ...)

;; Dependency graph queries
(defn get-ancestors [graph node-id] ...)
(defn get-descendants [graph node-id] ...)
(defn get-direct-dependents [graph node-id] ...)
(defn topological-sort [graph node-ids] ...)

;; Scope queries
(defn compute-valid-scope [graph node-id] ...)
(defn active-assumptions [graph node-id] ...)

;; Taint queries
(defn compute-taint [graph node-id] ...)
(defn tainted-nodes [graph] ...)

;; Independence check (for lemma extraction)
(defn check-independence [graph root-id node-ids] ...)

;; Token estimation
(defn estimate-tokens [node] ...)
(defn graph-token-estimate [graph] ...)
```

**Tests (graph_test.clj)**:
- `get-ancestors`: linear chain, diamond, disconnected
- `get-descendants`: same structures
- `compute-valid-scope`: with/without discharges
- `compute-taint`: clean, self-admitted, propagated
- `check-independence`: valid extraction, various failures
- `topological-sort`: various DAG shapes
- `estimate-tokens`: sanity checks

### 1.5 Create minimal CLI skeleton

**Task**: `core.clj` with subcommand dispatch, only `validate` working.

```clojure
(ns alethfeld.core
  (:require [clojure.tools.cli :refer [parse-opts]]
            [alethfeld.commands.validate :as validate])
  (:gen-class))

(def commands
  {"validate" validate/run
   ;; others added in later phases
   })

(defn -main [& args] ...)
```

**Integration test**: `clojure -M:run validate test.edn` works.

---

## Phase 2: Core Operations (add-node, update-status, delete-node)
**Estimated effort**: 35% context
**Deliverables**: Three mutation operations with full test coverage

### 2.1 Implement ops/add_node.clj

**Spec**:
```clojure
(defn add-node
  "Add a node to the graph.
   Input node must have: :id, :type, :statement, :dependencies, :scope,
                         :justification, :depth, :parent, :display-order
   Computed fields: :content-hash, :taint, :status (defaults to :proposed)
   Returns {:ok new-graph} or {:error message}"
  [graph node]
  ...)

(defn generate-node-id
  "Generate a new node ID with format :<depth>-<6-hex>"
  [depth]
  ...)
```

**Preconditions**:
1. Node ID doesn't already exist
2. All dependencies exist in graph
3. Scope is subset of valid scope
4. Adding node doesn't create cycle
5. Node type matches required fields (e.g., :local-assume needs :introduces)

**Postconditions**:
1. Node added to `:nodes`
2. `:version` incremented
3. `:metadata/last-modified` updated
4. `:metadata/context-budget/current-estimate` updated
5. `:content-hash` computed
6. `:taint` computed
7. `:provenance/created-at` set if not provided

**Tests (ops/add_node_test.clj)**:
- Add node to empty graph
- Add node with dependencies
- Add node with scope
- Reject duplicate ID
- Reject missing dependency
- Reject invalid scope entry
- Reject cycle creation (self-loop, would-close-cycle)
- Add each node type (:assumption, :claim, :local-assume, etc.)
- Content hash computed correctly
- Taint computed correctly (clean deps → clean, tainted dep → tainted)
- Version incremented
- Token estimate updated
- Provenance filled in

### 2.2 Implement ops/update_status.clj

**Spec**:
```clojure
(defn update-status
  "Update a node's verification status.
   Recomputes taint for node and all dependents.
   If status is :admitted, adds to :obligations.
   Returns {:ok new-graph} or {:error message}"
  [graph node-id new-status]
  ...)
```

**Postconditions**:
1. Node status updated
2. Taint recomputed for node and all transitive dependents
3. If :admitted, obligation added
4. Version incremented

**Tests (ops/update_status_test.clj)**:
- Update proposed → verified
- Update proposed → rejected
- Update proposed → admitted (check obligation added)
- Reject invalid status keyword
- Reject non-existent node
- Taint propagation: admit node → dependents become tainted
- Taint propagation: verify previously-admitted → no change (still tainted)
- Taint propagation: complex DAG (diamond pattern)
- Obligation context includes assumptions and scope

### 2.3 Implement ops/delete_node.clj

**Spec**:
```clojure
(defn delete-node
  "Delete a node from the graph.
   Node is archived, not destroyed.
   Returns {:ok new-graph} or {:error message}"
  [graph node-id]
  ...)
```

**Preconditions**:
1. Node exists
2. No other nodes depend on it

**Postconditions**:
1. Node moved to `:archived-nodes`
2. Node removed from `:nodes`
3. Version incremented

**Tests (ops/delete_node_test.clj)**:
- Delete leaf node (no dependents)
- Reject delete of node with dependents
- Reject delete of non-existent node
- Archived node preserved with all fields
- Can delete node that was dependency of now-archived node

### 2.4 Implement CLI commands for these operations

**commands/add_node.clj**:
```clojure
(defn run [args]
  ;; Usage: alethfeld add-node <graph.edn> <node.edn>
  ;; Or: alethfeld add-node <graph.edn> --stdin (read node from stdin)
  ...)
```

**commands/update_status.clj**:
```clojure
(defn run [args]
  ;; Usage: alethfeld update-status <graph.edn> <node-id> <status>
  ...)
```

**commands/delete_node.clj**:
```clojure
(defn run [args]
  ;; Usage: alethfeld delete-node <graph.edn> <node-id>
  ...)
```

**Output format** (all commands):
```clojure
;; Success (exit 0)
{:status :ok
 :graph-version 25
 :message "Node :1-abc123 added"}

;; Failure (exit 1)
{:status :error
 :errors [{:type :missing-dependency
           :node-id :1-xyz
           :message "..."}]}
```

**Integration tests (integration/cli_test.clj)**:
- Round-trip: init → add-node → validate passes
- add-node with invalid input → exit 1, error in output
- update-status changes taint correctly
- delete-node then validate passes

---

## Phase 3: Replace Node & External References
**Estimated effort**: 25% context
**Deliverables**: replace-node, add-external-ref, update-external-ref operations

### 3.1 Implement ops/replace_node.clj

**Spec**:
```clojure
(defn replace-node
  "Replace a rejected node with a revised version.
   - Old node must have status :rejected
   - Old node is archived
   - New node gets :provenance/revision-of pointing to old
   - Dependencies on old node are rewritten to new node
   Returns {:ok new-graph} or {:error message}"
  [graph old-id new-node]
  ...)
```

**Preconditions**:
1. Old node exists
2. Old node status is :rejected
3. New node passes all add-node preconditions (after dep rewriting)

**Postconditions**:
1. Old node archived
2. New node added with :revision-of set
3. All nodes that depended on old now depend on new
4. New node status is :proposed

**Tests (ops/replace_node_test.clj)**:
- Replace rejected node successfully
- Reject replace of non-rejected node (verified, proposed, admitted)
- Reject replace of non-existent node
- Dependencies rewritten correctly
- Provenance chain preserved
- Can replace multiple times (A → B → C)
- Replacement that would create cycle rejected

### 3.2 Implement ops/external_ref.clj

**Spec**:
```clojure
(defn add-external-ref
  "Add a new external reference (literature citation).
   Generates ID, sets status to :pending.
   Returns {:ok new-graph :ref-id <id>} or {:error message}"
  [graph ref]
  ...)

(defn update-external-ref
  "Update an external reference after verification.
   Returns {:ok new-graph} or {:error message}"
  [graph ref-id verification-result]
  ...)
```

**Tests (ops/external_ref_test.clj)**:
- Add external ref with DOI
- Add external ref with arXiv
- Add external ref with URL only
- Update ref: pending → verified
- Update ref: pending → mismatch
- Update ref: pending → not-found
- Update ref: pending → metadata-only
- Reject update of non-existent ref
- Multiple refs can coexist

### 3.3 CLI commands

**commands/replace_node.clj**:
```bash
alethfeld replace-node <graph.edn> <old-node-id> <new-node.edn>
```

**commands/external_ref.clj**:
```bash
alethfeld add-external-ref <graph.edn> <ref.edn>
alethfeld update-external-ref <graph.edn> <ref-id> <result.edn>
```

---

## Phase 4: Extract Lemma (Complex Operation)
**Estimated effort**: 35% context
**Deliverables**: extract-lemma operation with independence checking

### 4.1 Implement ops/extract_lemma.clj

**Spec**:
```clojure
(defn extract-lemma
  "Extract a subgraph as a lemma.
   - Validates independence (self-contained, only root accessed externally)
   - All nodes in set must be :verified
   - Creates lemma record
   - Creates lemma-ref node replacing the root
   - Archives extracted nodes
   - Rewrites external dependencies
   Returns {:ok new-graph :lemma-id <id>} or {:error message}"
  [graph lemma-name root-id node-ids]
  ...)
```

**Independence criteria** (from check-independence):
1. Root is in node-ids
2. All internal deps satisfied (or external deps are assumptions/verified/lemma-refs)
3. Only root is depended on from outside the set
4. Scope is balanced (every local-assume has matching local-discharge within set)

**Postconditions**:
1. Lemma record created in `:lemmas`
2. Lemma-ref node created with same statement as root
3. All extracted nodes moved to `:archived-nodes`
4. External nodes that depended on root now depend on lemma-ref
5. Context budget updated (should decrease)

**Tests (ops/extract_lemma_test.clj)**:

*Valid extractions*:
- Extract single verified node
- Extract linear chain
- Extract diamond subgraph
- Extract subgraph with internal local-assume/discharge pair
- Lemma taint computed correctly (all clean → clean, any tainted → tainted)

*Invalid extractions*:
- Root not in node set
- Node in set not verified
- External node depends on non-root internal node
- Unbalanced scope (local-assume without discharge)
- External dep not verified/assumption/lemma-ref
- Node set contains non-existent node

*Dependency rewriting*:
- Single external dependent rewired
- Multiple external dependents rewired
- No dependents (leaf extraction)

*Context budget*:
- Estimate decreases after extraction

### 4.2 CLI command

**commands/extract_lemma.clj**:
```bash
alethfeld extract-lemma <graph.edn> --name "Lemma Name" --root :1-abc --nodes :1-abc,:1-def,:1-ghi
# Or read node list from file:
alethfeld extract-lemma <graph.edn> --name "Lemma Name" --root :1-abc --nodes-file nodes.txt
```

---

## Phase 5: Init, Stats, Recompute & Polish
**Estimated effort**: 25% context
**Deliverables**: Utility commands, final polish, comprehensive integration tests

### 5.1 Implement ops/init.clj

**Spec**:
```clojure
(defn init-graph
  "Create a new empty graph with theorem statement.
   Optionally extracts assumptions from theorem.
   Returns {:ok graph}"
  [theorem-statement opts]
  ...)
```

**Generates**:
- UUID for graph-id
- Version 1
- Theorem node with content-hash
- Empty nodes, symbols, external-refs, lemmas, obligations, archived-nodes
- Metadata with timestamps, proof-mode, iteration-counts, context-budget

**Tests**:
- Init with simple theorem
- Init with proof-mode override
- Content hash computed
- All required fields present
- Output validates against schema

### 5.2 Implement commands/stats.clj

**Spec**:
```bash
alethfeld stats <graph.edn>
```

**Output**:
```clojure
{:graph-id "..."
 :version 24
 :proof-mode :strict-mathematics
 :nodes {:total 18
         :by-status {:verified 12 :proposed 4 :admitted 2 :rejected 0}
         :by-type {:claim 10 :assumption 3 :local-assume 2 ...}
         :by-taint {:clean 15 :tainted 3 :self-admitted 2}}
 :lemmas {:total 2 :proven 2 :pending 0}
 :external-refs {:total 3 :verified 2 :pending 1}
 :obligations 2
 :context-budget {:max 100000 :current 45000 :percent 45}}
```

### 5.3 Implement commands/recompute.clj

**Spec**:
```bash
alethfeld recompute-taint <graph.edn>
```

**Purpose**: Recompute all taint values from scratch. Useful if graph was manually edited or after schema migration.

**Tests**:
- Recompute on valid graph is idempotent
- Recompute fixes incorrect taint values
- Version incremented only if changes made

### 5.4 Comprehensive integration tests

**test/alethfeld/integration/workflow_test.clj**:

```clojure
(deftest full-proof-workflow-test
  (testing "Init → Add assumptions → Add claims → Verify → Extract lemma"
    ...))

(deftest rejection-revision-workflow-test
  (testing "Add → Reject → Replace → Verify"
    ...))

(deftest external-ref-workflow-test
  (testing "Add claim with external ref → Verify ref → Node becomes verified"
    ...))

(deftest taint-propagation-workflow-test
  (testing "Admit node → Dependents become tainted → Extract tainted lemma"
    ...))
```

### 5.5 Polish

- Help text for all commands (`alethfeld help`, `alethfeld add-node --help`)
- `--dry-run` flag for mutation commands (validate but don't write)
- `--output` flag to write to different file
- `--format json` option for JSON output instead of EDN
- Error messages include suggestions ("Did you mean :1-abc123?")

---

## Phase 6: Claude Code Skills & Documentation
**Estimated effort**: 15% context
**Deliverables**: Slash commands, updated documentation

### 6.1 Create Claude Code slash commands

**.claude/commands/validate.md** (update existing)
**.claude/commands/add-node.md**
**.claude/commands/update-status.md**
**.claude/commands/extract-lemma.md**
**.claude/commands/init.md**
**.claude/commands/stats.md**

Each follows pattern:
```markdown
---
allowed-tools: Read, Bash, Write
description: <one line>
---

# <Command Name>

## When to Use
<conditions>

## Invocation
```bash
alethfeld <command> [args]
```

## Input Format
<EDN schema for inputs>

## Output Format
<EDN schema for outputs>

## Error Handling
<how to interpret errors>

## Examples
<concrete examples>
```

### 6.2 Update orchestrator prompt

Create `orchestrator-prompt-v5.md`:
- Replace all Python pseudocode with tool invocations
- Keep EDN schema section (agents need to see structure)
- Reference `alethfeld --help` for operation details
- Should be ~600-800 lines (down from 1500)

### 6.3 Update project documentation

- `scripts/alethfeld/README.md` - comprehensive CLI docs
- `docs/cli-reference.md` - full command reference
- `docs/architecture.md` - update with new structure

---

## Execution Order Summary

| Phase | Est. Context | Key Deliverables |
|-------|--------------|------------------|
| 1 | 25% | Project structure, io.clj, graph.clj, validate command |
| 2 | 35% | add-node, update-status, delete-node |
| 3 | 25% | replace-node, external-ref operations |
| 4 | 35% | extract-lemma (complex) |
| 5 | 25% | init, stats, recompute, integration tests |
| 6 | 15% | Claude Code skills, documentation |

**Total**: ~160% context = 4-5 Claude Code sessions

---

## Testing Checklist

Each operation needs:
- [ ] Happy path test
- [ ] All precondition violation tests
- [ ] All postcondition verification tests
- [ ] Edge cases (empty graph, single node, max depth)
- [ ] Schema validation of output
- [ ] CLI integration test

Global:
- [ ] All example EDN files in repo validate
- [ ] Round-trip: any valid graph survives write→read
- [ ] Multi-command workflow tests
- [ ] Error messages are actionable

---

## Notes for Implementation

1. **Immutability**: All ops return new graph, never mutate input
2. **Consistent errors**: Always `{:status :error :errors [...]}` with `:type`, `:message`
3. **Schema validation**: Run schema validation on output of every op in tests
4. **Timestamps**: Use `config/current-iso8601` consistently
5. **UUIDs**: Use `(subs (str (java.util.UUID/randomUUID)) 0 6)` for node IDs
6. **Atomic writes**: Always write to temp file, then rename
