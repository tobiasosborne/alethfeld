# Alethfeld CLI Reference

Complete command reference for the `alethfeld` CLI tool.

## Installation

```bash
cd alethfeld

# Recommended: Use the pre-built wrapper (fast, ~1s startup)
./scripts/alethfeld <command> [options]

# Alternative: Build your own uberjar
clojure -T:build uber
java -jar target/alethfeld.jar <command> [options]

# Development only (slow, ~3s startup)
clojure -M:run <command> [options]
```

## Global Options

| Option | Description |
|--------|-------------|
| `-h, --help` | Show help message |
| `-V, --version` | Show version information |

---

## Commands

### init

Initialize a new semantic proof graph.

```bash
alethfeld init "Theorem statement" [options]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-m, --mode MODE` | Proof mode: `strict-mathematics`, `formal-physics`, `algebraic-derivation` |
| `-o, --output FILE` | Output file (default: `proof.edn`) |

**Example:**
```bash
alethfeld init "For all continuous f,g: (g \\circ f) is continuous" -m strict-mathematics -o continuity.edn
```

---

### validate

Validate a semantic proof graph against the schema.

```bash
alethfeld validate <graph.edn> [options]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-v, --verbose` | Detailed error output |
| `-q, --quiet` | Minimal output (exit code only) |
| `-s, --schema-only` | Skip semantic checks |

**Exit codes:**
- `0` - Validation passed
- `1` - Validation failed
- `2` - File error

---

### add-node

Add a node to a graph.

```bash
alethfeld add-node <graph.edn> <node.edn> [options]
alethfeld add-node --stdin <graph.edn> [options]
```

**Options:**
| Option | Description |
|--------|-------------|
| `-d, --dry-run` | Validate without writing |
| `-o, --output FILE` | Write to different file |
| `--stdin` | Read node from stdin |

**Node format:**
```clojure
{:id :1-abc123
 :type :claim
 :statement "For all $\\varepsilon > 0$..."
 :dependencies #{:A1 :1-def456}
 :scope #{}
 :justification :modus-ponens
 :depth 1
 :display-order 1}
```

---

### update-status

Update a node's verification status.

```bash
alethfeld update-status <graph.edn> <node-id> <status> [options]
```

**Valid statuses:** `proposed`, `verified`, `admitted`, `rejected`

**Options:**
| Option | Description |
|--------|-------------|
| `-d, --dry-run` | Validate without writing |
| `-o, --output FILE` | Write to different file |

**Effects:**
- Updates node status
- Recomputes taint for node and all dependents
- If `admitted`, adds to obligations list

---

### replace-node

Replace a rejected node with a revised version.

```bash
alethfeld replace-node <graph.edn> <old-node-id> <new-node.edn> [options]
```

**Preconditions:**
- Old node must have status `:rejected`
- New node must pass add-node validation

**Effects:**
- Archives old node
- Adds new node with `:revision-of` set
- Rewrites dependencies from old to new

---

### delete-node

Delete (archive) a node from the graph.

```bash
alethfeld delete-node <graph.edn> <node-id> [options]
```

**Preconditions:**
- Node must exist
- No other nodes can depend on it

**Effects:**
- Moves node to `:archived-nodes`
- Updates version

---

### extract-lemma

Extract a verified subgraph as an independent lemma.

```bash
alethfeld extract-lemma <graph.edn> --name "Lemma Name" --root <node-id> --nodes <id1>,<id2>,... [options]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--name NAME` | Human-readable lemma name (required) |
| `--root ID` | Root node ID (required) |
| `--nodes IDS` | Comma-separated node IDs to extract |
| `--nodes-file FILE` | Read node IDs from file (one per line) |
| `-d, --dry-run` | Validate without writing |
| `-o, --output FILE` | Write to different file |

**Independence criteria** (all must pass):
1. Root is in node set
2. All internal dependencies satisfied
3. Only root is depended on from outside the set
4. Scope is balanced (local-assume/discharge pairs match)
5. All nodes have status `:verified`

**Effects:**
- Creates lemma record in `:lemmas`
- Creates `:lemma-ref` node replacing root
- Archives extracted nodes
- Rewrites external dependencies to lemma-ref

---

### external-ref

Manage external references (citations).

**Add a reference:**
```bash
alethfeld external-ref add <graph.edn> <ref.edn>
```

**Update after verification:**
```bash
alethfeld external-ref update <graph.edn> <ref-id> <result.edn>
```

**Reference format:**
```clojure
{:doi "10.xxxx/yyyy"
 :arxiv "2301.12345"
 :claimed-statement "The theorem states..."}
```

**Verification result format:**
```clojure
{:status :verified  ; or :mismatch, :not-found, :metadata-only
 :found-statement "Actual statement from source"
 :bibdata {:authors ["..."] :title "..." :year 2024}}
```

---

### stats

Display graph statistics.

```bash
alethfeld stats <graph.edn> [options]
```

**Options:**
| Option | Description |
|--------|-------------|
| `--format FORMAT` | Output format: `edn` (default), `json` |

**Output:**
```clojure
{:graph-id "abc123"
 :version 24
 :proof-mode :strict-mathematics
 :nodes {:total 18
         :by-status {:verified 12 :proposed 4 :admitted 2}
         :by-type {:claim 10 :assumption 3 ...}
         :by-taint {:clean 15 :tainted 3}}
 :lemmas {:total 2 :proven 2}
 :external-refs {:total 3 :verified 2 :pending 1}
 :obligations 2
 :context-budget {:max 100000 :current 45000 :percent 45}}
```

---

### recompute

Recompute taint propagation across all nodes.

```bash
alethfeld recompute <graph.edn> [options]
```

Use this after manual edits or schema migrations.

**Options:**
| Option | Description |
|--------|-------------|
| `-d, --dry-run` | Show changes without writing |
| `-o, --output FILE` | Write to different file |

---

### convert

Convert legacy proof format to v4 schema.

```bash
alethfeld convert <input.edn> <output.edn>
```

Handles older proof formats and migrates them to the current schema version.

---

## Error Handling

All commands return structured errors:

```clojure
{:status :error
 :errors [{:type :missing-dependency
           :message "Dependencies not found: #{:1-xyz}"
           :node-id :1-abc123}]}
```

Common error types:
- `:duplicate-id` - Node ID already exists
- `:missing-dependency` - Referenced node doesn't exist
- `:invalid-scope` - Scope contains invalid entries
- `:would-create-cycle` - Operation would create dependency cycle
- `:not-verified` - Node is not verified (for extraction)
- `:has-dependents` - Node has dependents (for deletion)
- `:not-rejected` - Node is not rejected (for replacement)

---

## Workflow Examples

### Start a new proof

```bash
# Initialize graph
alethfeld init "For all continuous f,g: (g \\circ f) is continuous" -o cont.edn

# Add assumptions (parsed automatically or manually)
echo '{:id :A1 :type :assumption :statement "f is continuous" ...}' | \
  alethfeld add-node --stdin cont.edn

# Validate
alethfeld validate cont.edn -v
```

### Verification workflow

```bash
# Prover adds a step
alethfeld add-node cont.edn step1.edn

# Verifier accepts
alethfeld update-status cont.edn :1-abc123 verified

# Or rejects
alethfeld update-status cont.edn :1-abc123 rejected

# Prover revises
alethfeld replace-node cont.edn :1-abc123 step1-revised.edn
```

### Extract lemma

```bash
# Check stats first
alethfeld stats cont.edn

# Extract verified subgraph
alethfeld extract-lemma cont.edn \
  --name "Triangle Inequality" \
  --root :2-tri123 \
  --nodes :2-tri123,:3-sub1,:3-sub2

# Verify extraction worked
alethfeld validate cont.edn -v
```
