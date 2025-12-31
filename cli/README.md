# Alethfeld CLI

A Clojure CLI tool for semantic proof graph operations.

## Quick Start

### Using Compiled Uberjar (Recommended - 67% Faster)

```bash
# Build the uberjar (one-time)
clojure -T:build uber

# Run via wrapper script
./scripts/alethfeld <command> [options]
./scripts/alethfeld --help

# Or run directly with Java
java -jar target/alethfeld.jar <command> [options]
```

**Performance:** 1.1s startup (67% faster than Clojure CLI)

### Using Clojure CLI (Development)

```bash
clojure -M:run <command> [options]
clojure -M:run --help
```

**Performance:** 3.3s startup (convenient for development)

## Commands

| Command | Description |
|---------|-------------|
| `init` | Initialize a new semantic proof graph |
| `validate` | Validate graph against schema |
| `add-node` | Add a node to the graph |
| `update-status` | Update node verification status |
| `replace-node` | Replace a rejected node |
| `delete-node` | Archive a leaf node |
| `extract-lemma` | Extract subgraph as independent lemma |
| `external-ref` | Manage external references |
| `stats` | Display graph statistics |
| `recompute` | Recalculate taint propagation |
| `convert` | Convert legacy format to v4 schema |

## Common Workflows

### Initialize a proof

```bash
./scripts/alethfeld init "For all continuous f,g: (g \\circ f) is continuous" \
  --mode strict-mathematics \
  --output proof.edn
```

### Add nodes

```bash
# From file
./scripts/alethfeld add-node proof.edn node.edn

# From stdin
echo '{:id :1-abc :type :claim :statement "..." ...}' | \
  ./scripts/alethfeld add-node --stdin proof.edn
```

### Verification loop

```bash
# Verify a step
./scripts/alethfeld update-status proof.edn :1-abc123 verified

# Reject a step
./scripts/alethfeld update-status proof.edn :1-abc123 rejected

# Replace rejected with revision
./scripts/alethfeld replace-node proof.edn :1-abc123 revised.edn
```

### Extract lemmas

```bash
./scripts/alethfeld extract-lemma proof.edn \
  --name "Intermediate Value Theorem" \
  --root :2-ivt456 \
  --nodes :2-ivt456,:3-sub1,:3-sub2
```

### Validate

```bash
./scripts/alethfeld validate proof.edn -v
```

## Development

### Run tests

```bash
clojure -M:test
```

### Build and Distribution

**Uberjar (Recommended for Distribution):**
```bash
# Build
clojure -T:build uber

# Test
java -jar target/alethfeld.jar --help

# Or use wrapper script
./scripts/alethfeld --help

# Size: 7.3 MB (includes all dependencies)
# Startup: ~1.1 seconds (67% faster than Clojure CLI)
```

**Docker:**
```dockerfile
FROM eclipse-temurin:21-jre-alpine
COPY target/alethfeld.jar /app/
ENTRYPOINT ["java", "-jar", "/app/alethfeld.jar"]
```

## Project Structure

```
cli/ (formerly alethfeld/)
├── src/alethfeld/         # Clojure source (alethfeld.* namespaces)
│   ├── core.clj           # CLI entry point
│   ├── schema.clj         # Malli schemas
│   ├── validators.clj     # Validation logic
│   ├── graph.clj          # Graph query functions
│   ├── io.clj             # EDN I/O
│   ├── config.clj         # Constants
│   ├── ops/               # Graph operations
│   └── commands/          # CLI commands
├── test/alethfeld/        # Unit and integration tests
├── bench/alethfeld/       # Performance benchmarks
└── deps.edn
```

## Graph Schema

See [docs/proof-format.md](../docs/proof-format.md) for the full EDN schema.

Key concepts:
- **Nodes**: Claims, assumptions, definitions, lemma-refs
- **Dependencies**: DAG of what each node uses
- **Scope**: Active local assumptions
- **Taint**: Propagates from admitted steps
- **Status**: proposed, verified, admitted, rejected

## Full Documentation

- [CLI Reference](../docs/cli-reference.md) - Complete command documentation
- [Architecture](../docs/architecture.md) - System design
- [Proof Format](../docs/proof-format.md) - EDN schema details
