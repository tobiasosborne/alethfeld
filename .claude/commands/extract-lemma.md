---
allowed-tools: Read, Bash
description: Extract verified subgraph as independent lemma
---

# Extract Lemma

Extract a verified subgraph as an independent, reusable lemma.

## When to Use

Use this command when:
- A portion of the proof is complete and self-contained
- You want to reduce context window usage
- A result is worth extracting for reuse

## Invocation

```bash
./cli-legacy/scripts/alethfeld extract-lemma <graph.edn> <root-node-id> --name "Lemma Name"
```

## Arguments

- `<graph.edn>` - Path to the proof graph
- `<root-node-id>` - The root node of the extraction (e.g., `:1-abc123`)

## Required Options

- `--name NAME` or `-n NAME` - Name for the lemma (e.g., "L1-fourier")

## Optional Options

- `--nodes IDS` or `-N IDS` - Explicit comma-separated node IDs to extract
  - If not provided, extracts root + all ancestors
- `--dry-run` or `-d` - Validate without writing
- `--output FILE` or `-o FILE` - Write to different file

## Extraction Rules

1. **All nodes must be verified** - Only `:verified` nodes can be extracted
2. **Only root has external dependents** - No other internal node can be depended upon from outside
3. **Scope must be balanced** - Every `:local-assume` must have a matching `:local-discharge`

## Examples

Extract with automatic ancestor detection:
```bash
./scripts/alethfeld extract-lemma proof.edn :1-abc123 -n L1-fourier
```

Extract specific nodes:
```bash
./scripts/alethfeld extract-lemma proof.edn :1-abc123 -n L2-result -N :1-abc123,:1-def456,:2-ghi789
```

Dry run to check validity:
```bash
./scripts/alethfeld extract-lemma proof.edn :1-abc123 -n Test --dry-run
```

## What Happens

1. A lemma record is created in `:lemmas`
2. A `:lemma-ref` node replaces the root (same statement)
3. Extracted nodes are moved to `:archived-nodes`
4. External dependents now depend on the lemma-ref
5. Context budget estimate decreases

## Output Format

Success:
```clojure
{:status :ok
 :message "Lemma L1-fourier extracted with 6 nodes"
 :lemma-id "L1-fourier"
 :nodes-extracted 6
 :graph-version 27}
```

## Error Handling

- **:not-all-verified** - Some nodes are not verified
- **:external-deps-on-non-root** - Internal node has external dependents
- **:unbalanced-scope** - Local assumes not properly discharged
