---
allowed-tools: Read, Bash
description: Update node verification status in a proof graph
---

# Update Node Status

Update the verification status of a node after review by the Verifier.

## When to Use

Use this command when:
- The Verifier accepts a step: `proposed → verified`
- The Verifier rejects a step: `proposed → rejected`
- A step needs to be admitted: `proposed → admitted`

## Invocation

```bash
./cli-legacy/scripts/alethfeld update-status <graph.edn> <node-id> <status>
```

## Arguments

- `<graph.edn>` - Path to the proof graph file
- `<node-id>` - The node ID (keyword format, e.g., `:1-abc123`)
- `<status>` - New status: `proposed`, `verified`, `admitted`, or `rejected`

## Example

```bash
./scripts/alethfeld update-status proof.edn :1-abc123 verified
```

## Status Values

| Status | Meaning |
|--------|---------|
| `proposed` | Initial state, awaiting verification |
| `verified` | Verifier accepts the step |
| `admitted` | Temporarily accepted without full verification (creates proof obligation) |
| `rejected` | Verifier challenges the step (requires revision) |

## Side Effects

### Taint Propagation

Status changes trigger automatic taint recomputation:
- `:admitted` → node becomes `:self-admitted`, all dependents become `:tainted`
- `:verified` → depends on ancestor taints
- Changes propagate to all transitive dependents

### Obligations

- Setting status to `:admitted` adds a proof obligation
- Changing from `:admitted` to another status removes the obligation

## Output Format

Success:
```clojure
{:status :ok
 :message "Node :1-abc123 status updated to verified"
 :graph-version 26}
```

## Options

- `--dry-run` or `-d` - Validate without writing
- `--output FILE` or `-o FILE` - Write to different file
