# Skeleton Construction Phase

## Current State

Building the high-level proof skeleton.

**Theorem:**
```
<THEOREM_STATEMENT>
```

## Objectives

1. Create top-level proof steps (depth 1 only)
2. Establish the logical flow from assumptions to conclusion
3. Identify where expansion will be needed

## Construction Guidelines

### Skeleton Requirements
- Output ONLY depth-1 level steps
- No substeps at this phase
- Each step must have a clear justification type
- Dependencies must reference existing nodes or assumptions

### Node Format
```clojure
{:id :<suggested-id>
 :claim "Fully quantified LaTeX formula"
 :using [:<dep-id> :A1 ...]
 :justification :keyword}
```

### Forbidden Patterns
- Hidden quantifiers
- Implicit classical logic
- Uncited external theorems (use :admitted)
- Type drift
- Prose reasoning
- "Well known" or "standard" justifications

## Expected Output

The prover should produce:
```clojure
{:steps
 [{:id :1-xxx :claim "..." :using [...] :justification :keyword}
  {:id :1-yyy :claim "..." :using [...] :justification :keyword}
  ...]}
```

## CLI Operations

For each step:
```bash
alethfeld add-node graph.edn --stdin
```

## Next Phase

After skeleton is created, advance to **Skeleton Review** for adviser evaluation.
