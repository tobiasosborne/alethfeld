# Initialization Phase

## Current State

You are beginning a new proof verification session.

**Theorem:**
```
<THEOREM_STATEMENT>
```

**Graph Location:** `<PROOF_GRAPH_PATH>`

## Objectives

1. Initialize the proof graph with the theorem statement
2. Detect and record initial assumptions from the theorem
3. Set up the working environment for proof development

## Actions Required

- Run `alethfeld init` to create the graph structure
- Review the theorem for domain restrictions and implicit assumptions
- Identify any external references that may be needed

## Next Phase

After initialization is complete, the workflow transitions to **Theorem Audit** to assess the validity and provability of the theorem.

## Notes

- The graph will be created in strict-mathematics mode by default
- All subsequent mutations must go through the CLI
- Node IDs will be permanent once assigned
