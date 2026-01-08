# Decomposition Phase

## Current State

Analyzing the graph for extractable independent subgraphs.

**Theorem:**
```
<THEOREM_STATEMENT>
```

## Objectives

1. Identify self-contained subproofs that can become lemmas
2. Extract verified subgraphs to reduce complexity
3. Create reusable lemma records

## Independence Criteria

A node set S rooted at R is independent if and only if:

1. All dependencies of S are in S, or are assumptions, or are verified external references
2. Only R is depended on from outside S
3. Every local-assume in S has a matching local-discharge in S

## Extraction Analysis

The lemma decomposer should evaluate:
```clojure
{:proposed-extractions
 [{:lemma-name "descriptive name"
   :root-node :<id>
   :nodes #{:<id> ...}
   :lemma-statement "LaTeX"
   :independence {:external-deps #{...} :scope-balanced true}
   :benefit-score 0.0-1.0}]
 :extraction-order ["L1" "L2" ...]
 :warnings [...]}
```

## Benefit Score Calculation

```
benefit = 0.3 * size_reduction
        + 0.3 * isolation
        + 0.2 * reusability
        + 0.2 * depth_reduction
```

Only propose extractions with benefit > 0.4.

## CLI Operations

For each approved extraction:
```bash
alethfeld extract-lemma graph.edn --name "Lemma Name" --root :1-abc --nodes :1-abc,:1-def,:1-ghi
```

## Next Phase

After decomposition analysis, advance to **Expand-Verify Loop** to fill in proof details.
