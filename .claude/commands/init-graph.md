---
allowed-tools: Read, Bash, Write
description: Initialize a new semantic proof graph
---

# Initialize Proof Graph

Create a new semantic proof graph for a theorem.

## When to Use

Use this command when starting a new proof project.

## Invocation

```bash
./cli-legacy/scripts/alethfeld init <output.edn> --theorem "Theorem statement"
```

## Required Arguments

- `<output.edn>` - Path for the new graph file
- `--theorem STMT` or `-t STMT` - Theorem statement in LaTeX

## Optional Options

- `--mode MODE` or `-m MODE` - Proof mode (default: `strict-mathematics`)
  - `strict-mathematics` - Full rigor required
  - `formal-physics` - Standard physics conventions
  - `algebraic-derivation` - Algebraic manipulations
- `--graph-id ID` or `-g ID` - Custom graph ID (auto-generated if omitted)
- `--max-tokens N` or `-T N` - Context budget limit (default: 100000)

## Examples

Basic initialization:
```bash
./scripts/alethfeld init proof.edn -t 'For all $n \geq 1$, $\sum_{k=1}^n k = \frac{n(n+1)}{2}$'
```

With custom mode:
```bash
./scripts/alethfeld init quantum-proof.edn -t 'Quantum channel composition' -m formal-physics
```

## Output Format

The command creates an EDN file with:

```clojure
{:graph-id "uuid-prefix"
 :version 1
 :theorem {:id :theorem
           :statement "..."
           :content-hash "..."}
 :nodes {}
 :symbols {}
 :external-refs {}
 :lemmas {}
 :obligations []
 :archived-nodes {}
 :metadata {:created-at "..."
            :last-modified "..."
            :proof-mode :strict-mathematics
            :iteration-counts {:verification {} :expansion {} :strategy 0}
            :context-budget {:max-tokens 100000 :current-estimate 0}}}
```

## Next Steps After Init

1. Add assumptions: `add-node` with `:type :assumption`
2. Add definitions: `add-node` with `:type :definition`
3. Begin proof: `add-node` with `:type :claim`
