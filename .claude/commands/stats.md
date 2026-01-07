---
allowed-tools: Read, Bash
description: Display graph statistics
---

# Proof Graph Statistics

Display comprehensive statistics for a semantic proof graph.

## When to Use

Use this command to:
- Get an overview of proof progress
- Check taint status
- Monitor context budget usage
- Assess proof health

## Invocation

```bash
./cli-legacy/scripts/alethfeld stats <graph.edn>
```

## Options

- `--json` or `-j` - Output as JSON instead of EDN
- `--quiet` or `-q` - Minimal output (counts only)

## Output Format

Full output:
```clojure
{:graph-id "abc123"
 :version 24
 :proof-mode :strict-mathematics

 :nodes {:total 18
         :archived 2
         :by-type {:claim 10 :assumption 3 :definition 2 :local-assume 2 :qed 1}
         :by-status {:verified 12 :proposed 4 :admitted 2 :rejected 0}}

 :taint {:counts {:clean 15 :tainted 2 :self-admitted 1}
         :clean-count 15
         :tainted-count 3}

 :structure {:max-depth 4
             :avg-dependencies 2.5
             :max-dependencies 5}

 :references {:external-refs 3
              :lemmas 2
              :obligations 2}

 :context-budget {:estimated-tokens 45000
                  :max-tokens 100000
                  :usage-percent 45.0}}
```

Quiet output:
```
18 nodes, 15 clean, 3 tainted
```

## Interpreting Results

### Taint Status

- **clean** - Node and all ancestors are verified
- **tainted** - At least one ancestor is admitted
- **self-admitted** - This node itself is admitted

### Context Budget

- **usage-percent** - How much of the context budget is used
- Extract lemmas when approaching 70-80%

### Node Status

- **verified** - Fully checked by Verifier
- **proposed** - Awaiting verification
- **admitted** - Accepted without full verification (creates obligation)
- **rejected** - Needs revision
