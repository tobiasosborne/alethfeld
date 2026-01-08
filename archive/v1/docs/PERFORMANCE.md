# Alethfeld Performance

This document tracks baseline performance metrics for critical graph operations.

## Running Benchmarks

```bash
cd alethfeld

# Quick benchmarks (fewer iterations, faster)
clojure -M:bench quick

# Full benchmarks (more accurate, slower)
clojure -M:bench full
```

## Baseline Results (Dec 2025)

Measured on: Linux (WSL2), Clojure 1.12.0

### Summary Table

| Operation | 50 nodes | 100 nodes | 500 nodes | Complexity |
|-----------|----------|-----------|-----------|------------|
| get-ancestors | 22 us | 43 us | 243 us | O(n) |
| get-descendants | 28 us | 59 us | 370 us | O(n) |
| topological-sort | 437 us | 1.75 ms | 50 ms | O(n^2) |
| topological-sort (partial) | 139 ns | 144 ns | 129 ns | O(1)* |
| compute-all-scopes | 990 us | 3.8 ms | 112 ms | O(n^2) |
| validate-semantics | 2.3 ms | 8.1 ms | 219 ms | O(n^2) |
| validate-schema | 189 us | 290 us | 747 us | O(n) |
| find-cycle | 71 us | 159 us | 885 us | O(n+e) |

*Partial topological sort is O(k) where k = closure size of target nodes

### Detailed Results

#### get-ancestors
Traverses dependency graph backwards to find all transitive dependencies.

| Graph Size | Mean | Std Dev |
|------------|------|---------|
| 50 nodes (linear) | 22.3 us | 9.5 us |
| 100 nodes (linear) | 42.8 us | 6.6 us |
| 500 nodes (linear) | 242.8 us | 31.8 us |

#### get-descendants
Traverses dependency graph forwards using reverse dependency index.

| Graph Size | Mean | Std Dev |
|------------|------|---------|
| 50 nodes (linear) | 28.3 us | 1.3 us |
| 100 nodes (linear) | 58.6 us | 4.0 us |
| 500 nodes (linear) | 370.0 us | 21.8 us |

#### topological-sort (full graph)
Sorts all nodes in dependency order using Kahn's algorithm.

| Graph Type | 50 nodes | 100 nodes | 500 nodes |
|------------|----------|-----------|-----------|
| Linear | 437 us | 1.75 ms | 50.1 ms |
| Tree | 541 us | 1.72 ms | 46.3 ms |
| Diamond | 469 us | 1.81 ms | 52.6 ms |

#### topological-sort (partial)
Sorts only nodes in closure of specified targets - much faster for single-node queries.

| Graph Size | Mean |
|------------|------|
| 50 nodes | 139 ns |
| 100 nodes | 144 ns |
| 500 nodes | 129 ns |

The partial sort leverages `get-ancestors` to compute only the minimal closure needed.

#### compute-all-scopes
Computes valid scopes for all nodes in batch. Uses batched ancestor computation.

| Graph Size | Mean |
|------------|------|
| 50 nodes | 990 us |
| 100 nodes | 3.85 ms |
| 500 nodes | 111.8 ms |

#### validate-semantics
Full semantic validation including referential integrity, acyclicity, scope validity, and taint correctness.

| Graph Size | Mean |
|------------|------|
| 50 nodes | 2.28 ms |
| 100 nodes | 8.09 ms |
| 500 nodes | 219 ms |

#### validate-schema
Malli schema validation using the SemanticGraph schema.

| Graph Size | Mean |
|------------|------|
| 50 nodes | 189 us |
| 100 nodes | 290 us |
| 500 nodes | 747 us |

Linear scaling - schema validation is efficient.

#### find-cycle
DFS-based cycle detection with coloring.

| Graph Size | Mean |
|------------|------|
| 48 nodes (diamond) | 70.6 us |
| 100 nodes (diamond) | 159.3 us |
| 500 nodes (diamond) | 884.6 us |

Linear with graph size - O(n + e) where e = edges.

## Performance Considerations

### Hot Paths
The following operations are called frequently during proof development:

1. **Partial topological sort** - Called for each node addition. Now O(k) instead of O(n^2).
2. **get-ancestors** - Called for scope computation. O(n) per call.
3. **Schema validation** - Called on every graph write. O(n) - efficient.

### Optimization Opportunities

1. **compute-all-scopes** shows O(n^2) behavior. Could potentially cache intermediate results.
2. **validate-semantics** is slow for large graphs. Consider incremental validation.
3. **topological-sort** (full) shows O(n^2) behavior. Current Kahn implementation could be optimized.

### Caching

The graph module uses metadata-based caching for reverse dependencies:
- `build-reverse-deps` caches the reverse dependency map
- `invalidate-caches` must be called after graph structure changes

## Adding New Benchmarks

Edit `cli/bench/alethfeld/bench.clj` to add new benchmarks.

```clojure
(defn bench-my-operation
  [quick?]
  (println "\n=== Benchmarking my-operation ===")
  (doseq [n [50 100 500]]
    (let [graph (generate-linear-graph n)]
      (println (str "\nLinear graph (" n " nodes):"))
      (if quick?
        (crit/quick-bench (my-operation graph))
        (crit/bench (my-operation graph))))))
```

Then add the call to `run-all-benchmarks`.
