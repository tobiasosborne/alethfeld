# ANSI Proof Visualization Tool

This tool provides a terminal-based visualization of Alethfeld proof graphs using ANSI color codes and box-drawing characters.

## Usage

```bash
./scripts/ansi-viz.clj <proof-graph.edn> [summary]
```

### Arguments

*   `<proof-graph.edn>`: Path to the EDN proof graph file you want to visualize.
*   `summary`: (Optional) If provided, prints a compact one-line summary of the graph (nodes, verification status, taint status).

## Features

*   **Hierarchical View**: Displays the proof structure as a tree, showing the relationship between claims, assumptions, and definitions.
*   **Semantic Coloring**: Uses a Nord-inspired color palette to distinguish node types (e.g., assumptions in blue, definitions in sand, claims in white).
*   **Status Indicators**: Clearly shows verification status (verified, admitted, rejected) with symbols and colors.
*   **Taint Tracking**: Highlights tainted nodes (those depending on unverified or rejected steps) in red.

## Requirements

*   [Babashka](https://github.com/babashka/babashka) (`bb`) must be installed and available in your path.

## Example

```bash
./scripts/ansi-viz.clj examples/dobinski-formula/dobinski-v2.edn
```

Output:
(A colorful tree representation of the proof)
