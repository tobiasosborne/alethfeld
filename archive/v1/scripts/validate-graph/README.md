# validate-graph

A Clojure CLI tool for validating Alethfeld semantic proof graph EDN files against the schema specification and semantic invariants.

## Overview

`validate-graph` performs comprehensive validation of semantic proof graphs, ensuring they conform to the Alethfeld schema (as defined in `orchestrator-prompt-v4.md`) and maintain semantic consistency. It catches errors early—before proofs are processed by the Lean formalizer or other downstream tools.

### What It Validates

**Schema Validation (Malli)**
- All required fields present with correct types
- Enum values match allowed sets (node types, justifications, statuses)
- Content hashes are valid 16-character hex strings
- ISO 8601 timestamps are properly formatted
- Nested structures (provenance, metadata, symbols) are well-formed

**Semantic Validation**
- **Referential Integrity**: All node dependencies, parent references, lemma refs, and external refs point to existing entities
- **Acyclicity**: The dependency graph forms a valid DAG (no circular dependencies)
- **Scope Validity**: Local assumptions are correctly tracked through proof scope
- **Discharge Correctness**: Local discharges only target in-scope ancestors
- **Taint Propagation**: Taint status correctly propagates from admitted/rejected nodes

## Installation

### Prerequisites

- [Clojure CLI](https://clojure.org/guides/install_clojure) (1.11+)
- Java 11+

### Setup

No installation required—run directly with the Clojure CLI:

```bash
cd scripts/validate-graph
clojure -M:run <file.edn>
```

Or run the tests:

```bash
clojure -M:test
```

## Usage

### Basic Validation

```bash
# Validate a semantic proof graph
clojure -M:run path/to/proof-graph.edn

# Output on success:
# OK: All validations passed

# Output on failure:
# FAIL: Semantic validation
#   [missing-dependency] Node :1-abc123 depends on non-existent node :1-xyz789
```

### Command-Line Options

```
Usage: validate-graph [options] <file.edn>

Options:
  -v, --verbose       Show detailed error information
  -q, --quiet         Only show pass/fail, no details
  -s, --schema-only   Only run schema validation, skip semantic checks
  -h, --help          Show this help message

Exit codes:
  0 - Validation successful
  1 - Validation failed
  2 - File error (not found, parse error, etc.)
```

### Examples

```bash
# Verbose output with full error details
clojure -M:run -v examples/qbf-rank1/expanded.edn

# Quick schema check only (faster for large files)
clojure -M:run -s examples/shannon-maximum.edn

# Quiet mode for CI/CD pipelines
clojure -M:run -q proof.edn && echo "Valid" || echo "Invalid"
```

## Architecture

```
validate-graph/
├── deps.edn                    # Dependencies (Clojure, Malli, tools.cli, tools.logging)
├── src/validate_graph/
│   ├── main.clj               # CLI entry point
│   ├── schema.clj             # Malli schema definitions
│   ├── validators.clj         # Semantic validation logic
│   └── config.clj             # Configuration constants
├── test/validate_graph/
│   ├── fixtures.clj           # Test data generators
│   ├── schema_test.clj        # Schema validation tests
│   ├── referential_test.clj   # Referential integrity tests
│   ├── acyclicity_test.clj    # Cycle detection tests
│   ├── scope_test.clj         # Scope validation tests
│   ├── taint_test.clj         # Taint propagation tests
│   ├── edge_cases_test.clj    # Edge case tests
│   └── cli_test.clj           # CLI integration tests
└── fix-schema.clj             # Utility script for fixing common schema issues
```

## Schema Reference

The semantic proof graph schema is based on the Alethfeld orchestrator specification. Key structures:

### Top-Level Graph

```clojure
{:graph-id    "unique-graph-identifier"
 :version     1                           ; Schema version (>= 1)
 :theorem     {:id :theorem, :statement "...", :content-hash "..."}
 :nodes       {:<id> Node, ...}           ; Active proof nodes
 :symbols     {:sym-id Symbol, ...}       ; Symbol declarations
 :external-refs {"ref-id" ExternalRef}    ; Literature citations
 :lemmas      {"lem-id" Lemma}            ; Extracted lemmas
 :obligations [Obligation, ...]           ; Proof obligations
 :archived-nodes {:<id> Node, ...}        ; Archived/extracted nodes
 :metadata    Metadata}
```

### Node Structure

```clojure
{:id           :1-abc123                  ; Keyword ID
 :type         :claim                     ; :assumption, :local-assume, :claim, :qed, etc.
 :statement    "LaTeX statement"          ; Non-empty string
 :content-hash "0123456789abcdef"         ; 16 hex chars
 :dependencies #{:1-dep1 :1-dep2}         ; Set of node IDs
 :scope        #{:1-assume1}              ; Active local assumptions
 :justification :modus-ponens             ; Inference rule
 :status       :verified                  ; :proposed, :verified, :admitted, :rejected
 :taint        :clean                     ; :clean, :tainted, :self-admitted
 :depth        1                          ; Nesting level (>= 0)
 :parent       :1-parent                  ; Optional parent node
 :display-order 0                         ; Ordering hint
 :provenance   {:created-at "2024-01-01T00:00:00Z"
                :created-by :prover
                :round 1
                :revision-of nil}}
```

### Node Types

| Type | Description |
|------|-------------|
| `:assumption` | Global hypothesis from theorem statement |
| `:local-assume` | Scoped assumption introduction |
| `:local-discharge` | Discharges a local-assume |
| `:definition` | Definition introduction |
| `:claim` | Proof step |
| `:lemma-ref` | Reference to extracted/proven lemma |
| `:external-ref` | Reference to external result |
| `:qed` | Concludes a subproof |

### Justification Rules

The validator accepts these justification types:

- **Basic Logic**: `:modus-ponens`, `:conjunction-intro`, `:conjunction-elim`, `:disjunction-intro`, `:disjunction-elim`, `:implication-intro`, `:contradiction`
- **Quantifiers**: `:universal-intro`, `:universal-elim`, `:existential-intro`, `:existential-elim`
- **Equality**: `:equality-rewrite`, `:algebraic-rewrite`, `:substitution`
- **Structural**: `:assumption`, `:local-assumption`, `:discharge`, `:definition-expansion`, `:case-split`, `:qed`
- **Induction**: `:induction-base`, `:induction-step`
- **References**: `:lemma-application`, `:external-application`
- **Special**: `:admitted` (explicit gap acknowledgment)

## Semantic Invariants

### Referential Integrity

Every reference must point to an existing entity:

```clojure
;; Dependencies must exist in :nodes
{:id :1-step2, :dependencies #{:1-step1}}  ; :1-step1 must exist

;; Parents must exist in :nodes
{:id :2-child, :parent :1-parent}          ; :1-parent must exist

;; Lemma refs must exist in :lemmas
{:id :1-lemref, :type :lemma-ref, :lemma-id "lem-001"}  ; "lem-001" must exist

;; Symbol :introduced-at must reference existing node
{:sym-x {:introduced-at :1-def1}}          ; :1-def1 must exist
```

### Acyclicity

The dependency graph must be a DAG. These are rejected:

```clojure
;; Self-loop
{:id :1-a, :dependencies #{:1-a}}

;; Direct cycle
{:id :1-a, :dependencies #{:1-b}}
{:id :1-b, :dependencies #{:1-a}}

;; Transitive cycle
{:id :1-a, :dependencies #{:1-c}}
{:id :1-b, :dependencies #{:1-a}}
{:id :1-c, :dependencies #{:1-b}}
```

### Scope Tracking

The `:scope` field must accurately reflect which local assumptions are active:

```clojure
;; Valid: :1-assume is an ancestor local-assume
{:id :1-assume, :type :local-assume, :introduces "P"}
{:id :1-step, :dependencies #{:1-assume}, :scope #{:1-assume}}

;; Invalid: :1-assume not an ancestor
{:id :1-other, :scope #{:1-assume}}  ; Error: :1-assume not reachable

;; Invalid: :1-assume was discharged
{:id :1-discharge, :type :local-discharge, :discharges :1-assume}
{:id :1-after, :dependencies #{:1-discharge}, :scope #{:1-assume}}  ; Error
```

### Taint Propagation

Taint status must be computed correctly:

| Node Status | Expected Taint |
|-------------|----------------|
| `:admitted` | `:self-admitted` |
| `:rejected` | `:tainted` |
| Depends on tainted node | `:tainted` |
| Otherwise | `:clean` |

```clojure
;; Correct taint propagation
{:id :1-admitted, :status :admitted, :taint :self-admitted}
{:id :1-child, :dependencies #{:1-admitted}, :taint :tainted}  ; Must be :tainted

;; Incorrect (will fail validation)
{:id :1-admitted, :status :admitted, :taint :clean}  ; Should be :self-admitted
```

## Error Messages

The validator provides detailed, actionable error messages:

```
FAIL: Schema validation
  Content hash must be 16 lowercase hex characters

FAIL: Semantic validation
  [missing-dependency] Node :1-step5 depends on non-existent node :1-missing
  [dependency-cycle] Dependency cycle detected: :1-a -> :1-b -> :1-c -> :1-a
  [invalid-scope] Node :1-claim has invalid scope entries: #{:1-discharged}
  [incorrect-taint] Node :1-child has taint :clean but should be :tainted
```

## Utility Scripts

### fix-schema.clj

A standalone script to fix common schema issues in EDN files:

```bash
clojure fix-schema.clj input.edn output.edn
```

Fixes applied:
- Adds missing `content-hash` fields (computed from statement)
- Converts keyword keys to string keys where required
- Extends short content hashes to 16 characters
- Adds missing `provenance` and `display-order` fields
- Ensures all required top-level keys exist

## Testing

The test suite covers 180+ test cases across all validators:

```bash
# Run all tests
clojure -M:test

# Run specific test namespace
clojure -M:test -n validate-graph.acyclicity-test
```

Test coverage includes:
- Valid graph structures (minimal, linear, diamond, scoped)
- All node types and justification rules
- Schema violations (invalid types, missing fields, wrong formats)
- Referential integrity errors
- Cycle detection (self-loops, direct cycles, long cycles)
- Scope violations
- Taint propagation errors
- Edge cases (empty graphs, large graphs, Unicode)

## Integration with Alethfeld

This tool is designed to validate proof graphs produced by the Alethfeld orchestrator:

```bash
# After running the orchestrator
clojure -M:run ../../examples/qbf-rank1/expanded.edn

# Before Lean formalization
clojure -M:run proof.edn && scripts/edn-to-lean.sh proof.edn
```

### CI/CD Integration

```yaml
# Example GitHub Actions step
- name: Validate proof graphs
  run: |
    cd scripts/validate-graph
    for f in ../../examples/**/*.edn; do
      clojure -M:run -q "$f" || exit 1
    done
```

## Configuration

Configuration constants are centralized in `src/validate_graph/config.clj`:

```clojure
;; Content hash length (must match schema regex)
(def content-hash-length 16)

;; Default context budget
(def default-max-tokens 100000)

;; Default proof mode
(def default-proof-mode :strict-mathematics)
```

## Dependencies

| Library | Version | Purpose |
|---------|---------|---------|
| `org.clojure/clojure` | 1.12.0 | Core language |
| `metosin/malli` | 0.16.4 | Schema validation |
| `org.clojure/tools.cli` | 1.1.230 | CLI argument parsing |
| `org.clojure/tools.logging` | 1.3.0 | Debug logging |

## License

MIT (same as parent Alethfeld project)

## See Also

- [Alethfeld README](../../README.md) - Project overview
- [Orchestrator Prompt](../../orchestrator-prompt-v4.md) - Schema specification
- [Proof Format Documentation](../../docs/proof-format.md) - Detailed format guide
