---
allowed-tools: Read, Bash, Glob
description: Validate semantic proof graph EDN files against the Alethfeld schema
---

# Semantic Proof Graph Validator

Validate EDN proof graph files against the Alethfeld protocol schema and semantic invariants.

## Input

The user will provide a file path to an EDN proof graph (`.edn`). If no path is provided, prompt for one or search for `.edn` files in the current directory.

## Validation Protocol

### 1. Run the Validator

```bash
./cli-legacy/scripts/alethfeld validate -v <path-to-edn-file>
```

The `-v` (verbose) flag provides detailed error information.

### 2. Interpret Results

**Exit codes:**
- `0` - Validation successful (all checks pass)
- `1` - Validation failed (schema or semantic errors)
- `2` - File error (not found, parse error, etc.)

### 3. Validation Checks Performed

**Schema Validation (Malli):**
- Node structure: `:id`, `:type`, `:statement`, `:content-hash`, `:dependencies`, `:scope`, `:justification`, `:status`, `:taint`, `:depth`, `:parent`, `:display-order`, `:provenance`
- Valid node types: `:assumption`, `:local-assume`, `:local-discharge`, `:definition`, `:claim`, `:lemma-ref`, `:external-ref`, `:qed`
- Valid justifications: 23 allowed keywords (`:modus-ponens`, `:universal-intro`, etc.)
- Valid statuses: `:proposed`, `:verified`, `:admitted`, `:rejected`
- Valid taint values: `:clean`, `:tainted`, `:self-admitted`
- Symbol, external-ref, lemma, and metadata structure

**Semantic Validation:**
- **Referential integrity**: All `:dependencies` reference existing nodes; all `:lemma-id` and `:external-id` references exist
- **Acyclicity**: No cycles in the dependency graph
- **Scope validity**: `:scope` entries are valid (undischarged ancestor `:local-assume` nodes)
- **Taint correctness**: `:taint` values match computed values based on `:status` and dependencies

## Output Format

On success:
```
OK: All validations passed
```

On failure, report:
```
VALIDATION FAILED: <filename>
================================

ERRORS:
- [<error-type>] <detailed message>
- ...

SUMMARY:
- Schema errors: <n>
- Semantic errors: <n>

RECOMMENDATIONS:
- <specific fixes for each error>
```

## Additional Options

If the user wants schema-only validation (skip semantic checks):
```bash
./scripts/alethfeld validate -s -v <path-to-edn-file>
```

If the user wants quiet output (just pass/fail):
```bash
./scripts/alethfeld validate -q <path-to-edn-file>
```

## When Validation Fails

1. Parse the error output carefully
2. Identify the specific node(s) causing issues
3. Explain what invariant is violated
4. Suggest concrete fixes with code examples if possible
