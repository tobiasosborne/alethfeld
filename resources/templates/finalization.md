# Finalization Phase

## Current State

Generating final outputs from the verified proof.

**Current Status:** <CURRENT_STATUS>

## Objectives

1. Generate publication-quality LaTeX document
2. Create Lean 4 formalization skeleton
3. Compile obligation list for admitted steps

## Output Generation

### LaTeX Document

The LaTeX-er will produce a document with:
- Theorem statement
- Definitions section
- Extracted lemmas with proofs
- Main proof with numbered steps
- Obligations list (admitted steps)
- Bibliography from verified references

Status markers in LaTeX:
- `:verified` - no marker
- `:admitted` - `\admitted`
- `:tainted` - `\unverified`

### Lean 4 Skeleton

The Formalizer will produce:
- Import statements for Mathlib
- Variable declarations
- Lemma stubs with `sorry`
- Main theorem structure
- Taint annotations as comments

Taint handling:
- `:taint :clean, :status :verified` -> attempt proof term or sorry
- `:taint :self-admitted` -> `sorry -- ADMITTED`
- `:taint :tainted` -> `sorry -- TAINTED: <reason>`

### Obligations Report

List all `:admitted` nodes with:
- Node ID
- Claim statement
- Reason for admission
- Impact on proof taint

## CLI Operations

Final validation:
```bash
alethfeld validate graph.edn -v
alethfeld stats graph.edn
```

## Next Phase

After outputs are generated, advance to **Complete**.
