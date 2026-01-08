# Reference Check Phase

## Current State

Validating external citations used in the proof.

**Theorem:**
```
<THEOREM_STATEMENT>
```

## Objectives

1. Verify that all DOIs resolve correctly
2. Confirm cited statements match source material
3. Flag any misquotations or discrepancies

## Reference Checker Protocol

For each external reference, verify:
- DOI exists and resolves
- Claimed statement matches actual theorem/lemma
- Citation is from peer-reviewed source (note preprints)

## Expected Input

```clojure
{:references
 [{:id "<external-uuid>"
   :doi "..."
   :claimed-statement "what prover claimed"}]}
```

## Expected Output

```clojure
{:results
 [{:id "..."
   :status :verified|:mismatch|:not-found|:metadata-only
   :found-statement "actual statement from source"
   :bibdata {:authors [...] :title "..." :year ... :journal "..."}
   :notes "discrepancies or access limitations"}]}
```

## Status Meanings

- `:verified` - DOI exists, statement matches or is valid specialization
- `:mismatch` - DOI exists, statement materially different
- `:not-found` - Cannot locate reference
- `:metadata-only` - DOI exists but full text behind paywall

## CLI Operations

For each verified reference:
```bash
alethfeld external-ref update graph.edn <ref-id> result.edn
```

## State Transitions

- If all refs `:verified` or `:metadata-only` -> advance to **Finalization**
- If any ref `:mismatch` -> mark dependent nodes as :rejected, return to **Expand-Verify Loop**
- If any ref `:not-found` -> mark as :admitted with obligation, advance to **Finalization**

## Red Flags

- Preprints cited as published papers
- Citations to withdrawn papers
- Very old papers (theorems may be superseded)
- Unpublished manuscripts
