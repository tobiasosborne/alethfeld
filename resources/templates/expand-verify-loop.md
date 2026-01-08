# Expand-Verify Loop Phase

## Current State

Iteratively expanding and verifying proof steps.

**Iteration:** <N> of <LIMIT>

## Subgraph Status

<SUBGRAPH_STATUS_LIST>

## Loop Mechanics

This phase alternates between:

1. **Expansion**: Prover adds substeps to proposed nodes
2. **Verification**: Verifier checks semantic validity of new steps

## Expansion Protocol

When expanding a step, the prover must:
- Provide inline substeps (never file references)
- Use only allowed justifications
- Cite all dependencies explicitly
- Handle all solution branches (optimization)

```clojure
{:steps
 [{:id :<id>
   :claim "..."
   :using [...]
   :justification :keyword
   :substeps [...]}]}
```

## Verification Protocol

The verifier checks each step for:

### Structural Issues (REJECT if present)
- Undefined references
- Out-of-scope assumptions
- Invalid justification types
- Circular dependencies

### Semantic Issues (CHALLENGE if present)
- Claim doesn't follow from cited references
- Justification rule misapplied
- Hidden quantifiers
- Domain restrictions without proof
- Incomplete optimization enumeration

## Verifier Responses

```clojure
{:step :<id> :verdict :accept}
{:step :<id> :verdict :challenge :reason "specific issue"}
{:step :<id> :verdict :reject :reason "structural violation"}
{:step :<id> :verdict :type-error :reason "A has type X, used as Y"}
```

## State Transitions

- If pending expansions exist -> expand next step
- If pending verifications exist -> verify next batch
- If all steps terminal -> advance to **Reference Check**
- If iteration limit reached -> mark remaining as :admitted, advance to **Reference Check**

## Anti-Sycophancy Reminder

Detecting an error is MORE VALUABLE than approving a flawed step. Challenge aggressively.
