# Skeleton Review Phase

## Current State

Reviewing the proof skeleton for structural soundness.

**Theorem:**
```
<THEOREM_STATEMENT>
```

## Current Skeleton

The following depth-1 nodes have been constructed:

<LIST_OF_DEPTH_1_NODES>

## Review Objectives

1. Verify the skeleton covers all necessary cases
2. Check that the logical flow is sound
3. Identify structural weaknesses before expansion

## Evaluation Criteria

### Completeness
- Do the steps together establish the theorem?
- Are there missing cases or edge conditions?
- Is the case split exhaustive?

### Soundness
- Does each step follow from its dependencies?
- Are quantifiers handled correctly?
- Are there implicit assumptions?

### Structure
- Is the decomposition appropriate?
- Are steps at the right level of granularity?
- Will expansion be tractable?

## Expected Output

The adviser should provide:
```clojure
{:verdict [:enum :promising :risky :flawed :doomed]
 :assessment "2-3 sentences on skeleton quality"
 :weaknesses [{:issue "..." :severity :minor|:moderate|:critical}]
 :suggestions [{:type :restructure|:add-step|:remove-step :description "..."}]}
```

## State Transitions

- If verdict is `:promising` or `:risky` -> advance to **Decomposition**
- If verdict is `:flawed` and revisions remain -> return to **Skeleton** with feedback
- If revisions exhausted -> **Escalate** to user

## Warning Signs

- Steps that claim too much in one jump
- Missing boundary condition handling
- Circular reasoning patterns
- Over-reliance on external results
