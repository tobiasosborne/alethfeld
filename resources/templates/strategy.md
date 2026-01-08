# Strategy Formulation Phase

## Current State

Developing a high-level proof strategy.

**Theorem:**
```
<THEOREM_STATEMENT>
```

**Iteration:** <N> of <LIMIT>

## Objectives

1. Identify the most promising proof approach
2. Anticipate potential obstacles
3. Assess the likelihood of success

## Strategy Considerations

### Approach Options
- Direct proof
- Proof by contradiction
- Mathematical induction
- Case analysis
- Construction

### Risk Assessment
- Where is the proof likely to get stuck?
- Are there non-trivial lemmas needed?
- Does the approach handle all edge cases?

### Prerequisites
- What supporting lemmas are needed?
- Are external references required?
- What assumptions must be made explicit?

## Expected Output

The adviser should provide:
```clojure
{:verdict [:enum :promising :risky :flawed :doomed]
 :assessment "2-3 sentences on viability"
 :weaknesses [{:issue "..." :severity :minor|:moderate|:critical}]
 :predicted-obstacles [{:step "..." :difficulty :technical|:conceptual|:open-problem}]
 :suggestions [{:type :restructure|:add-lemma|:change-approach :description "..."}]
 :confidence 0.0-1.0}
```

## State Transitions

- If verdict is `:promising` or `:risky` -> advance to **Skeleton**
- If verdict is `:flawed` and iterations remain -> retry **Strategy** with alternative approach
- If verdict is `:doomed` or iterations exhausted -> **Escalate** to user

## Structural Red Flags

Watch for:
- Induction on the wrong variable
- Case split that doesn't cover all cases
- "Without loss of generality" hiding non-trivial symmetry
- Quantifier ordering errors
- Hidden classical logic dependencies
