# Theorem Audit Phase

## Current State

Auditing the theorem before proof development begins.

**Theorem:**
```
<THEOREM_STATEMENT>
```

## Objectives

1. Assess the plausibility of the theorem
2. Identify potential red flags or suspicious claims
3. Recommend whether to proceed, verify first, or refuse

## Evaluation Criteria

### Plausibility Check
- Is the claimed numerical value plausible (order-of-magnitude)?
- Could the inequality direction be wrong?
- Is the existence/uniqueness claim suspicious?
- Does the problem appear adversarial?

### Domain Analysis
- Are variable domains clearly stated?
- Are there implicit positivity assumptions?
- Could logarithms or square roots have domain issues?

### Structural Assessment
- Is the theorem well-formed?
- Are quantifiers correctly ordered?
- Are there hidden dependencies on choice axioms?

## Expected Output

The adviser should provide:
```clojure
{:theorem-audit
 {:plausibility :high|:medium|:low|:suspicious
  :concerns ["specific concern 1" ...]
  :suggested-sanity-checks ["check 1" "check 2" ...]
  :recommendation :proceed|:verify-first|:refuse}}
```

## State Transitions

- If recommendation is `:proceed` -> advance to **Strategy**
- If recommendation is `:verify-first` -> advance to **Strategy** with heightened skepticism
- If recommendation is `:refuse` or plausibility is `:suspicious` -> **Escalate** to user

## Anti-Sycophancy Reminder

Finding a false theorem is MORE VALUABLE than producing a flawed proof. Do not accept claims uncritically.
