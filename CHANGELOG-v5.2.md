# Alethfeld v5.2 Changelog & Migration Guide

## Summary of Changes

v5.2 is a **non-breaking** update focused on eliminating ambiguity in control flow and CLI usage. Existing graphs remain compatible.

---

## Changelog

### Added

1. **Explicit State Machine (§VI)**
   - Full state transition diagram (§VI.1)
   - 30+ explicit transitions with conditions and actions (§VI.2)
   - States: `init`, `theorem-audit`, `strategy`, `skeleton`, `skeleton-review`, `decomposition`, `decomposition-eval`, `expand-verify-loop`, `expansion-step`, `verification-step`, `reference-check`, `reference-eval`, `finalization`, `complete`, `escalated`
   - Each transition specifies: from-state, condition, action, next-state

2. **Subagent Dispatch Protocol (§VI.3)**
   - Explicit template for spawning subagents
   - Mandatory input construction as EDN
   - Mandatory response parsing
   - Prohibition against assuming subagent roles

3. **Exhaustive CLI Reference (§IX)**
   - Complete signatures for all 12 commands (§IX.1)
   - Exit codes documented (§IX.2)
   - Common errors and solutions (§IX.3)
   - **Explicit list of non-existent flags** (§IX.4) — prevents `-o` confusion

4. **LaTeX Template Reference (§VII.7)**
   - Points to external `latex-template.tex`
   - Specifies placeholder replacement only
   - No structural modifications allowed

5. **Enhanced Progress Reporting (§VIII)**
   - Shows current state machine position
   - Shows previous and expected next states
   - Shows pending work queues

### Changed

1. **Verifier Response Format**
   - Added `:reject` verdict (separate from `:challenge`)
   - `:reject` = structural violation (immediate fail)
   - `:challenge` = semantic concern (needs expansion)

2. **Phase Names**
   - `verification` → `expand-verify-loop` (clearer semantics)
   - Added intermediate states: `skeleton-review`, `decomposition-eval`, `expansion-step`, `verification-step`, `reference-eval`

3. **LaTeX-er Specification**
   - Now references external template
   - Reduced inline specification to placeholder mapping only

### Fixed

1. **Control Flow Stalls**
   - Root cause: implicit transitions after Adviser
   - Fix: explicit "SPAWN Prover with {...}" actions in state machine

2. **CLI Flag Confusion**
   - Root cause: incomplete documentation
   - Fix: exhaustive signatures + explicit "these flags don't exist" section

---

## Migration Guide

### For Orchestrator Users

**No action required.** v5.2 is backward compatible with v5.1 graphs.

### For Prompt Engineers

1. **Update prompts** to v5.2 version
2. **Deploy `latex-template.tex`** alongside orchestrator prompt
3. **Update any tooling** that parses progress reports (new format in §VIII)

### For CLI Implementations

No changes to CLI behavior. v5.2 only documents existing behavior more precisely.

---

## File Manifest

```
alethfeld/
├── orchestrator-prompt-v5_2-claude.md   # Main orchestrator prompt
├── latex-template.tex                    # Canonical LaTeX template
└── CHANGELOG-v5.2.md                     # This file
```

---

## Testing Checklist

Before deploying v5.2, verify:

- [ ] State machine transitions correctly from `:strategy` to `:skeleton` after Adviser approval
- [ ] Prover is explicitly spawned (not assumed by orchestrator)
- [ ] No `-o` or other non-existent flags in CLI invocations
- [ ] LaTeX output matches template structure
- [ ] Progress reports show state machine position

---

## Known Limitations (to be addressed in v6)

1. **Single Verifier**: Still uses one verifier agent. v6 will introduce triple-verifier with voting.
2. **Late Decomposition**: Lemma extraction happens after expansion. v6 will move to subgraph-first.
3. **Embedded Finalizers**: LaTeX-er and Formalizer still in main prompt. v6 will separate them.
4. **No Backtracking**: Cannot checkpoint/restore graph state. Planned for v6.

---

## Version History

| Version | Date | Summary |
|---------|------|---------|
| v5.0 | 2024-11 | Initial release |
| v5.1 | 2024-12 | Anti-sycophancy, domain checks, theorem audit |
| v5.2 | 2025-01 | Explicit state machine, CLI docs, LaTeX template |

---

*End of Changelog. See `orchestrator-prompt-v5_2-claude.md` for full specification.*
