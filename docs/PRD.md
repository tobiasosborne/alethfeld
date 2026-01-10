# Alethfeld: Product Requirements Document

**Version:** 0.2
**Date:** January 2026

---

## Vision

Alethfeld is a collaborative proof verification system where AI agents swarm a mathematical argument, decomposing claims, checking references, finding counterexamples, and building consensus on correctness. Human mathematicians set the goal; agents do the grunt work.

## Problem

Mathematical proofs are hard to verify at scale. A single researcher can't exhaustively check every step, citation, and edge case. Existing tools (Lean, Coq) require formal encoding upfront—too slow for exploratory work. We need a middle ground: structured argumentation with adversarial verification, without full formalization.

## Solution

A CLI tool (`af`) that manages a DAG of proof steps ("motes"). Agents query for work, receive a mote + role + prompt, do their job, check in results. Git provides ACID transactions and history. No database, no server, no setup.

## User Stories

**As a mathematician**, I create a root mote with my conjecture. I run `af ready` periodically to see progress. Agents decompose, verify, and flag issues. I intervene only when agents get stuck or find real problems.

**As a proposer agent**, I receive a mote needing decomposition. I break it into 2-5 substeps that together prove the parent claim. My proposal goes to advisors for review.

**As an advisor agent**, I review a proposed decomposition. I check: do the substeps cover all cases? Are there gaps? I vote approve or reject. Rejected proposals get archived; the proposer tries again.

**As a verifier agent**, I receive a fixed mote. I check if the substeps logically entail the claim. I vote for or against, with reasoning.

**As a ref-checker agent**, I validate external citations. Does arXiv:2301.00001 actually say what the mote claims? I flag misquotations.

**As a counterexample agent**, I try to break the claim. I look for edge cases, boundary conditions, vacuous truths. If I find one, the mote is refuted.

**As a swarm orchestrator**, I run `af ready --max 20` to get a batch of jobs, dispatch them to agents running in parallel, collect results. Agents work on 5-10 minute timescales; I poll and reassign as needed.

## Scope

### In Scope (v0.1)
- CLI tool `af` with subcommands: init, ready, show, create, propose, approve, reject, update, vote, claim, unclaim, taint, check, sync
- Motes stored as EDN files, one per mote
- Git for persistence, history, sync
- Role-based work dispatch with prompts
- Priority (p0-p4) and difficulty (1-5) filtering
- Atomic proposal sets (approve/reject children together)
- EDN output (JSON fallback)

### Out of Scope (v0.1)
- LaTeX rendering
- Lean/Coq integration  
- Web UI
- SQLite caching
- Multi-repo federation
- Real-time collaboration
- Authentication/permissions

## Success Criteria

1. A single agent can take a 10-step proof from conjecture to verified in under 1 hour
2. Multiple agents can work in parallel without conflicts
3. A human can understand the proof state by reading EDN files directly
4. Full history is recoverable via `git log`

## Risks

| Risk | Mitigation |
|------|------------|
| Agents produce incoherent decompositions | Advisor review gate; rejection triggers retry |
| Circular dependencies in mote graph | DAG validation on every write |
| Git merge conflicts | One file per mote minimizes conflicts; atomic commits |
| Agents get stuck in loops | Claim timeout; manual intervention flag |

## Timeline

- **Day 1**: Core CLI (init, show, ready, create), file I/O, schemas
- **Day 2**: Proposal workflow (propose, approve, reject), voting
- **Day 3**: Work dispatch with prompts, sync, polish

## Future Directions

- Lean export: generate formal proof sketches from verified mote trees
- LaTeX export: render proof as readable document
- Federation: cross-repo references for large collaborative proofs
- Reputation: track agent accuracy over time
