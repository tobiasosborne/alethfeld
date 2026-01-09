# Glossary

Quick reference for Alethfeld terminology.

## Core Concepts

**Mote**
: The fundamental unit—a node in the proof graph representing a mathematical claim. Contains claim text, status, votes, assumptions, and metadata.

**DAG**
: Directed Acyclic Graph. The proof structure where motes are nodes and parent-child relationships are edges. Must remain acyclic.

**Claim**
: The mathematical statement a mote asserts. What needs to be proven or verified.

**Taint**
: A flag indicating what work a mote needs. Maps to agent roles. Examples: `:needs-verification`, `:needs-decomposition`.

## Identifiers

**Mote ID**
: Hierarchical dot-separated integers. Encodes ancestry. Example: `1.2.3` is child of `1.2`, grandchild of `1`.

**Session ID**
: Two concatenated UUIDs (256 bits). Uniquely identifies an agent's work session.

**Job ID**
: Timestamped identifier for a work assignment. Format: `job-YYYYMMDD-HHMMSS-XXXX`.

## Statuses

**proposed**
: Newly created, awaiting advisor approval.

**rejected**
: Proposal declined by advisors.

**fixed**
: Approved, awaiting verification votes.

**verified**
: Quorum of `:for` votes reached. Claim accepted.

**refuted**
: Quorum of `:against` votes reached. Claim rejected.

**contested**
: Conflicting votes without clear consensus.

## Roles

**proposer**
: Decomposes complex claims into sub-claims.

**advisor**
: Reviews and approves/rejects proposals.

**prover**
: Constructs formal proofs for claims.

**verifier**
: Casts verification votes on fixed claims.

**ref-checker**
: Validates external references.

**counterexample**
: Attempts to disprove claims by finding counterexamples.

## Workflow

**Job**
: A work assignment returned by `af ready`. Bundles mote, context, and role-specific prompt.

**Session**
: Binds an agent to a mote+role for a time window. Enforces action permissions.

**Quorum**
: The number of votes needed for a status change. Default: 3 for verification, 2 for proposals.

**Proposal**
: A suggested decomposition of a mote into children. Subject to advisor voting.

**Claim (verb)**
: Reserve a mote for work. Prevents duplicate effort. Expires after timeout.

## Data Types

**Assumption**
: A dependency declaration. Internal (references another mote) or external (outside knowledge).

**Definition**
: A symbol definition local to a mote. Maps symbol to meaning.

**Vote**
: A judgment cast by an agent. Types: `:for`, `:against`, `:approve`, `:reject`.

**Priority**
: Urgency level. `:p0` (critical) through `:p4` (someday).

**Difficulty**
: Complexity estimate. Integer 1 (trivial) through 5 (research-level).

## Infrastructure

**Transaction**
: An atomic operation that validates, writes, and commits. Provides ACID guarantees.

**Repository lock**
: Per-repo `ReentrantLock` serializing mutations.

**Race window**
: Brief period (~100ms) between validation and git commit where crash could leave uncommitted validated changes.

## Files

**config.edn**
: Repository configuration. Quorum thresholds, timeouts.

**motes/**
: Directory containing approved motes. Hierarchical structure mirrors IDs.

**proposed/**
: Directory containing pending proposal children.

**archive/**
: Directory containing rejected proposals.

**sessions/**
: Directory tracking active and completed agent sessions.

## Commands

**af init**
: Initialize repository with `.alethfeld/` structure.

**af ready**
: Get next job for an agent role.

**af vote**
: Cast verification vote.

**af propose**
: Create decomposition proposal.

**af approve / reject**
: Vote on proposal.

**af done**
: Complete current session.

**af sync**
: Pull, commit local changes, push.

**af check**
: Validate DAG integrity.
