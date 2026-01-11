# Alethfeld v0.3 Revision Plan

**Date:** 2026-01-11
**Status:** Draft
**Goal:** Align AF with legacy alethfeld workflow while preserving agent-friendly design

---

## Executive Summary

The current `af` tool (v0.2.1) is well-engineered for multi-agent safety but suffers from **workflow rigidity** that frustrates agent use. The legacy alethfeld (v5.1) has a simpler, more natural **prover → verifier loop** that naturally incentivizes decomposition.

This plan proposes transforming AF to adopt legacy's flexibility while preserving AF's solid engineering foundation.

---

## Part 1: Problems with Current AF

### 1.1 The Proposer/Advisor Bottleneck

**Current flow:**
```
Create mote → Verifier says "needs decomposition" → Proposer creates proposal
→ Advisor(s) vote → Quorum reached → Children promoted → Verifiers vote
```

**Problem:** 4-5 steps just to decompose a claim. The advisor role adds gatekeeping without proportionate value.

### 1.2 Schema Poverty

| Element | Legacy Has | AF Lacks |
|---------|-----------|----------|
| Justification types | 20+ (modus-ponens, universal-elim, etc.) | Yes |
| Node types | 8 (assumption, claim, lemma-ref, qed...) | Yes |
| Symbol table | Graph-level | Yes |
| Lemma system | Built-in | Yes |
| Obligations tracking | Yes | Yes |
| Scope tracking | For local-assume/discharge | Yes |

### 1.3 Voting Overhead

- Quorum=2 means spawning multiple agents for every step
- Single-agent testing is painful
- Voting doesn't add value when agents can't truly be independent

### 1.4 Missing "Admitted" Status

- Legacy has `:admitted` with taint propagation
- AF has no working admission mechanism
- Terminal states have no recovery path

### 1.5 Verifier Role Mismatch

**Legacy:** Verifier can directly accept/challenge → naturally triggers decomposition

**AF:** Must wait for proposer → advisor approval → much less agency

---

## Part 2: Design Principles

### 2.1 Accretive, Non-Destructive

- **Add information, don't restructure**
- No deleting nodes, no archive directories
- Git handles all history
- Labeling over extraction

### 2.2 Git as Source of Truth

- Git provides integrity (no content hashes needed)
- Git provides history (no archive directories needed)
- Git provides ACID semantics
- Every mutation = git commit

### 2.3 LaTeX Convention

- All mathematical content in LaTeX
- Convention, not strict validation
- Prompts instruct agents to use LaTeX
- Enables future document generation

### 2.4 Verifier-Driven Decomposition

- Verifier decides: accept / challenge / decompose / admit
- Natural incentive: "If I can't verify it, break it down"
- No proposal/approval gatekeeping

---

## Part 3: Simplified Roles

### From 6 Roles to 3

| New Role | Responsibility | Replaces |
|----------|----------------|----------|
| **Prover** | Creates steps, decomposes when requested, adds refinements | proposer, prover |
| **Verifier** | Evaluates steps: accept/challenge/decompose/admit | verifier, advisor |
| **Checker** | Validates external refs, counterexamples (optional) | ref-checker, counterexample |

### Removed

- `proposer` → merged into `prover`
- `advisor` → eliminated (redundant gatekeeping)

---

## Part 4: Simplified Workflow

```
┌─────────────────────────────────────────────────────────────────┐
│                    SIMPLIFIED WORKFLOW                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. PROVER creates claim (with justification)                   │
│       │                                                         │
│       ▼                                                         │
│  2. VERIFIER evaluates claim                                    │
│       │                                                         │
│       ├─► ACCEPT → status = :verified                          │
│       │                                                         │
│       ├─► CHALLENGE → prover revises (back to step 2)          │
│       │                                                         │
│       ├─► DECOMPOSE → prover creates substeps                  │
│       │      └─► each substep goes to step 2                   │
│       │                                                         │
│       └─► ADMIT → status = :admitted (taints dependents)       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Key insight:** Verifier's "decompose" request is the natural driver. No proposal/approval dance.

---

## Part 5: Enriched Schema

### 5.1 Node Types

```clojure
(def NodeType
  [:enum
   :assumption        ; Global assumption (axiom, hypothesis)
   :local-assume      ; Local assumption (for discharge)
   :local-discharge   ; Discharges a local assumption
   :definition        ; Defines a symbol
   :claim             ; Mathematical claim requiring proof
   :lemma-ref         ; Reference to a labeled lemma
   :external-ref      ; Reference to external result
   :qed])             ; Final step completing proof
```

### 5.2 Justifications

```clojure
(def Justification
  [:enum
   ;; Structural
   :assumption :local-assumption :discharge :definition-expansion

   ;; Core inference
   :modus-ponens :universal-elim :universal-intro
   :existential-intro :existential-elim

   ;; Equality & algebra
   :substitution :equality-rewrite :algebraic-rewrite

   ;; Case analysis & induction
   :case-split :induction-base :induction-step

   ;; Propositional
   :contradiction
   :conjunction-intro :conjunction-elim
   :disjunction-intro :disjunction-elim
   :implication-intro

   ;; References
   :lemma-application :external-application

   ;; Special
   :admitted :qed])
```

### 5.3 Status (Simplified)

```clojure
(def Status
  [:enum
   :proposed   ; Awaiting verification
   :verified   ; Proven correct
   :admitted   ; Accepted without proof (taints dependents)
   :rejected]) ; Refuted or withdrawn
```

### 5.4 Taint (Legacy Style)

```clojure
(def Taint
  [:enum
   :clean          ; No issues
   :tainted        ; Depends on admitted/tainted node
   :self-admitted]) ; This node itself is admitted
```

### 5.5 Mote Schema (Malli)

```clojure
(def LaTeXString
  "String containing LaTeX mathematical notation."
  [:string {:min 1}])

(def Definition
  [:map
   [:symbol :string]
   [:meaning LaTeXString]
   [:tex {:optional true} :string]])

(def InternalRef
  [:map
   [:type [:= :internal]]
   [:ref MoteId]
   [:note {:optional true} :string]])

(def ExternalRef
  [:map
   [:type [:= :external]]
   [:ref :string]
   [:note {:optional true} :string]])

(def Assumption
  [:or InternalRef ExternalRef])

(def LemmaLabel
  [:map
   [:id :string]
   [:name :string]])

(def Mote
  [:map
   ;; Identity
   [:id MoteId]
   [:type NodeType]
   [:statement LaTeXString]
   [:justification Justification]
   [:status Status]
   [:taint Taint]

   ;; Structure
   [:parent {:optional true} MoteId]
   [:children [:vector MoteId]]
   [:dependencies [:set MoteId]]
   [:scope {:optional true} [:set MoteId]]

   ;; Content (LaTeX)
   [:definitions [:vector Definition]]
   [:assumptions [:vector Assumption]]

   ;; Lemma (accretive labeling)
   [:lemma {:optional true} LemmaLabel]

   ;; Work tracking
   [:priority Priority]
   [:difficulty Difficulty]
   [:claimed-by {:optional true} :string]
   [:claimed-at {:optional true} inst?]

   ;; Provenance
   [:created-by :string]
   [:created-at inst?]
   [:updated-at inst?]
   [:revision-of {:optional true} MoteId]])
```

**Example instance:**

```clojure
{:id            "1.2.3"
 :type          :claim
 :statement     "\\forall \\varepsilon > 0, \\exists \\delta > 0 \\ldots"
 :justification :modus-ponens
 :status        :proposed
 :taint         :clean

 :parent        "1.2"
 :children      ["1.2.3.1" "1.2.3.2"]
 :dependencies  #{"1.2.1" "1.2.2"}
 :scope         #{"1.1"}

 :definitions   [{:symbol "ε" :meaning "$\\varepsilon > 0$" :tex "\\varepsilon"}]
 :assumptions   [{:type :internal :ref "1.1" :note "Continuity assumption"}]

 :lemma         nil

 :priority      :p2
 :difficulty    3
 :claimed-by    nil
 :claimed-at    nil

 :created-by    "prover-1"
 :created-at    #inst "2026-01-11T10:00:00Z"
 :updated-at    #inst "2026-01-11T10:00:00Z"
 :revision-of   nil}
```

### 5.6 Graph-Level Metadata (Malli)

```clojure
(def Symbol
  [:map
   [:name :string]
   [:type {:optional true} :string]
   [:tex :string]])

(def Theorem
  [:map
   [:statement LaTeXString]
   [:status Status]])

(def LemmaIndex
  [:map
   [:node-id MoteId]
   [:name :string]])

(def Obligation
  [:map
   [:node-id MoteId]
   [:statement LaTeXString]
   [:reason {:optional true} :string]])

(def GraphMetadata
  [:map
   [:graph-id :string]
   [:version [:int {:min 0}]]
   [:theorem Theorem]
   [:symbols [:map-of :string Symbol]]
   [:lemmas [:map-of :string LemmaIndex]]
   [:obligations [:vector Obligation]]])
```

**Example instance:**

```clojure
;; In config.edn or separate graph.edn
{:graph-id      "550e8400-e29b-41d4-a716-446655440000"
 :version       1
 :theorem       {:statement "\\sqrt{2} \\text{ is irrational}" :status :proposed}
 :symbols       {"ε" {:name "epsilon" :type "ℝ⁺" :tex "\\varepsilon"}
                 "δ" {:name "delta" :type "ℝ⁺" :tex "\\delta"}}
 :lemmas        {"L1" {:node-id "1.2.3" :name "Continuity Lemma"}}
 :obligations   [{:node-id "1.4" :statement "..." :reason "Assumed without proof"}]}
```

---

## Part 6: Command Changes

### 6.1 New Commands

```bash
# Prover creates substeps directly (no proposal/approval)
af decompose <id> --claim "Step 1" --claim "Step 2" --session <token>

# Unified verifier actions
af verify <id> --accept --reason "..." --session <token>
af verify <id> --challenge --reason "..." --session <token>
af verify <id> --decompose --reason "..." --session <token>
af verify <id> --admit --reason "..." --session <token>

# Accretive lemma labeling
af lemma <id> --name "Lemma Name"
af lemma <id> --remove
af lemmas                              # List all lemmas

# Symbol table
af symbol add --name "ε" --type "ℝ⁺" --tex "\\varepsilon"
af symbol list
af symbol remove "ε"

# Role listing (UX improvement)
af roles                               # Show valid roles
```

### 6.2 Modified Commands

```bash
# Create with richer schema
af create <parent> --claim "LaTeX..." \
  --type claim \
  --justification modus-ponens \
  --using 1.2.1 1.2.2 \
  --session <token>

# Vote simplified (single verifier by default)
af vote <id> --for --reason "..." --session <token>
af vote <id> --against --reason "..." --session <token>
```

### 6.3 Removed/Deprecated Commands

| Command | Status | Replacement |
|---------|--------|-------------|
| `af propose` | Removed | `af decompose` |
| `af approve` | Removed | N/A (no approval needed) |
| `af reject` | Removed | N/A (no approval needed) |

### 6.4 Role Mapping

| Old Role | New Role |
|----------|----------|
| proposer | prover |
| advisor | (eliminated) |
| prover | prover |
| verifier | verifier |
| ref-checker | checker |
| counterexample | checker |

---

## Part 7: Taint Propagation

### 7.1 Rules

```clojure
(defn compute-taint [node graph]
  (cond
    ;; Self-admitted
    (= (:status node) :admitted)
    :self-admitted

    ;; Depends on tainted/admitted node
    (some #(#{:tainted :self-admitted}
            (:taint (get-node graph %)))
          (:dependencies node))
    :tainted

    ;; Clean
    :else :clean))
```

### 7.2 Propagation

When a node's taint changes, recompute taint for all dependents (transitive).

### 7.3 Obligations

When a node is admitted:
1. Set status to `:admitted`
2. Set taint to `:self-admitted`
3. Add to graph `:obligations` list
4. Propagate taint to all dependents

---

## Part 8: Migration Strategy

### 8.1 Schema Version

```clojure
;; config.edn
{:schema-version 3
 :project-name "..."
 ...}
```

### 8.2 Migration Command

```bash
af migrate                             # Upgrade v0.2 → v0.3
```

**Migration steps:**
1. Add `:type :claim` to all motes (default)
2. Add `:justification :assumption` to root motes
3. Add `:taint :clean` to all verified motes
4. Convert `:status :fixed` → `:status :proposed`
5. Remove `:proposal` fields
6. Update config schema version

### 8.3 Backward Compatibility

- Old commands (`propose`, `approve`, `reject`) show deprecation warning
- Old motes readable, upgraded on first write
- Tests updated incrementally

---

## Part 9: Configuration Changes

### 9.1 New Config Options

```clojure
{:schema-version      3
 :project-name        "My Proof"
 :version             "0.1"

 ;; Defaults
 :default-difficulty  3
 :default-priority    :p2

 ;; Verification (simplified)
 :vote-quorum         1              ; Default: single verifier
 :claim-timeout-minutes 30
 :session-timeout-minutes 30

 ;; Graph metadata
 :symbols             {}             ; Symbol table
 :obligations         []}            ; Admitted nodes needing proof
```

### 9.2 Removed Config

- `:proposal-quorum` (no proposals)

---

## Part 10: Implementation Phases

### Phase 1: Workflow Simplification (Week 1-2)

**Priority: CRITICAL**

- [ ] Add `af decompose` command
- [ ] Add `af verify` with `--accept/--challenge/--decompose/--admit` modes
- [ ] Remove proposal system entirely
- [ ] Merge proposer into prover role
- [ ] Eliminate advisor role
- [ ] Set default vote-quorum to 1
- [ ] Update prompts for new workflow

### Phase 2: Admitted Status (Week 2)

**Priority: HIGH**

- [ ] Add `:admitted` status
- [ ] Implement taint propagation (`:clean`, `:tainted`, `:self-admitted`)
- [ ] Add `:obligations` tracking
- [ ] Add `af admit` command (or `af verify --admit`)

### Phase 3: Schema Enrichment (Week 3-4)

**Priority: MEDIUM**

- [ ] Add `:type` field (node types)
- [ ] Add `:justification` field
- [ ] Add `:dependencies` field
- [ ] Add `:scope` field
- [ ] Add graph-level `:symbols` table
- [ ] Update `af create` with `--type`, `--justification`, `--using`

### Phase 4: Lemma System (Week 4)

**Priority: MEDIUM**

- [ ] Add `:lemma` field (accretive labeling)
- [ ] Add `af lemma` command
- [ ] Add graph-level lemma index
- [ ] Support `:lemma-application` justification

### Phase 5: UX Improvements (Ongoing)

**Priority: LOW**

- [ ] Add `af roles` command
- [ ] Implicit session support (environment variable)
- [ ] Better error messages with suggestions
- [ ] Role aliases (reviewer → verifier)

---

## Part 11: What We're NOT Doing

### 11.1 Removed from Original Plan

| Feature | Reason |
|---------|--------|
| Content hash | Git handles integrity |
| Archive directory | Git is the archive |
| Lemma extraction (delete/replace) | Accretive labeling instead |
| Strict LaTeX validation | Convention only, trust agents |
| Complex dependency rewriting | Keep IDs stable, no rewriting |

### 11.2 Deferred to Later

| Feature | Reason |
|---------|--------|
| LaTeXer role | Trivial once schema is LaTeX |
| Leanifier role | Separate tool, different expertise |
| External ref checker | Can be added as checker mode |
| Multi-graph references | Complexity, unclear need |

---

## Part 12: Success Criteria

### 12.1 Workflow

- [ ] Single proof step: create → verify takes 2 commands (not 5+)
- [ ] Decomposition: verify --decompose → decompose takes 2 commands
- [ ] No advisor bottleneck
- [ ] Single-agent testing works naturally

### 12.2 Schema

- [ ] All nodes have type and justification
- [ ] Taint propagates correctly
- [ ] Admitted status works with obligations
- [ ] Lemmas are just labeled nodes

### 12.3 Agent Experience

- [ ] Agents can complete sqrt(2) proof in <30 commands (was 76)
- [ ] Role discovery is immediate (`af roles`)
- [ ] Error messages suggest valid alternatives

---

## Appendix A: Command Reference (v0.3)

```
af init [--name <name>]                    Initialize project

af create --root --claim "LaTeX"           Create root mote
af create <parent> --claim "LaTeX"         Create child mote
  [--type <type>]                          Node type (default: claim)
  [--justification <just>]                 Justification (default: assumption for root)
  [--using <id> ...]                       Dependencies
  [--session <token>]

af decompose <id>                          Create substeps
  --claim "LaTeX" [--difficulty N] ...     One or more claims
  --session <token>

af verify <id>                             Evaluate a claim
  --accept | --challenge | --decompose | --admit
  --reason "..."
  --session <token>

af vote <id> --for|--against               Cast verification vote
  --reason "..."
  --session <token>

af lemma <id> --name "Name"                Label node as lemma
af lemma <id> --remove                     Remove lemma label
af lemmas                                  List all lemmas

af symbol add --name "ε" --tex "\\varepsilon" --type "ℝ⁺"
af symbol list
af symbol remove "ε"

af show <id>                               Display mote
af tree [<id>]                             Display proof tree
af status                                  Project summary

af ready [--role <role>] [--name <agent>]  Get next job
af claim <id> --role <role> --name <agent> Claim mote
af done --session <token>                  End session

af check                                   Validate DAG
af sync                                    Git pull/commit/push
af roles                                   List valid roles
af migrate                                 Upgrade schema
```

---

## Appendix B: Comparison with Legacy

| Feature | Legacy (v5.1) | AF v0.2 | AF v0.3 (Proposed) |
|---------|---------------|---------|---------------------|
| Roles | Prover, Verifier, Adviser | 6 roles | 3 roles (Prover, Verifier, Checker) |
| Decomposition | Prover proposes, Verifier challenges | Proposal → Approval | Verifier requests → Prover creates |
| Voting | Single verifier | Quorum-based | Optional quorum (default=1) |
| Admitted status | Yes, with taint | Missing | Yes, with taint |
| Node types | 8 types | None | 8 types |
| Justifications | 20+ rules | None | 20+ rules |
| Symbol table | Graph-level | Per-mote | Graph-level |
| Lemmas | Extract/archive | None | Accretive labeling |
| Content hash | Yes | No | No (git handles) |
| Archive directory | Yes | No | No (git handles) |
| Git backing | Optional | Required | Required |

---

## Appendix C: Example Session (v0.3)

```bash
# Initialize
$ af init --name "Sqrt2 Irrational"

# Create root theorem
$ af create --root --claim "$\\sqrt{2}$ is irrational" --name prover1
{:id "1" :status :proposed ...}

# Verifier requests decomposition
$ af ready --role verifier --name verifier1
{:job-id "..." :mote-id "1" ...}

$ af verify 1 --decompose --reason "Needs proof by contradiction" --session <token>
$ af done --session <token>

# Prover decomposes
$ af ready --role prover --name prover1
{:job-id "..." :mote-id "1" ...}

$ af decompose 1 \
    --claim "Assume $\\sqrt{2} = p/q$ in lowest terms" --difficulty 1 \
    --claim "Then $p^2 = 2q^2$" --difficulty 2 \
    --claim "If $p^2$ is even, then $p$ is even" --difficulty 2 \
    --claim "Let $p = 2k$, substitution shows $q$ is even" --difficulty 2 \
    --claim "Contradiction: $\\gcd(p,q) \\neq 1$" --difficulty 1 \
    --session <token>
$ af done --session <token>

# Verifier accepts each substep
$ af ready --role verifier --name verifier1
$ af verify 1.1 --accept --reason "Valid assumption for contradiction" --session <token>
$ af done --session <token>

# Verifier sees 1.3 is a reusable result (even square implies even root)
# Requests decomposition for proper proof
$ af verify 1.3 --decompose --reason "Needs standalone proof" --session <token>
$ af done --session <token>

# Prover provides substeps for 1.3
$ af decompose 1.3 \
    --claim "Contrapositive: if $p$ is odd, then $p^2$ is odd" --difficulty 1 \
    --claim "Odd squared: $(2m+1)^2 = 4m^2 + 4m + 1 = 2(2m^2+2m) + 1$" --difficulty 1 \
    --session <token>
$ af done --session <token>

# Verify the substeps of 1.3
$ af verify 1.3.1 --accept --reason "Valid contrapositive" --session <token>
$ af verify 1.3.2 --accept --reason "Algebraic identity correct" --session <token>
$ af done --session <token>

# Now 1.3 is fully verified - label it as a reusable lemma
$ af lemma 1.3 --name "Even Square Lemma"

# ... verify remaining substeps 1.2, 1.4, 1.5 ...

# Verify root theorem (all children verified)
$ af verify 1 --accept --reason "Contradiction established" --session <token>

# Check final state
$ af status
Project: Sqrt2 Irrational
Theorem: $\sqrt{2}$ is irrational [verified]
Motes: 8 (8 verified, 0 proposed, 0 admitted)
Lemmas: 1 (Even Square Lemma @ 1.3)
Obligations: 0

$ af lemmas
L1: "Even Square Lemma" @ 1.3
    Statement: If $p^2$ is even, then $p$ is even
    Status: verified
    Taint: clean
```

**Key points:**
- The **theorem** (root mote 1) is the main claim being proved
- A **lemma** is an internal mote (1.3) labeled for reuse
- Lemma labeling is accretive - just adds `:lemma` field, doesn't change the mote's role in the proof
- The lemma can be referenced by other proofs via `--using 1.3` or by lemma name

**Total commands:** ~20 (vs 76 in v0.2 agent test)
