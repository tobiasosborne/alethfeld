# Data Model

All data structures are validated by Malli schemas defined in `schema.clj`. Invalid data is rejected before persistence.

## Mote

The fundamental unit—a node in the proof graph representing a mathematical claim.

```clojure
{:id            "1.2.3"                     ; Hierarchical identifier
 :claim         "For all ε > 0, there exists δ > 0 such that..."
 :status        :fixed                      ; Lifecycle state
 :taint         #{:needs-verification}      ; Work flags
 :priority      :p2                         ; Urgency
 :difficulty    3                           ; Complexity (1-5)

 ;; Hierarchy
 :parent        "1.2"                       ; Parent mote ID
 :children      ["1.2.3.1" "1.2.3.2"]       ; Approved child IDs

 ;; Content
 :assumptions   [{:type :internal :ref "1.1"}
                 {:type :external :desc "Axiom of Choice"}]
 :definitions   [{:symbol "ε" :meaning "error tolerance"}]
 :depends-on    [{:ref "1.2.1" :reason "Uses lemma on continuity"}]

 ;; Voting
 :votes         [{:agent "verifier-1" :vote :for :timestamp #inst "..."}]

 ;; Decomposition
 :proposal      {:id "prop-..." :children [...] :votes [...]}

 ;; Work tracking
 :claimed-by    "prover-1"
 :claimed-at    #inst "..."

 ;; Audit
 :created-by    "proposer-1"
 :created-at    #inst "..."
 :updated-at    #inst "..."
 :contributors  {:created-by "proposer-1"
                 :proposed-by "proposer-2"
                 :verified-by ["verifier-1" "verifier-2"]}}
```

### Status Lifecycle

```
proposed ──┬── approved ──→ fixed ──┬── quorum:for ──→ verified
           │                        │
           └── rejected             └── quorum:against ──→ refuted
                                    │
                                    └── mixed ──→ contested
```

| Status | Meaning |
|--------|---------|
| `proposed` | Awaiting advisor approval |
| `rejected` | Proposal declined |
| `fixed` | Approved, awaiting verification |
| `verified` | Quorum of :for votes reached |
| `refuted` | Quorum of :against votes reached |
| `contested` | Conflicting votes, needs review |

### Taint Flags

Taints signal what work a mote needs. Each maps to one or more roles.

| Taint | Role | Meaning |
|-------|------|---------|
| `:needs-decomposition` | proposer | Requires breakdown into sub-claims |
| `:needs-advisor-review` | advisor | Proposal awaiting approval |
| `:needs-proof` | prover | Needs formal proof |
| `:needs-verification` | verifier | Awaiting verification votes |
| `:needs-ref-check` | ref-checker | External references need validation |
| `:needs-counterexample` | counterexample | Suspected false, needs disproof |

### Priority

| Priority | Label | Meaning |
|----------|-------|---------|
| `:p0` | Critical | Blocks everything |
| `:p1` | High | Important dependency |
| `:p2` | Medium | Normal work |
| `:p3` | Low | Can wait |
| `:p4` | Someday | Backlog |

### Difficulty

Integer 1–5:
- **1:** Trivial—obvious or mechanical
- **2:** Easy—straightforward proof
- **3:** Medium—requires some insight
- **4:** Hard—significant work
- **5:** Research—open problem level

## Hierarchical IDs

IDs encode ancestry. Components are dot-separated integers.

```
1       → root
1.1     → first child of 1
1.2.3   → third child of second child of 1
1.2.3.4 → and so on
```

Operations in `id.clj`:

| Function | Example |
|----------|---------|
| `parse-id "1.2.3"` | `[1 2 3]` |
| `format-id [1 2 3]` | `"1.2.3"` |
| `parent-id "1.2.3"` | `"1.2"` |
| `child-id "1.2" 3` | `"1.2.3"` |
| `id-depth "1.2.3"` | `3` |
| `ancestor-ids "1.2.3"` | `("1" "1.2")` |
| `is-ancestor? "1" "1.2.3"` | `true` |

## Proposal

Represents a proposed decomposition of a mote into children.

```clojure
{:id          "prop-20260107-a7f3"
 :proposed-by "proposer-1"
 :proposed-at #inst "..."
 :children    ["1.2.1" "1.2.2" "1.2.3"]  ; Proposed child mote IDs
 :votes       [{:agent "advisor-1" :vote :approve}]
 :status      :pending}  ; :pending | :approved | :rejected
```

Children are atomic—all approved together or all rejected. They initially live in `proposed/` and move to `motes/` upon approval.

## Job

Work assignment returned by `af ready`. Bundles mote with context.

```clojure
{:job-id     "job-20260107-143052-a7f3"
 :mote-id    "1.2.3"
 :role       :verifier
 :difficulty 3
 :priority   :p1
 :mote       {...}        ; Full mote data
 :parent     {...}        ; Parent mote (context)
 :siblings   [...]        ; Sibling motes (context)
 :prompt     "You are a VERIFIER..."}
```

## Session

Binds an agent to a mote+role for a time window. Enforces action permissions.

```clojure
{:session-id "uuid1-uuid2"              ; 256-bit ID
 :mote-id    "1.2.3"
 :role       :verifier
 :agent      "verifier-1"
 :started-at #inst "..."
 :expires-at #inst "..."                ; Default 30 min
 :pid        12345                      ; Optional process ID
 :actions    [:vote]}                   ; Audit trail
```

### Role-Action Matrix

| Role | Allowed Actions |
|------|-----------------|
| proposer | `:propose`, `:add-child`, `:update-claim` |
| advisor | `:approve-proposal`, `:reject-proposal` |
| prover | `:add-proof`, `:add-assumption`, `:add-definition` |
| verifier | `:vote` |
| ref-checker | `:validate-ref`, `:add-ref` |
| counterexample | `:refute`, `:add-counterexample` |

Agents cannot act outside their role. Contributors cannot vote on their own work.

## Assumption

Dependencies on other claims.

```clojure
;; Internal: references another mote
{:type :internal
 :ref  "1.2.1"}

;; External: references outside knowledge
{:type :external
 :desc "Axiom of Choice"}
```

## Definition

Symbol definitions local to a mote.

```clojure
{:symbol  "ε"
 :meaning "error tolerance, a positive real number"}
```

## Vote

Verification or proposal vote.

```clojure
{:agent     "verifier-1"
 :vote      :for          ; :for | :against | :approve | :reject
 :timestamp #inst "..."
 :reason    "optional rationale"}
```

## Config

Repository configuration stored in `.alethfeld/config.edn`.

```clojure
{:project-name    "my-proof"
 :created-at      #inst "..."
 :quorum          {:verification 3    ; Votes needed for status change
                   :proposal 2}       ; Votes needed for proposal approval
 :claim-timeout   1800000             ; Claim expiry in ms (30 min)
 :session-timeout 1800000}            ; Session expiry in ms
```
