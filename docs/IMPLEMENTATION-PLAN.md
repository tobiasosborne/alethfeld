# Alethfeld Implementation Plan

**Approach:** Test-driven, purely functional where possible
**Chunk size:** Each step implementable in ~20% context (~20K tokens)
**Language:** Clojure

---

# Part I: v0.1 Core (COMPLETED)

> All 28 steps completed. 746 tests, 1926 assertions passing.

## Phase 0: Project Setup (COMPLETED)

### Step 0.1: Repository & Build Structure
- Create project directory structure
- Create `deps.edn` with dependencies (malli, data.json, babashka/process, babashka/fs)
- Create `build.clj` for uberjar compilation
- Create `.gitignore`
- Create `README.md` stub
- Create `CLAUDE.md` with project conventions

**Deliverables:** Empty project that runs `clj -M:run` without error

### Step 0.2: Test Infrastructure
- Set up `test/` directory structure mirroring `src/`
- Add `cognitect/test-runner` to deps.edn
- Create test runner alias `:test`
- Create first dummy test to verify infrastructure
- Document test conventions in `CLAUDE.md`

**Deliverables:** `clj -M:test` runs and passes

---

## Phase 1: Core Data Model (COMPLETED)

### Step 1.1: Schema Definitions + Validation Tests
### Step 1.2: Mote Constructor Functions + Tests
### Step 1.3: Mote Transformation Functions + Tests

---

## Phase 2: DAG Operations (COMPLETED)

### Step 2.1: ID Operations + Tests
### Step 2.2: Path Derivation + Tests
### Step 2.3: DAG Validation + Tests

---

## Phase 3: Job Selection (COMPLETED)

### Step 3.1: Role Derivation + Tests
### Step 3.2: Job Selection Algorithm + Tests
### Step 3.3: Prompt Rendering + Tests

---

## Phase 4: File I/O (COMPLETED)

### Step 4.1: EDN I/O + Tests
### Step 4.2: Mote Persistence + Tests
### Step 4.3: Git Operations + Tests

---

## Phase 5: Transaction Layer (COMPLETED)

### Step 5.1: Transaction Wrapper + Tests
### Step 5.2: Proposal Workflow + Tests
### Step 5.3: Verification Workflow + Tests

---

## Phase 6: CLI Commands (COMPLETED)

### Step 6.1: CLI Infrastructure + Tests
### Step 6.2: Init & Show Commands + Tests
### Step 6.3: Create Command + Tests
### Step 6.4: Ready Command + Tests
### Step 6.5: Propose/Approve/Reject Commands + Tests
### Step 6.6: Update/Vote/Taint Commands + Tests
### Step 6.7: Claim/Unclaim Commands + Tests
### Step 6.8: Add-* Commands + Tests
### Step 6.9: Check/Log/Sync Commands + Tests

---

## Phase 7: Integration & Polish (COMPLETED)

### Step 7.1: End-to-End Integration Tests
### Step 7.2: Error Handling & Messages
### Step 7.3: Build & Distribution
### Step 7.4: Documentation

---

# Part II: v0.2 Session Enforcement & UX

> Based on testing feedback from proving sqrt(2) irrationality.
> Critical design requirement: enforce role-based workflow, prevent self-voting.

---

## Phase A: Session & Role Enforcement (CRITICAL)

This phase introduces **breaking changes** to all mutation commands. After this phase, agents must obtain a session via `af ready` or `af claim` before performing any mutations. This enforces:

1. **Role-based actions**: Verifiers can't propose, provers can't vote
2. **Self-vote prevention**: Can't vote on work you created/proposed/refined
3. **Workflow discovery**: Agents use `af ready` to find work
4. **Low-context swarm**: One agent per mote, minimal context per agent

### Step A.1: Session Schema & Storage

**Goal:** Define session data model and persistence layer.

- Create `src/alethfeld/session.clj`
- Add `Session` schema to `schema.clj`:
  ```clojure
  (def Session
    [:map
     [:session-id :string]           ; Dual-UUID, cryptographically random
     [:mote-id MoteId]
     [:role Role]
     [:agent :string]
     [:started-at inst?]
     [:expires-at inst?]             ; Default: 30 minutes
     [:pid {:optional true} :int]    ; For crash detection
     [:actions [:vector :keyword]]]) ; Audit trail
  ```
- Implement session ID generation (dual UUID = 256 bits entropy):
  ```clojure
  (defn generate-session-id []
    (str (java.util.UUID/randomUUID) "-" (java.util.UUID/randomUUID)))
  ```
- Add session directory structure to `path.clj`:
  - `sessions/active/<session-id>.edn`
  - `sessions/completed/<session-id>.edn`
- Implement in `session.clj`:
  - `create-session!`: Create new session file
  - `load-session`: Load session by ID
  - `load-all-sessions`: Load all active sessions
  - `end-session!`: Move to completed, clear mote claim
  - `archive-session!`: Move expired/crashed session to completed
- Create `test/alethfeld/session_test.clj`
- Write tests: CRUD operations, session ID format, expiration

**Deliverables:** Session persistence layer with tests

### Step A.2: Role-Action Matrix

**Goal:** Define which roles can perform which actions.

- Add role-action matrix to `session.clj`:
  ```clojure
  (def role-actions
    {:proposer      #{:propose :add-definition :add-assumption :add-ref :done}
     :advisor       #{:approve :reject :done}
     :prover        #{:propose :add-definition :add-assumption :add-ref
                      :taint-remove :done}
     :verifier      #{:vote :taint-add :done}
     :ref-checker   #{:add-ref :taint-remove :done}
     :counterexample #{:vote :update-status :done}})
  ```
- Add sessionless commands set:
  ```clojure
  (def sessionless-commands
    #{:init :ready :show :tree :status :check :log :help :config})
  ```
- Implement `allowed?` predicate:
  ```clojure
  (defn allowed? [role action]
    (contains? (get role-actions role) action))
  ```
- Write tests: each role can/cannot perform expected actions

**Deliverables:** Role-action enforcement logic with tests

### Step A.3: Contributors Tracking & Self-Vote Prevention

**Goal:** Track who touched a mote to prevent self-voting.

- Add `:contributors` field to Mote schema:
  ```clojure
  [:contributors {:optional true}
   [:map
    [:created-by :string]
    [:proposed-by {:optional true} :string]
    [:refined-by {:optional true} [:set :string]]
    [:refs-checked-by {:optional true} [:set :string]]]]
  ```
- Update mote constructors in `mote.clj` to initialize contributors
- Update `proposal.clj` to set `:proposed-by` when proposal created
- Update add-* functions to add agent to `:refined-by`
- Implement `can-vote?` predicate in `session.clj`:
  ```clojure
  (defn can-vote? [mote agent]
    (let [{:keys [created-by proposed-by refined-by]} (:contributors mote)]
      (and (not= agent created-by)
           (not= agent proposed-by)
           (not (contains? (or refined-by #{}) agent)))))
  ```
- Update `cast-vote!` in `verify.clj` to check `can-vote?`
- Write tests: self-vote scenarios rejected

**Deliverables:** Contributors tracking, self-vote prevention with tests

### Step A.4: Session Creation in Ready/Claim

**Goal:** Create sessions when agents claim work.

- Update `cmd-ready` in `cmd.clj`:
  - When `--agent` provided (claiming), create session
  - Require `--role` when claiming
  - Return session token in output
  - Update output format to include session info
- Update `cmd-claim` in `cmd.clj`:
  - Add `--role` flag (required)
  - Create session on claim
  - Return session token
- Session creation flow:
  1. Validate mote not already claimed (or claim expired)
  2. Generate cryptographically secure session ID
  3. Write session file to `sessions/active/`
  4. Update mote with `claimed-by`, `claimed-at`, `:active-session`
  5. Return session token to agent
- Write tests: claim creates session, session token returned

**Deliverables:** Session creation on claim with tests

### Step A.5: Session Enforcement Middleware

**Goal:** All mutation commands require valid session.

- Create `enforce-session!` function in `session.clj`:
  ```clojure
  (defn enforce-session! [session-id action mote-id]
    (let [session (load-session session-id)]
      (cond
        (nil? session)
        (throw (ex-info "Invalid session" {:session-id session-id}))

        (expired? session)
        (throw (ex-info "Session expired" {:session-id session-id}))

        (not= mote-id (:mote-id session))
        (throw (ex-info "Session locked to different mote" {...}))

        (not (allowed? (:role session) action))
        (throw (ex-info "Action not allowed for role" {...}))

        :else
        (do (record-action! session-id action)
            session))))
  ```
- Add `--session` flag to all mutation commands in `cli.clj`:
  - `propose`, `approve`, `reject`, `vote`, `taint`, `update`
  - `add-ref`, `add-assumption`, `add-definition`
  - `claim`, `unclaim`
- Update each `cmd-*` function to:
  1. Check if command is sessionless (skip enforcement)
  2. Call `enforce-session!` before executing
  3. Record action in session audit trail
- Write tests: commands without session rejected, wrong role rejected

**Deliverables:** Session enforcement on all mutations with tests

### Step A.6: Done Command

**Goal:** Clean session termination.

- Add `cmd-done` in `cmd.clj`:
  ```bash
  af done --session <token>
  ```
- Implementation:
  1. Load session
  2. Clear mote claim (`claimed-by`, `claimed-at`, `:active-session`)
  3. Move session file to `sessions/completed/`
  4. Record completion timestamp and final action count
  5. Git commit the changes
- Write tests: done ends session, mote claimable again

**Deliverables:** `af done` command with tests

### Step A.7: Stale Session Cleanup

**Goal:** Recover from crashed agents.

- Implement `cleanup-stale-sessions!` in `session.clj`:
  ```clojure
  (defn cleanup-stale-sessions! [repo-path]
    (doseq [session (load-all-sessions repo-path)]
      (when (or (expired? session)
                (not (pid-alive? (:pid session))))
        (let [mote-id (:mote-id session)]
          ;; Release the mote
          (clear-mote-claim! repo-path mote-id)
          ;; Archive the session
          (archive-session! repo-path session)))))
  ```
- Call `cleanup-stale-sessions!` at start of `cmd-ready`
- Implement `pid-alive?` using `babashka/process`
- Write tests: expired sessions cleaned up, crashed agent sessions released

**Deliverables:** Stale session cleanup with tests

### Step A.8: Prompt Updates with Session Constraints

**Goal:** Prompts tell agents exactly what they can do.

- Update all prompt templates in `prompt.clj` to include:
  ```
  SESSION: {{session-id}}
  MOTE: {{mote-id}}
  ROLE: {{role}}

  ALLOWED COMMANDS:
  {{#allowed-commands}}
    af {{command}} {{mote-id}} ... --session {{session-id}}
  {{/allowed-commands}}

  FORBIDDEN (your role cannot):
  {{#forbidden-actions}}
    - {{action}} ({{role-that-can}} only)
  {{/forbidden-actions}}

  When finished: af done --session {{session-id}}
  ```
- Update `render-prompt` to accept session context
- Update `build-job` to include session in job
- Write tests: prompts include session info, correct allowed/forbidden lists

**Deliverables:** Updated prompts with session constraints, tests

---

## Phase B: Tier 1 Essential Improvements

Based on testing feedback: immediate usability pain points.

### Step B.1: Configurable Quorum

**Goal:** Allow solo workflows with quorum=1.

- Update Config schema in `schema.clj`:
  ```clojure
  (def Config
    [:map
     [:project-name :string]
     [:version :string]
     [:default-difficulty Difficulty]
     [:proposal-quorum {:optional true} [:int {:min 1}]]  ; default 2
     [:verify-quorum {:optional true} [:int {:min 1}]]    ; default 2
     [:claim-timeout-minutes {:optional true} :int]])
  ```
- Add `cmd-config` in `cmd.clj`:
  ```bash
  af config set proposal-quorum 1
  af config set verify-quorum 1
  af config get quorum
  af config list
  ```
- Update `check-proposal-quorum` in `proposal.clj` to read from config
- Update `check-verification-quorum` in `verify.clj` to read from config
- Write tests: quorum=1 allows single-agent approval/verification

**Deliverables:** `af config` command, configurable quorum with tests

### Step B.2: Tree View Command

**Goal:** Visualize proof structure at a glance.

- Add `cmd-tree` in `cmd.clj`:
  ```bash
  af tree <id> [--depth <n>]
  ```
- Output format:
  ```
  1 [verified] The square root of 2 is irrational
  +-- 1.1 [verified] Assumption for contradiction...
  +-- 1.2 [verified] From sqrt(2) = p/q...
  +-- 1.3 [verified] Lemma: If n^2 is even...
  |   +-- 1.3.1 [verified] Prove contrapositive...
  |   +-- 1.3.2 [verified] If n odd, n = 2m + 1
  |   +-- 1.3.3 [verified] n^2 = 4m^2 + 4m + 1
  +-- 1.4 [verified] p^2 even -> p even (by 1.3)
  ```
- Implement recursive tree rendering with:
  - Status indicators: `[verified]`, `[fixed]`, `[proposed]`, etc.
  - Taint indicators: `(needs-decomposition)`, etc.
  - ASCII connectors: `+--`, `|   `, `\--`
  - Depth limiting with `--depth` flag
- Write tests: tree rendering, depth limiting, nested structures

**Deliverables:** `af tree` command with tests

### Step B.3: Status Summary Command

**Goal:** Quick overview of proof progress.

- Add `cmd-status` in `cmd.clj`:
  ```bash
  af status
  ```
- Output format:
  ```
  Project: sqrt2-irrationality
  Root motes: 1
  Total motes: 10

  Status breakdown:
    verified:  10 (100%)
    fixed:      0
    proposed:   0
    contested:  0

  Taints:
    needs-decomposition: 0
    needs-verification:  0
    needs-refs:          0

  Active sessions: 2
  Ready for work: 0 motes
  ```
- Implementation:
  - Load all motes
  - Count by status
  - Count by taint
  - Count active sessions
  - Calculate "ready for work" (workable motes)
- Write tests: status aggregation correct

**Deliverables:** `af status` command with tests

### Step B.4: Human-Readable Error Messages

**Goal:** Errors explain what went wrong and how to fix it.

- Create `src/alethfeld/errors.clj`
- Define error message formatters:
  ```clojure
  (def error-messages
    {:atomicity-violation
     (fn [{:keys [parent-id children-statuses]}]
       (str "Cannot create children for mote " parent-id
            " because previous children exist:\n"
            (format-children children-statuses)
            "\n\nTo fix: Run 'af archive clear " parent-id
            "' to remove archived children."))

     :quorum-not-reached
     (fn [{:keys [mote-id votes-needed votes-have]}]
       (str "Mote " mote-id " needs " votes-needed " votes, has " votes-have ".\n"
            "Run 'af vote " mote-id " --for --agent <name>' to add a vote."))

     :session-invalid
     (fn [{:keys [session-id]}]
       (str "Session " session-id " not found or expired.\n"
            "Get a new session: af ready --agent <name> --role <role>"))

     :role-forbidden
     (fn [{:keys [role action allowed-roles]}]
       (str "Role '" (name role) "' cannot perform '" (name action) "'.\n"
            "This action requires: " (str/join ", " (map name allowed-roles))))

     :self-vote-forbidden
     (fn [{:keys [agent mote-id reason]}]
       (str "Agent '" agent "' cannot vote on mote " mote-id ".\n"
            "Reason: " reason "\n"
            "A different agent must verify this work."))

     ;; ... more error types
     })
  ```
- Create `format-error` function that matches error type to formatter
- Update all `throw` sites to use structured error data
- Update CLI to catch and format errors nicely
- Write tests: each error type produces helpful message

**Deliverables:** Human-readable errors with hints, tests

---

## Phase C: Tier 2 High Value Improvements

Quality-of-life features that significantly improve workflow.

### Step C.1: Batch Voting

**Goal:** Vote on all pending items at once.

- Add `cmd-vote-all` in `cmd.clj`:
  ```bash
  af vote-all --pending --for --agent <name> --session <token>
  ```
- Implementation:
  - Find all motes with `:needs-verification` taint
  - Filter to those agent can vote on (not creator/proposer)
  - Cast vote on each in single transaction
  - Report: "Voted on 5 motes: 1.1, 1.2, 1.3, 1.4, 1.5"
- Flags:
  - `--pending`: Only motes needing votes
  - `--for` / `--against`: Vote direction
  - `--reason`: Applied to all votes
- Write tests: batch voting, skip self-vote candidates

**Deliverables:** `af vote-all` command with tests

### Step C.2: Auto-Propagation

**Goal:** When all children verified, optionally verify parent.

- Add `--propagate` flag to `af vote`:
  ```bash
  af vote 1.3.3 --for --agent verifier-1 --propagate --session <token>
  ```
- Implementation:
  - After voting, check if all siblings are `:verified`
  - If yes, and agent can vote on parent (not contributor), auto-vote
  - Recurse up the tree
  - Report: "Propagated verification to: 1.3, 1"
- Write tests: propagation occurs, stops at contributor boundary

**Deliverables:** `--propagate` flag on vote with tests

### Step C.3: Proposal Withdrawal

**Goal:** Cancel own proposal without quorum.

- Add `cmd-withdraw` in `cmd.clj`:
  ```bash
  af withdraw <parent-id> --session <token>
  ```
- Implementation:
  - Load proposal from parent
  - Verify session agent == proposal's `proposed-by`
  - Verify proposal status is `:pending`
  - Archive children to `archive/`
  - Clear proposal from parent
  - Add `:needs-decomposition` taint back
  - Git commit
- Write tests: withdrawal by proposer, rejection for non-proposer

**Deliverables:** `af withdraw` command with tests

### Step C.4: Cross-References / Dependencies

**Goal:** Express "mote X depends on mote Y".

- Add `:depends-on` field to Mote schema:
  ```clojure
  [:depends-on {:optional true}
   [:vector [:map
             [:ref MoteId]
             [:reason {:optional true} :string]]]]
  ```
- Add `cmd-add-dep` in `cmd.clj`:
  ```bash
  af add-dep 1.4 --depends-on 1.3 --reason "Uses evenness lemma" --session <token>
  ```
- Update DAG validation in `dag.clj`:
  - Check all `:depends-on` refs exist
  - Detect cycles in dependency graph
- Update verification logic:
  - Cannot verify X if any dependency Y is not `:verified`
- Write tests: dependency tracking, cycle detection, verification blocking

**Deliverables:** Dependency tracking with tests

### Step C.5: Atomic Markers on Creation

**Goal:** Mark claims as atomic at proposal time.

- Add `--atomic` flag to `af propose`:
  ```bash
  af propose 1 --claim "Simple fact" --atomic --agent proposer-1 --session <token>
  ```
- Implementation:
  - When `--atomic` specified for a claim:
    - Do NOT add `:needs-decomposition` taint
    - Add `:needs-verification` taint instead
  - Can mix: some claims atomic, some not
- Alternative syntax per-claim:
  ```bash
  af propose 1 \
    --claim "Complex step" --difficulty 4 \
    --claim "Simple fact" --difficulty 1 --atomic \
    --agent proposer-1
  ```
- Write tests: atomic claims skip decomposition taint

**Deliverables:** `--atomic` flag on propose with tests

---

## Phase D: Tier 3 Vision Features (FUTURE)

> These features make Alethfeld exciting and compelling.
> Deferred to v0.3+ but documented here for planning.

### Step D.1: Lean4 Export

**Goal:** Generate Lean 4 proof skeletons from verified motes.

- Add `af export <id> --format lean4`:
  ```bash
  af export 1 --format lean4 > Sqrt2Irrational.lean
  ```
- Map mote tree to Lean structure:
  - Root claim → `theorem` statement
  - Children → `have` statements
  - Unverified → `sorry`
  - Assumptions → `variable` or `hypothesis`
  - Definitions → `def` or `abbrev`
- Include comments mapping Lean lines to mote IDs
- Generate proper imports based on content

**Deliverables:** Lean4 export with mote ID comments

### Step D.2: Lean4 Verification Bridge

**Goal:** Actually verify proofs against Lean 4.

- Add `af verify <id> --backend lean4`:
  ```bash
  af verify 1 --backend lean4
  ```
- Implementation:
  - Export to temp Lean file
  - Run `lake build`
  - Parse output for:
    - Sorry count
    - Error locations
    - Success/failure
  - Map errors back to mote IDs
  - Report verification status

**Deliverables:** Lean4 verification with sorry tracking

### Step D.3: Adversarial Review Mode

**Goal:** Tool actively challenges claims.

- Add `af challenge <id>`:
  ```bash
  af challenge 1.3
  ```
- Analysis includes:
  - Edge cases for numeric claims (0, negative, large)
  - Boundary conditions
  - Implicit assumptions
  - Potential counterexample spaces
  - Comparison to similar verified lemmas

**Deliverables:** Adversarial analysis command

### Step D.4: Visualization Export

**Goal:** See proof structure graphically.

- Add `af export <id> --format mermaid`:
  ```bash
  af export 1 --format mermaid > proof.mmd
  ```
- Add `af export <id> --format svg`:
  ```bash
  af export 1 --format svg > proof.svg  # Uses mermaid-cli
  ```
- Show:
  - Mote hierarchy
  - Dependencies (cross-links)
  - Status colors
  - Vote counts

**Deliverables:** Mermaid/SVG visualization export

---

# Summary

## v0.1 Core (COMPLETED)

| Phase | Steps | Focus | Status |
|-------|-------|-------|--------|
| 0 | 0.1-0.2 | Setup | DONE |
| 1 | 1.1-1.3 | Data model (pure) | DONE |
| 2 | 2.1-2.3 | DAG ops (pure) | DONE |
| 3 | 3.1-3.3 | Job selection (pure) | DONE |
| 4 | 4.1-4.3 | File I/O (impure) | DONE |
| 5 | 5.1-5.3 | Transactions | DONE |
| 6 | 6.1-6.9 | CLI commands | DONE |
| 7 | 7.1-7.4 | Integration | DONE |

**Total v0.1:** 28 steps, 746 tests, 1926 assertions

## v0.2 Session & UX (IN PROGRESS)

| Phase | Steps | Focus | Priority |
|-------|-------|-------|----------|
| A | A.1-A.8 | Session enforcement | CRITICAL |
| B | B.1-B.4 | Essential UX | HIGH |
| C | C.1-C.5 | Quality of life | MEDIUM |

**Total v0.2:** 17 steps

## v0.3 Vision (FUTURE)

| Phase | Steps | Focus | Priority |
|-------|-------|-------|----------|
| D | D.1-D.4 | Lean4, visualization | FUTURE |

**Total v0.3:** 4 steps

---

# Breaking Changes in v0.2

Phase A introduces breaking changes to the CLI:

**Before (v0.1):**
```bash
af propose 1.2 "claim" --agent proposer-1
```

**After (v0.2):**
```bash
# Must first get a session
af ready --agent proposer-1 --role proposer
# Returns: {:session-id "abc-123-..." ...}

# All mutations require session
af propose 1.2 "claim" --session abc-123-...
af done --session abc-123-...
```

This is intentional: it enforces the multi-agent workflow and prevents agents from bypassing role restrictions.

---

# File Structure Changes (v0.2)

```
.alethfeld/
+-- config.edn
+-- motes/
+-- proposed/
+-- archive/
+-- sessions/           # NEW in v0.2
    +-- active/         # Current sessions
    |   +-- <uuid>-<uuid>.edn
    +-- completed/      # Audit trail
        +-- <uuid>-<uuid>.edn
```

---

# Schema Changes (v0.2)

```clojure
;; New Session schema
(def Session
  [:map
   [:session-id :string]
   [:mote-id MoteId]
   [:role Role]
   [:agent :string]
   [:started-at inst?]
   [:expires-at inst?]
   [:pid {:optional true} :int]
   [:actions [:vector :keyword]]])

;; Mote additions
[:contributors {:optional true}
 [:map
  [:created-by :string]
  [:proposed-by {:optional true} :string]
  [:refined-by {:optional true} [:set :string]]
  [:refs-checked-by {:optional true} [:set :string]]]]

[:depends-on {:optional true}
 [:vector [:map
           [:ref MoteId]
           [:reason {:optional true} :string]]]]

[:active-session {:optional true} :string]
```

---

# New Commands (v0.2)

| Command | Phase | Purpose |
|---------|-------|---------|
| `af done --session <token>` | A.6 | End session cleanly |
| `af config set <key> <value>` | B.1 | Configure quorum etc. |
| `af config get <key>` | B.1 | Read configuration |
| `af tree <id>` | B.2 | Visualize proof structure |
| `af status` | B.3 | Project-wide summary |
| `af vote-all` | C.1 | Batch voting |
| `af withdraw <id>` | C.3 | Cancel own proposal |
| `af add-dep <id>` | C.4 | Add dependency link |
