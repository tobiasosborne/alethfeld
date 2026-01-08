# Alethfeld Implementation Plan

**Approach:** Test-driven, purely functional where possible  
**Chunk size:** Each step implementable in ~20K tokens  
**Language:** Clojure  

---

## Phase 0: Project Setup

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

## Phase 1: Core Data Model (Pure Functions)

### Step 1.1: Schema Definitions + Validation Tests
- Create `src/alethfeld/schema.clj`
- Define all Malli schemas: MoteId, Status, Taint, Priority, Difficulty, Role
- Define Assumption, Definition, Vote, ProposalVote, Proposal
- Define Mote schema
- Define Job, ReadyOptions schemas
- Create `test/alethfeld/schema_test.clj`
- Write tests: valid motes pass, invalid motes fail
- Write tests: edge cases (empty strings, out-of-range values)

**Deliverables:** All schemas defined, validation tests pass

### Step 1.2: Mote Constructor Functions + Tests
- Create `src/alethfeld/mote.clj`
- `make-mote`: constructor with defaults
- `make-root-mote`: root mote constructor
- `make-child-mote`: inherits difficulty/priority from parent
- `make-proposal`: proposal constructor
- `make-vote`, `make-proposal-vote`: vote constructors
- Create `test/alethfeld/mote_test.clj`
- Write tests: constructors produce valid motes
- Write tests: inheritance from parent works
- Write tests: timestamps are set

**Deliverables:** Pure constructor functions, all tests pass

### Step 1.3: Mote Transformation Functions + Tests
- `add-assumption`: pure fn, returns updated mote
- `add-definition`: pure fn
- `add-vote`: pure fn
- `add-taint`, `remove-taint`: pure fns
- `set-status`: pure fn with valid transition check
- `set-claim-by`: pure fn for claiming
- `clear-claim`: pure fn for unclaiming
- Write tests for each transformation
- Write tests: invalid status transitions rejected

**Deliverables:** Pure transformation functions, all tests pass

---

## Phase 2: DAG Operations (Pure Functions)

### Step 2.1: ID Operations + Tests
- Create `src/alethfeld/id.clj`
- `parse-id`: "1.2.3" → ["1" "2" "3"]
- `parent-id`: "1.2.3" → "1.2"
- `root-id`: "1.2.3" → "1"
- `child-id`: "1.2" + 3 → "1.2.3"
- `next-child-id`: given parent + existing children → next ID
- `id-depth`: "1.2.3" → 3
- `is-ancestor?`: check if one ID is ancestor of another
- Create `test/alethfeld/id_test.clj`
- Write tests for all functions
- Write tests: edge cases (root IDs, deep nesting)

**Deliverables:** Pure ID functions, all tests pass

### Step 2.2: Path Derivation + Tests
- Create `src/alethfeld/path.clj`
- `mote-id->path`: ID + status → file path
- `path->mote-id`: file path → ID
- `proposed-path`: ID → proposed/ path
- `archive-path`: ID + proposal-id → archive/ path
- `config-path`: → "config.edn"
- Create `test/alethfeld/path_test.clj`
- Write tests: path derivation for various depths
- Write tests: round-trip (id→path→id)

**Deliverables:** Pure path functions, all tests pass

### Step 2.3: DAG Validation + Tests
- Create `src/alethfeld/dag.clj`
- `validate-parent-child`: check bidirectional consistency
- `find-cycles`: detect cycles in assumption graph (DFS)
- `validate-refs`: all internal refs exist
- `validate-proposal-atomicity`: children share proposal
- `validate-mote-graph`: run all validations on mote collection
- Create `test/alethfeld/dag_test.clj`
- Write tests: valid DAGs pass
- Write tests: cycles detected
- Write tests: orphan children detected
- Write tests: broken refs detected

**Deliverables:** Pure DAG validation, all tests pass

---

## Phase 3: Job Selection (Pure Functions)

### Step 3.1: Role Derivation + Tests
- Create `src/alethfeld/job.clj`
- `mote->role`: derive role from taint flags
- `workable?`: check if mote needs work (not verified, not claimed)
- `matches-filter?`: check mote against ReadyOptions
- Create `test/alethfeld/job_test.clj`
- Write tests: role derivation for each taint
- Write tests: filter matching (difficulty range, priority range, role)

**Deliverables:** Pure role/filter functions, all tests pass

### Step 3.2: Job Selection Algorithm + Tests
- `select-jobs`: filter + sort + take N
- `priority-rank`: priority → numeric rank for sorting
- `job-comparator`: sort by priority, then difficulty
- `build-job`: mote + context → Job record
- Create tests: selection from mixed mote set
- Create tests: respects all filter options
- Create tests: correct sorting order

**Deliverables:** Pure job selection, all tests pass

### Step 3.3: Prompt Rendering + Tests
- Create `src/alethfeld/prompt.clj`
- Define prompt templates as data (not strings with interpolation)
- `render-prompt`: role + mote + context → prompt string
- `format-assumptions`: assumptions → readable string
- `format-definitions`: definitions → readable string
- `format-vote-summary`: votes → summary string
- Create `test/alethfeld/prompt_test.clj`
- Write tests: each role produces expected prompt structure
- Write tests: context correctly interpolated

**Deliverables:** Pure prompt rendering, all tests pass

---

## Phase 4: File I/O (Impure, Isolated)

### Step 4.1: EDN I/O + Tests
- Create `src/alethfeld/io.clj`
- `read-edn`: path → EDN data (or nil)
- `write-edn`: path + data → writes file (creates dirs)
- `delete-file`: path → deletes file
- `move-file`: src + dst → moves file
- `list-edn-files`: dir → list of .edn paths
- Create `test/alethfeld/io_test.clj`
- Write tests using temp directories
- Write tests: read what was written
- Write tests: missing file returns nil
- Write tests: nested dirs created

**Deliverables:** I/O functions with tests using temp dirs

### Step 4.2: Mote Persistence + Tests
- Create `src/alethfeld/store.clj`
- `load-mote`: repo-path + mote-id → Mote (or nil)
- `save-mote!`: repo-path + Mote → writes file
- `delete-mote!`: repo-path + mote-id → deletes file
- `move-mote!`: repo-path + mote-id + new-status → moves file
- `load-all-motes`: repo-path → map of id→Mote
- `load-config`: repo-path → Config
- `save-config!`: repo-path + Config → writes file
- Create `test/alethfeld/store_test.clj`
- Write tests: CRUD operations
- Write tests: load-all-motes finds nested motes

**Deliverables:** Mote persistence, all tests pass

### Step 4.3: Git Operations + Tests
- Create `src/alethfeld/git.clj`
- `git-init!`: initialize repo if needed
- `git-add-all!`: stage all .alethfeld changes
- `git-commit!`: commit with message
- `git-log`: get log for file
- `git-pull!`: pull with rebase
- `git-push!`: push
- `git-status`: check for uncommitted changes
- Create `test/alethfeld/git_test.clj`
- Write tests using temp git repos
- Write tests: init creates .git
- Write tests: commit creates history
- Write tests: log retrieves history

**Deliverables:** Git operations, all tests pass

---

## Phase 5: Transaction Layer

### Step 5.1: Transaction Wrapper + Tests
- Create `src/alethfeld/tx.clj`
- `transact!`: wraps operations in git commit
- `with-validation`: validates before commit, rolls back on failure
- `atomic-write!`: write multiple motes atomically
- Create `test/alethfeld/tx_test.clj`
- Write tests: successful tx commits
- Write tests: failed validation → no commit
- Write tests: multiple motes in one commit

**Deliverables:** Transaction wrapper, all tests pass

### Step 5.2: Proposal Workflow + Tests
- Create `src/alethfeld/proposal.clj`
- `create-proposal!`: parent-id + claims → creates proposed children + proposal
- `approve-proposal!`: parent-id + agent + reason → casts vote, maybe promotes
- `reject-proposal!`: parent-id + agent + reason → casts vote, maybe archives
- `check-proposal-quorum`: proposal → :pending | :approved | :rejected
- Create `test/alethfeld/proposal_test.clj`
- Write tests: proposal creates children in proposed/
- Write tests: quorum approval moves children to motes/
- Write tests: quorum rejection moves children to archive/
- Write tests: partial votes leave pending

**Deliverables:** Proposal workflow, all tests pass

### Step 5.3: Verification Workflow + Tests  
- Create `src/alethfeld/verify.clj`
- `cast-vote!`: mote-id + agent + for/against + reason
- `check-verification-quorum`: mote → updated status
- `update-taint-after-vote!`: adjust taints based on vote outcome
- Create `test/alethfeld/verify_test.clj`
- Write tests: vote recorded
- Write tests: quorum reached → status changes
- Write tests: contested when mixed votes

**Deliverables:** Verification workflow, all tests pass

---

## Phase 6: CLI Commands

### Step 6.1: CLI Infrastructure + Tests
- Create `src/alethfeld/cli.clj`
- Argument parsing (use clojure.tools.cli or hand-roll)
- `dispatch`: command → handler function
- `format-output`: data + format → edn or json string
- `exit`: code + message → exits
- Create `test/alethfeld/cli_test.clj`
- Write tests: arg parsing
- Write tests: dispatch routes correctly
- Write tests: output formatting

**Deliverables:** CLI infrastructure, all tests pass

### Step 6.2: Init & Show Commands + Tests
- `cmd-init!`: create .alethfeld/, config.edn, git init
- `cmd-show`: load and display mote
- Create `test/alethfeld/cmd/init_test.clj`
- Create `test/alethfeld/cmd/show_test.clj`
- Write tests: init creates structure
- Write tests: show returns mote data

**Deliverables:** init, show commands working

### Step 6.3: Create Command + Tests
- `cmd-create!`: create root or child mote
- Options: --root, --claim, --difficulty, --priority, --agent
- Create `test/alethfeld/cmd/create_test.clj`
- Write tests: root creation
- Write tests: child creation with inheritance
- Write tests: validation errors

**Deliverables:** create command working

### Step 6.4: Ready Command + Tests
- `cmd-ready`: query for jobs, optionally claim
- Options: --agent, --role, --difficulty, --priority, --max, --no-claim, --format
- Build Job with prompt
- Create `test/alethfeld/cmd/ready_test.clj`
- Write tests: filters work
- Write tests: auto-claim works
- Write tests: prompt included

**Deliverables:** ready command working

### Step 6.5: Propose/Approve/Reject Commands + Tests
- `cmd-propose!`: create proposal
- `cmd-approve!`: vote approve
- `cmd-reject!`: vote reject
- Create `test/alethfeld/cmd/proposal_test.clj`
- Write tests: full proposal lifecycle
- Write tests: quorum behavior

**Deliverables:** proposal commands working

### Step 6.6: Update/Vote/Taint Commands + Tests
- `cmd-update!`: update mote fields
- `cmd-vote!`: cast verification vote
- `cmd-taint!`: add/remove taints
- Create `test/alethfeld/cmd/update_test.clj`
- Write tests: each command modifies correctly

**Deliverables:** update commands working

### Step 6.7: Claim/Unclaim Commands + Tests
- `cmd-claim!`: set claimed-by
- `cmd-unclaim!`: clear claimed-by
- Create `test/alethfeld/cmd/claim_test.clj`
- Write tests: claim sets fields
- Write tests: unclaim clears fields
- Write tests: already-claimed error

**Deliverables:** claim commands working

### Step 6.8: Add-* Commands + Tests
- `cmd-add-ref!`: add external reference
- `cmd-add-assumption!`: add internal assumption
- `cmd-add-definition!`: add definition
- Create `test/alethfeld/cmd/add_test.clj`
- Write tests: each add type

**Deliverables:** add-* commands working

### Step 6.9: Check/Log/Sync Commands + Tests
- `cmd-check`: validate entire DAG
- `cmd-log`: show git history for mote
- `cmd-sync!`: pull, commit, push
- Create `test/alethfeld/cmd/util_test.clj`
- Write tests: check catches errors
- Write tests: log retrieves history
- Write tests: sync sequence

**Deliverables:** utility commands working

---

## Phase 7: Integration & Polish

### Step 7.1: End-to-End Integration Tests
- Create `test/alethfeld/integration_test.clj`
- Test: full lifecycle from init → create → propose → approve → verify
- Test: multiple agents working in parallel (simulated)
- Test: conflict detection
- Test: recovery from invalid state

**Deliverables:** Integration tests pass

### Step 7.2: Error Handling & Messages
- Review all error paths
- Add clear error messages for common failures
- Add `--verbose` flag for debugging
- Test error messages are helpful

**Deliverables:** Polished error handling

### Step 7.3: Build & Distribution
- Create uberjar build
- Create install script
- Test on fresh system
- Document installation in README

**Deliverables:** Distributable `af` binary

### Step 7.4: Documentation
- Complete README with examples
- Document all commands with `af help <cmd>`
- Add example session transcript
- Add troubleshooting guide

**Deliverables:** Complete documentation

---

## Summary: 28 Steps

| Phase | Steps | Focus |
|-------|-------|-------|
| 0 | 0.1–0.2 | Setup |
| 1 | 1.1–1.3 | Data model (pure) |
| 2 | 2.1–2.3 | DAG ops (pure) |
| 3 | 3.1–3.3 | Job selection (pure) |
| 4 | 4.1–4.3 | File I/O (impure) |
| 5 | 5.1–5.3 | Transactions |
| 6 | 6.1–6.9 | CLI commands |
| 7 | 7.1–7.4 | Integration |

**Estimated total:** 28 issues for beads tracking
