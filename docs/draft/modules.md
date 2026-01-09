# Module Reference

Source organized in `src/alethfeld/`. Approximately 8,300 lines across 17 modules.

## Data Layer

Pure functions for constructing and transforming data structures.

### schema.clj (248 lines)

Malli schemas for all data types.

```clojure
(require '[alethfeld.schema :as schema])

(schema/valid? schema/Mote mote)        ; → boolean
(schema/explain schema/Mote mote)       ; → error map or nil
```

**Schemas:** `MoteId`, `Status`, `Taint`, `Priority`, `Difficulty`, `Vote`, `Assumption`, `Definition`, `Proposal`, `Mote`, `Job`, `Session`, `Config`.

### id.clj (179 lines)

Hierarchical ID parsing and manipulation.

```clojure
(require '[alethfeld.id :as id])

(id/parse-id "1.2.3")                   ; → [1 2 3]
(id/format-id [1 2 3])                  ; → "1.2.3"
(id/valid-id? "1.2.3")                  ; → true
(id/parent-id "1.2.3")                  ; → "1.2"
(id/child-id "1.2" 3)                   ; → "1.2.3"
(id/next-child-id "1.2" ["1.2.1"])      ; → "1.2.2"
(id/id-depth "1.2.3")                   ; → 3
(id/ancestor-ids "1.2.3")               ; → ("1" "1.2")
(id/is-ancestor? "1" "1.2.3")           ; → true
(id/common-ancestor "1.2.3" "1.2.4")    ; → "1.2"
```

### mote.clj (356 lines)

Mote construction and pure transformations.

```clojure
(require '[alethfeld.mote :as mote])

;; Construction
(mote/make-mote {:id "1" :claim "..."})
(mote/make-root-mote "1" "claim text" "agent-name")
(mote/make-child-mote parent-mote "1.1" "child claim" "agent-name")

;; Transformations (return new mote)
(mote/add-assumption mote {:type :internal :ref "1.2"})
(mote/add-definition mote {:symbol "x" :meaning "..."})
(mote/add-vote mote {:agent "v1" :vote :for})
(mote/set-status mote :verified)
(mote/set-claimed-by mote "agent-name")
(mote/clear-claim mote)
(mote/add-taint mote :needs-verification)
(mote/remove-taint mote :needs-decomposition)

;; Queries
(mote/claim-expired? mote timeout-ms)
```

## Persistence Layer

File I/O and path management.

### io.clj (195 lines)

Low-level EDN file operations.

```clojure
(require '[alethfeld.io :as io])

(io/read-edn path)                      ; → data or nil
(io/write-edn path data)                ; → nil (side effect)
(io/delete-file path)                   ; → boolean
(io/move-file src dest)                 ; → nil
(io/list-edn-files dir)                 ; → seq of paths
(io/ensure-dir path)                    ; → nil
```

### path.clj (207 lines)

Derives filesystem paths from mote IDs and vice versa.

```clojure
(require '[alethfeld.path :as path])

(path/mote-id->path repo-path "1.2.3")  ; → ".alethfeld/motes/1/1.2/1.2.3.edn"
(path/path->mote-id file-path)          ; → "1.2.3"
(path/path->status file-path)           ; → :approved | :proposed | :archived
(path/mote-dir repo-path)               ; → ".alethfeld/motes"
(path/proposed-dir repo-path)           ; → ".alethfeld/proposed"
(path/session-path repo-path sid)       ; → ".alethfeld/sessions/active/<sid>.edn"
```

### store.clj (244 lines)

Mote CRUD and batch operations.

```clojure
(require '[alethfeld.store :as store])

;; Single mote
(store/load-mote repo-path "1.2.3")     ; → mote or nil
(store/save-mote! repo-path mote)       ; → nil
(store/delete-mote! repo-path "1.2.3")  ; → nil

;; Batch
(store/load-all-motes repo-path)        ; → {id → mote}

;; Config
(store/load-config repo-path)           ; → config map
(store/save-config! repo-path config)   ; → nil
```

## Transaction Layer

ACID operations and git integration.

### tx.clj (543 lines)

Transaction coordination with validation and locking.

```clojure
(require '[alethfeld.tx :as tx])

;; Execute with validation and git commit
(tx/with-validation repo-path
  (fn []
    ;; mutations here
    (store/save-mote! repo-path mote))
  {:message "Add vote to 1.2.3"})

;; Lock management (internal)
(tx/with-repo-lock repo-path
  (fn []
    ;; critical section
    ))
```

**Guarantees:**
- Per-repository mutual exclusion via `ReentrantLock`
- DAG validation before commit
- Atomic git commit on success
- Lock release on any exit

### git.clj (372 lines)

Git operations for persistence.

```clojure
(require '[alethfeld.git :as git])

(git/git-initialized? repo-path)        ; → boolean
(git/git-init! repo-path)               ; → nil
(git/git-status repo-path)              ; → {:staged [...] :modified [...]}
(git/git-add! repo-path files)          ; → nil
(git/git-commit! repo-path message)     ; → nil
(git/git-push! repo-path)               ; → nil
(git/git-pull! repo-path)               ; → nil
(git/git-log repo-path file n)          ; → [{:hash :message :date}...]
```

## Graph Validation

### dag.clj (477 lines)

DAG integrity checks.

```clojure
(require '[alethfeld.dag :as dag])

(dag/validate-dag motes)                ; → nil or [error...]

;; Individual checks
(dag/validate-parent-child motes)       ; Parent↔child consistency
(dag/detect-cycles motes)               ; Acyclic property
(dag/validate-internal-refs motes)      ; Reference integrity
(dag/validate-assumption-graph motes)   ; No circular assumptions
(dag/validate-proposal-atomicity motes) ; Children share fate
```

Returns nil if valid, vector of error maps if not.

## Verification Workflow

### verify.clj (437 lines)

Vote management and quorum logic.

```clojure
(require '[alethfeld.verify :as verify])

(verify/count-votes-by-type votes)      ; → {:for n :against m}
(verify/check-quorum-generic votes config) ; → :verified | :refuted | :contested | nil
(verify/cast-vote! repo-path mote-id vote agent) ; Side effect + quorum check
```

### proposal.clj (549 lines)

Decomposition workflow.

```clojure
(require '[alethfeld.proposal :as proposal])

(proposal/create-proposal! repo-path parent-id children agent)
(proposal/approve-proposal! repo-path mote-id agent)
(proposal/reject-proposal! repo-path mote-id agent reason)
```

Proposals are atomic: all children approved or all rejected together.

## Work Dispatch

### job.clj (281 lines)

Job selection and role derivation.

```clojure
(require '[alethfeld.job :as job])

(job/mote->roles mote)                  ; → #{:verifier :prover ...}
(job/mote->role mote)                   ; → primary role
(job/workable? mote)                    ; → boolean
(job/select-jobs motes role priority)   ; → [job...]
```

Role derivation from taint flags:

| Taint | Primary Role |
|-------|--------------|
| `:needs-decomposition` | `:proposer` |
| `:needs-advisor-review` | `:advisor` |
| `:needs-proof` | `:prover` |
| `:needs-verification` | `:verifier` |
| `:needs-ref-check` | `:ref-checker` |
| `:needs-counterexample` | `:counterexample` |

### session.clj (784 lines)

Session lifecycle and role enforcement.

```clojure
(require '[alethfeld.session :as session])

(session/create-session! repo-path mote-id role agent)
(session/get-session repo-path session-id)
(session/complete-session! repo-path session-id)
(session/validate-action session action)  ; → true or throws
(session/session-expired? session)
```

### prompt.clj (789 lines)

Prompt assembly for agent roles.

```clojure
(require '[alethfeld.prompt :as prompt])

(prompt/render-job job)                 ; → job with :prompt field
(prompt/format-assumptions mote motes)
(prompt/format-definitions mote)
(prompt/format-vote-summary mote)
```

Loads role templates from `prompts/` directory.

## CLI Layer

### cli.clj (918 lines)

Entry point, argument parsing, output formatting.

```clojure
(require '[alethfeld.cli :as cli])

(-main & args)                          ; Entry point
(cli/format-output data format)         ; :edn | :json
(cli/suggest-command input commands)    ; Typo suggestions
(cli/levenshtein-distance a b)          ; Edit distance
```

### cmd.clj (2,779 lines)

Command implementations. Each `cmd-*` function handles one CLI command.

**Repository:** `cmd-init!`, `cmd-config`

**Motes:** `cmd-show`, `cmd-create`, `cmd-update`, `cmd-check`, `cmd-tree`, `cmd-status`

**Work:** `cmd-ready`, `cmd-claim`, `cmd-unclaim`, `cmd-done`

**Decomposition:** `cmd-propose`, `cmd-approve`, `cmd-reject`

**Verification:** `cmd-vote`, `cmd-vote-all`

**Content:** `cmd-add-ref`, `cmd-add-assumption`, `cmd-add-definition`, `cmd-taint`

**Git:** `cmd-log`, `cmd-sync`

### errors.clj (572 lines)

Error handling and user-friendly messages.

```clojure
(require '[alethfeld.errors :as errors])

(errors/format-error ex)                ; → string with suggestions
(errors/suggest-role input)             ; → closest valid role
```

Error types include `:not-found`, `:validation-failed`, `:permission-denied`, `:conflict`. Each type has tailored recovery suggestions.
