# Transactions and Persistence

Alethfeld treats git as a database. Every mutation is an atomic commit, providing durability and audit trails.

## Transaction Model

The `tx/with-validation` macro orchestrates the complete write path:

```clojure
(tx/with-validation repo-path
  (fn []
    (store/save-mote! repo-path updated-mote))
  {:message "Cast verification vote on 1.2.3"})
```

### Execution Sequence

1. **Acquire lock.** `ReentrantLock` per repository path.
2. **Execute body.** Write operations to filesystem.
3. **Validate DAG.** Full integrity check via `dag/validate-dag`.
4. **Stage changes.** `git add .alethfeld/`.
5. **Commit.** `git commit -m "message"`.
6. **Release lock.** On success or exception.

### Guarantees

| Property | Implementation |
|----------|---------------|
| Atomicity | Git commit or nothing |
| Consistency | DAG validation before commit |
| Isolation | Per-repo `ReentrantLock` |
| Durability | Git object store |

## Locking

```clojure
;; Internal structure
(def repo-locks (ConcurrentHashMap.))

(defn get-lock [repo-path]
  (.computeIfAbsent repo-locks
    (canonical-path repo-path)
    (fn [_] (ReentrantLock.))))
```

- **Scope:** One lock per repository (canonical path).
- **Type:** `java.util.concurrent.locks.ReentrantLock`.
- **Normalization:** Paths canonicalized to handle symlinks.
- **Cleanup:** Lock entries accumulate in memory; acceptable for CLI lifetime.

## Race Window

A small window (~100ms) exists between validation completing and git commit finishing:

```
[validation passes] ──────── [files on disk] ──────── [git commit]
                     ↑                          ↑
                     │                          │
              validated, consistent       recorded in history
```

### If Process Crashes During Window

- Files on disk are validated and consistent.
- Git history does not reflect the changes.
- Other agents using `git pull` will not see the changes.

### Recovery

```bash
git add .alethfeld/
git commit -m 'recovery: uncommitted validated changes'
```

### Mitigations Considered

1. **Validate against git index.** Would eliminate window but adds complexity.
2. **Write-ahead log.** Overkill for CLI tool.
3. **Startup recovery.** Detect uncommitted changes on `af` invocation.

Current approach is acceptable for v0.1—the window is brief and data integrity (validation) is preserved.

## Git Operations

### Initialization

```clojure
(git/git-init! repo-path)
```

Creates `.git/` if not present. Alethfeld can operate in an existing git repository.

### Staging and Commit

```clojure
(git/git-add! repo-path [".alethfeld/"])
(git/git-commit! repo-path "message")
```

All changes within `.alethfeld/` are staged atomically.

### Sync

```clojure
(git/git-pull! repo-path)   ; Fetch + merge
(git/git-push! repo-path)   ; Push to remote
```

The `af sync` command wraps these with conflict detection.

### History

```clojure
(git/git-log repo-path ".alethfeld/motes/1.2.3.edn" 10)
; → [{:hash "abc123" :message "Add vote" :date #inst "..."}]
```

Per-file history enables mote audit trails.

## Validation Pipeline

Before any commit, `dag/validate-dag` runs all integrity checks:

```clojure
(defn validate-dag [motes]
  (or (validate-parent-child motes)      ; Bidirectional links
      (detect-cycles motes)               ; No cycles
      (validate-internal-refs motes)      ; Refs exist
      (validate-assumption-graph motes)   ; No circular deps
      (validate-proposal-atomicity motes) ; Atomic children
      nil))                               ; nil = valid
```

If any check fails, the transaction aborts and lock releases without committing.

## File Layout

Motes stored one-per-file, hierarchy mirrored in directory structure:

```
.alethfeld/
├── motes/
│   ├── 1.edn                    # Root mote
│   └── 1/
│       ├── 1.1.edn
│       └── 1.2/
│           └── 1.2.1.edn
├── proposed/
│   └── 1.2.2.edn                # Pending proposal
└── archive/
    └── 1/
        └── prop-20260106-xyz/   # Rejected proposal
            └── 1.2.3.edn
```

Benefits:
- **Minimal merge conflicts.** One mote per file.
- **Natural partitioning.** Hierarchy visible in filesystem.
- **Git-friendly.** File renames/moves tracked.

## Error Handling

Errors during transactions:

```clojure
(try
  (tx/with-validation repo-path
    (fn [] ...)
    {:message "..."})
  (catch ExceptionInfo e
    (case (:type (ex-data e))
      :validation-failed (println "DAG integrity error")
      :lock-timeout      (println "Repository busy")
      :git-error         (println "Git operation failed")
      (throw e))))
```

Lock is always released, even on exception.
