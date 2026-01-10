# Race Condition Analysis & Remediation Plan

**Date:** January 9, 2026
**Project:** Alethfeld
**Topic:** Concurrency & DAG Corruption

## 1. Problem Statement

A critical race condition exists in the Alethfeld CLI (`af`) when multiple agents attempt to claim work or modify the proof graph simultaneously. This results in:
1.  **Duplicate Claims:** Multiple agents successfully claiming the same mote, leading to wasted work and conflicting downstream updates.
2.  **DAG Corruption:** "Lost update" anomalies during structural modifications (e.g., adding children), causing permanent inconsistency between parent and child pointers (violations of DAG invariants).
3.  **Data Loss:** Rollback mechanisms in one process deleting valid files committed by another concurrently running process.

## 2. Root Cause Analysis

The application relies on `java.util.concurrent.locks.ReentrantLock` in `src/alethfeld/tx.clj` to serialize access to the repository:

```clojure
;; src/alethfeld/tx.clj
(def ^:private repo-locks (ConcurrentHashMap.))

(defn- with-repo-lock [repo-path f]
  (let [lock (get-repo-lock repo-path)]
    (.lock lock)
    ;; ...
```

**The Defect:**
`ReentrantLock` provides mutual exclusion only for threads within a **single JVM process**. Alethfeld is designed as a CLI tool where every command invocation (e.g., `af ready`, `af vote`) spawns a **new, independent JVM process**.

Because the locks are process-local and in-memory:
1.  **Process Isolation:** Process A has no visibility into Process B's locks.
2.  **Zero Coordination:** Both processes acquire their own local "lock" successfully and proceed to read/write shared files on disk simultaneously.
3.  **Race Window:**
    *   **T1:** Agent A reads `mote.edn` (version 1).
    *   **T2:** Agent B reads `mote.edn` (version 1).
    *   **T3:** Agent A writes `mote.edn` (version 2a: claims work).
    *   **T4:** Agent B writes `mote.edn` (version 2b: claims work), overwriting A's change.

Additionally, decision-making logic in `cmd.clj` (selecting a job) often happens *before* the transaction lock is acquired, exacerbating the issue by acting on stale data.

## 3. Impact Assessment

*   **Severity:** **Critical**. The system fails to maintain data integrity under normal concurrent usage (swarm mode).
*   **Likelihood:** **High**. Any deployment with >1 active agent will encounter this immediately.
*   **Consequences:**
    *   **Operational:** Agents waste compute resources working on the same tasks.
    *   **Integrity:** The proof graph becomes topologically invalid (orphaned children), requiring manual intervention or complex repair scripts (`af repair`).
    *   **Trust:** The verification guarantees of the system are nullified if the underlying storage is unreliable.

## 4. Proposed Solutions

### Solution 1: Global OS File Lock (Recommended)
Replace in-memory locks with `java.nio.channels.FileLock`. This uses the operating system kernel to enforce mutual exclusion on a specific file (e.g., `.alethfeld/lock`).

*   **Pros:** Robust, works across processes, simple implementation, OS handles cleanup on crash.
*   **Cons:** Blocking IO (commands serialize), relies on filesystem support (problematic on some NFS configurations, but fine for local git).

### Solution 2: Daemon / Client-Server
Refactor `af` into a continuously running server process that holds state and locks in memory. CLI commands become lightweight clients.

*   **Pros:** High performance (no JVM startup cost), enables true parallelism via threading.
*   **Cons:** Significant architectural rewrite, higher complexity (protocol, lifecycle management).

### Solution 3: Optimistic Concurrency
Implement version checking (MVCC-lite). Read a version token; when writing, assert the token hasn't changed. Retry on failure.

*   **Pros:** Non-blocking, fine-grained (per-mote) concurrency.
*   **Cons:** Wasted computational work on retry, complex to retrofit into the current "read-everything-then-act" code structure.

## 5. Implementation Plan

We will implement **Solution 1 (Global OS File Lock)** as it provides the necessary safety guarantees with the least disruption to the existing codebase.

### Step 1: Modify `src/alethfeld/tx.clj`

1.  **Remove** the `repo-locks` `ConcurrentHashMap` and `ReentrantLock` logic.
2.  **Introduce** a `lock-file-path` helper (target: `.alethfeld/lock`).
3.  **Redefine** `with-repo-lock` to use `java.nio.channels.FileChannel`:
    *   Open `.alethfeld/lock` with `RandomAccessFile` (rw).
    *   Call `channel.lock()` to acquire an exclusive lock. This will block until available.
    *   Execute the transaction function.
    *   Ensure the lock is released and channel closed in a `finally` block.

### Step 2: User Feedback

*   Implement a wrapper or feedback mechanism. If the lock cannot be acquired immediately (e.g., > 200ms), print a message to `stderr`: `Waiting for repository lock...`. This prevents users from thinking the CLI has hung.

### Step 3: Verification

1.  Create a reproduction script spawning 10 concurrent `af create` processes.
2.  Verify that without the fix, the graph is corrupted.
3.  Apply the fix.
4.  Verify that with the fix, all 10 motes are created correctly and linked to the parent.

### Code Sketch (`tx.clj`)

```clojure
(defn- with-repo-lock [repo-path f]
  (let [lock-file (io/file (str repo-path "/.alethfeld/lock"))]
    (with-open [raf (java.io.RandomAccessFile. lock-file "rw")
                channel (.getChannel raf)]
      ;; Blocks until lock is acquired
      (let [lock (.lock channel)]
        (try
          (f)
          (finally
            (.release lock)))))))
```
