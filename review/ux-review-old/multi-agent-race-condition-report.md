# Multi-Agent Claim Race Condition Analysis

**Document Version:** 1.0
**Date:** 2026-01-09
**Author:** Code Review Analysis
**Status:** Ready for Review

---

## Executive Summary

A critical race condition exists in Alethfeld's job claiming mechanism that allows multiple agents to simultaneously claim the same mote. This results in duplicate sessions, lost claims, and potential DAG corruption. The issue affects both single-process concurrent operations and multi-process deployments.

The root cause is a non-atomic read-check-write cycle in `cmd-ready` where job selection occurs outside the transaction boundary. While individual writes are protected by `ReentrantLock`, the full claim operation spans multiple unprotected steps.

This report details the problem, analyzes its impact, evaluates seven potential solutions, and recommends a hybrid approach combining the existing reservation system with optimistic concurrency control.

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Root Cause Analysis](#2-root-cause-analysis)
3. [Impact Assessment](#3-impact-assessment)
4. [Proposed Solutions](#4-proposed-solutions)
5. [Recommended Solution](#5-recommended-solution)
6. [Implementation Plan](#6-implementation-plan)
7. [Testing Strategy](#7-testing-strategy)
8. [Appendices](#8-appendices)

---

## 1. Problem Statement

### 1.1 Observed Behavior

When multiple agents simultaneously execute `af ready --name <agent>` targeting overlapping job criteria, the following anomalies occur:

1. **Duplicate Sessions:** Multiple session files created for the same mote/role combination
2. **Overwritten Claims:** The last agent's claim silently overwrites previous claims
3. **Orphaned Sessions:** Agents hold sessions for motes they no longer own
4. **Conflicting Work:** Multiple agents believe they own the same work item

### 1.2 Reproduction Scenario

```bash
# Terminal 1                          # Terminal 2
af ready --name agent-1               af ready --name agent-2
# Both return mote "1.2"              # Both return mote "1.2"
# agent-1 session created             # agent-2 session created
# agent-1 claims "1.2"                # agent-2 claims "1.2" (overwrites!)
```

### 1.3 Scope

| Deployment Model | Affected? | Severity |
|-----------------|-----------|----------|
| Single agent | No | N/A |
| Multiple agents, single process (futures/threads) | Yes | High |
| Multiple agents, multiple processes, same machine | Yes | Critical |
| Multiple agents, distributed (via git remote) | Yes | Critical |

### 1.4 Affected Components

| File | Function | Role |
|------|----------|------|
| `src/alethfeld/cmd.clj` | `cmd-ready` | Primary site of race |
| `src/alethfeld/cmd.clj` | `cmd-claim!` | Secondary claim path |
| `src/alethfeld/session.clj` | `create-session!` | Session creation outside lock |
| `src/alethfeld/job.clj` | `select-jobs` | Uses stale mote snapshot |
| `src/alethfeld/tx.clj` | `atomic-write!` | Lock scope too narrow |

---

## 2. Root Cause Analysis

### 2.1 Architecture Overview

Alethfeld uses a transaction layer (`tx.clj`) with per-repository `ReentrantLock` to serialize mutations:

```
┌─────────────────────────────────────────────────────────┐
│                    cmd-ready Flow                        │
├─────────────────────────────────────────────────────────┤
│  1. cleanup-stale-sessions-and-claims!                  │ ← Outside lock
│  2. store/load-all-motes                                │ ← Outside lock
│  3. job/select-jobs (filters by claimed-by: nil)        │ ← Outside lock
│  4. session/create-session! (writes session file)       │ ← Outside lock
│  5. tx/atomic-write! (writes mote claim)                │ ← INSIDE lock
└─────────────────────────────────────────────────────────┘
```

### 2.2 The Race Window

The critical issue is the **temporal gap** between checking claim availability (step 3) and writing the claim (step 5):

```
Timeline:
─────────────────────────────────────────────────────────────────────────
T0: Agent A loads motes        → sees mote "1.2" with claimed-by: nil
T1: Agent B loads motes        → sees mote "1.2" with claimed-by: nil (STALE!)
T2: Agent A selects job "1.2"  → passes workable? check
T3: Agent B selects job "1.2"  → passes workable? check (STALE DATA!)
T4: Agent A creates session-A  → .alethfeld/sessions/active/session-A.edn
T5: Agent B creates session-B  → .alethfeld/sessions/active/session-B.edn
T6: Agent A acquires lock      → writes claimed-by: "agent-A" to mote
T7: Agent A releases lock
T8: Agent B acquires lock      → writes claimed-by: "agent-B" to mote (OVERWRITES!)
T9: Agent B releases lock
─────────────────────────────────────────────────────────────────────────
Result: Agent B owns claim, but Agent A has orphaned session
```

### 2.3 Code Evidence

**File:** `src/alethfeld/cmd.clj`, lines 832-960

```clojure
;; Line 832: READ - Outside any lock
motes (store/load-all-motes repo-path)

;; Lines 837-842: CHECK - Uses potentially stale snapshot
jobs (job/select-jobs motes
                      :role role
                      :difficulty difficulty-filter
                      :priority priority-filter
                      :max jobs-to-fetch
                      :claim-timeout claim-timeout)

;; Lines 936-940: SESSION CREATION - Outside any lock!
sess (session/create-session! repo-path
                              (:mote-id j)
                              job-role
                              agent
                              :duration-minutes session-timeout)

;; Line 960: WRITE - Only this is inside the lock
(tx/atomic-write! repo-path commit-msg updated-motes :validate false)
```

### 2.4 Contrast with Safe Pattern

The test file demonstrates the correct atomic pattern that IS NOT used in production:

**File:** `test/alethfeld/concurrency_test.clj`, lines 85-102

```clojure
(defn- claim-mote! [id agent]
  (tx/atomic-update! repo-path           ; Lock acquired HERE
    (str "Claim mote " id " for " agent)
    id
    (fn [current-mote]                   ; Read happens INSIDE lock
      (let [current-claimer (:claimed-by current-mote)]
        (when (and current-claimer (not= current-claimer agent))
          (throw (ex-info "Mote already claimed"  ; Check happens INSIDE lock
                          {:type :already-claimed
                           :mote-id id
                           :claimed-by current-claimer})))
        (mote/set-claimed-by current-mote agent)))))  ; Write happens INSIDE lock
```

### 2.5 Multi-Process Limitation

The `ReentrantLock` in `tx.clj` is a **JVM in-memory lock**:

```clojure
;; File: src/alethfeld/tx.clj, lines 18-33
(def ^:private repo-locks
  "Map of canonical repo paths to their ReentrantLocks."
  (ConcurrentHashMap.))
```

This provides **zero protection** when agents run as separate OS processes. Each process has its own `repo-locks` map.

The test file acknowledges this limitation:

```clojure
;; File: test/alethfeld/concurrency_test.clj, lines 6-9
;; NOTE: These tests simulate concurrency within a single process using
;; futures. Real multi-process concurrency would require git-level locking
;; which is not yet implemented.
```

---

## 3. Impact Assessment

### 3.1 Data Integrity

| Issue | Severity | Recovery |
|-------|----------|----------|
| Duplicate sessions for same mote | High | Manual deletion required |
| Overwritten claims (lost work assignment) | High | Agent must re-claim |
| Conflicting votes/proposals from multiple "owners" | Critical | Manual DAG repair |
| Invalid mote state (multiple proposals) | Critical | May require rollback |

### 3.2 User Experience

| Symptom | Frequency | Impact |
|---------|-----------|--------|
| Agent told they have work, but claim lost | Common under load | Confusing, wastes effort |
| Session commands fail with "mote mismatch" | Common | Breaks agent workflow |
| `af check` reports DAG inconsistencies | Occasional | Requires investigation |
| Silent overwrite (no error) | Always when race occurs | Hardest to diagnose |

### 3.3 System Reliability

| Scenario | Risk Level |
|----------|------------|
| 2 agents, same role, same priority filter | High |
| N agents polling `af ready` in tight loop | Very High |
| Orchestrator distributing work to agent pool | Critical |
| CI/CD spawning parallel verification agents | Critical |

### 3.4 Blast Radius

```
Race occurs on claim
        │
        ├─► Duplicate sessions created
        │         │
        │         └─► Both agents attempt work
        │                    │
        │                    ├─► Conflicting proposals → DAG corruption
        │                    ├─► Duplicate votes → Invalid quorum
        │                    └─► Conflicting status updates → State machine violation
        │
        └─► One agent's claim overwritten
                  │
                  └─► Agent has session but no claim
                             │
                             └─► Session commands fail silently or confusingly
```

---

## 4. Proposed Solutions

### 4.1 Solution A: Pessimistic Locking (Extend Lock Scope)

**Approach:** Move the entire read-check-session-write flow inside a single lock acquisition.

```clojure
(defn cmd-ready-safe [{:keys [options]}]
  (tx/with-lock repo-path  ; NEW: Acquire lock at start
    (fn []
      (let [motes (store/load-all-motes repo-path)  ; Read inside lock
            jobs (job/select-jobs motes ...)        ; Check inside lock
            sess (session/create-session! ...)      ; Session inside lock
            updated-motes ...]
        (store/save-mote! repo-path ...)            ; Write inside lock
        (git/git-add-all! repo-path)
        (git/git-commit! repo-path msg)))))
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Fully solves single-process race |
| **Multi-process** | Does NOT solve (in-memory lock) |
| **Complexity** | Low - minor refactor |
| **Performance** | Poor - serializes ALL ready commands |
| **Throughput** | ~1 ready/second (lock held during I/O) |

**Verdict:** Quick fix for single-process only. Not recommended as final solution.

---

### 4.2 Solution B: Optimistic Concurrency Control (CAS)

**Approach:** Read version, attempt write with version check, retry on conflict.

```clojure
(defn claim-with-cas! [repo-path mote-id agent]
  (loop [attempts 0]
    (let [mote (store/load-mote repo-path mote-id)
          version (:updated-at mote)]
      (when (:claimed-by mote)
        (throw (ex-info "Already claimed" {:type :already-claimed})))
      (try
        (tx/atomic-update! repo-path
          (str "Claim " mote-id)
          mote-id
          (fn [current]
            (when (not= (:updated-at current) version)
              (throw (ex-info "Version conflict" {:type :cas-conflict})))
            (when (:claimed-by current)
              (throw (ex-info "Already claimed" {:type :already-claimed})))
            (mote/set-claimed-by current agent)))
        (catch ExceptionInfo e
          (if (and (= :cas-conflict (:type (ex-data e)))
                   (< attempts 3))
            (do (Thread/sleep (+ 10 (rand-int 50)))
                (recur (inc attempts)))
            (throw e)))))))
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Fully correct with retry |
| **Multi-process** | Works via git (timestamp/hash as version) |
| **Complexity** | Medium - requires retry logic |
| **Performance** | Good - no global lock |
| **Throughput** | High under low contention |

**Verdict:** Scalable and correct, but adds complexity. Good for high-throughput scenarios.

---

### 4.3 Solution C: Two-Phase Reserve-Then-Claim

**Approach:** Leverage existing reservation system, make it mandatory.

```
Phase 1: af ready --reserve → Creates reservation (60s TTL)
Phase 2: af ready --claim-reservation TOKEN → Claims if reservation valid
```

```clojure
;; Enhanced select-jobs to exclude reserved motes
(defn workable? [mote repo-path]
  (and (not (terminal-status? (:status mote)))
       (not (:claimed-by mote))
       (not (mote-has-active-reservation? repo-path (:id mote)))))

;; Atomic reservation creation
(defn create-reservation-atomic! [repo-path mote-id role]
  (let [token (generate-token)]
    (tx/with-validation repo-path
      (str "Reserve " mote-id)
      (fn [_]
        (when (mote-has-active-reservation? repo-path mote-id)
          (throw (ex-info "Already reserved" {:type :already-reserved})))
        (write-reservation! repo-path token mote-id role)))
    token))
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Correct if reservation creation is atomic |
| **Multi-process** | Works via reservation files |
| **Complexity** | Medium - builds on existing code |
| **Performance** | Medium - two round-trips |
| **Throughput** | Medium |

**Verdict:** Good balance. Reservation files provide cross-process coordination.

---

### 4.4 Solution D: File-Level Locking (flock)

**Approach:** OS-level advisory lock on a lockfile.

```clojure
(import '[java.nio.channels FileChannel FileLock]
        '[java.nio.file StandardOpenOption])

(defn with-flock [repo-path f]
  (let [lock-path (io/file repo-path ".alethfeld/.lock")
        opts (into-array [StandardOpenOption/CREATE
                          StandardOpenOption/WRITE])]
    (with-open [channel (FileChannel/open (.toPath lock-path) opts)]
      (let [lock (.lock channel)]
        (try (f)
          (finally (.release lock)))))))
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Correct for same-machine |
| **Multi-process** | Works on same machine |
| **Distributed** | Does NOT work (NFS advisory locks unreliable) |
| **Complexity** | Low |
| **Performance** | Poor - global serialization |

**Verdict:** Good for single-machine multi-process. Fails for distributed agents.

---

### 4.5 Solution E: Git-Native Coordination

**Approach:** Use git's atomic operations for coordination.

**Option E1: Push-to-claim branch**
```bash
# Agent creates claim branch and pushes atomically
git checkout -b claim/1.2/agent-1
git push origin claim/1.2/agent-1
# Push fails if branch exists = claim conflict
```

**Option E2: Git notes for claims**
```bash
git notes --ref=claims add -m "agent-1" <mote-commit>
git push origin refs/notes/claims
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Correct with atomic push |
| **Multi-process** | Works |
| **Distributed** | Works with remote |
| **Complexity** | High - unusual git usage |
| **Performance** | Medium - requires network for remote |

**Verdict:** Elegant but complex. Conflates git semantics with application logic.

---

### 4.6 Solution F: Claim-Lock Field in Mote Schema

**Approach:** Add transient lock field to mote, implement acquire/release protocol.

```clojure
;; Schema addition
(def ClaimLock
  [:map
   [:holder :string]
   [:acquired-at inst?]
   [:expires-at inst?]])

;; Acquisition
(defn acquire-claim-lock! [repo-path mote-id agent ttl-seconds]
  (tx/atomic-update! repo-path
    (str "Lock " mote-id)
    mote-id
    (fn [mote]
      (let [lock (:claim-lock mote)
            now (Instant/now)]
        (when (and lock (.isBefore now (->instant (:expires-at lock))))
          (throw (ex-info "Lock held" {:holder (:holder lock)})))
        (assoc mote :claim-lock
               {:holder agent
                :acquired-at (Date/from now)
                :expires-at (Date/from (.plusSeconds now ttl-seconds))})))))
```

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Correct with TTL expiration |
| **Multi-process** | Works via git commit |
| **Distributed** | Works with git sync |
| **Complexity** | Medium |
| **Performance** | Good - per-mote granularity |

**Verdict:** Clean semantics. Lock is visible in mote history. Adds schema complexity.

---

### 4.7 Solution G: Dedicated Lock Service (Out of Scope)

**Approach:** External coordination service (Redis, etcd, ZooKeeper).

| Criterion | Assessment |
|-----------|------------|
| **Correctness** | Fully correct |
| **Multi-process** | Works |
| **Distributed** | Works |
| **Complexity** | Very High - external dependency |
| **Performance** | Excellent |

**Verdict:** Overkill for CLI tool. Violates "no external dependencies" principle.

---

## 5. Recommended Solution

### 5.1 Hybrid Approach: Enhanced Reservations + Optimistic Locking

Combine **Solution C** (Two-Phase Reserve) with **Solution B** (CAS) elements:

```
┌─────────────────────────────────────────────────────────────────┐
│                    Enhanced Claim Flow                          │
├─────────────────────────────────────────────────────────────────┤
│  1. af ready --name agent-1                                     │
│         │                                                       │
│         ▼                                                       │
│  2. Atomic reservation creation (CAS on reservation dir)        │
│         │                                                       │
│         ├── Success: reservation-token returned                 │
│         └── Failure: mote already reserved → select next job    │
│                                                                 │
│  3. Create session (reservation provides exclusivity)           │
│         │                                                       │
│         ▼                                                       │
│  4. Atomic claim write (verify reservation still valid)         │
│         │                                                       │
│         ├── Success: claim written, reservation consumed        │
│         └── Failure: reservation expired → rollback session     │
│                                                                 │
│  5. Return job with session                                     │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 Key Design Decisions

1. **Reservations are mandatory** for claim mode (not optional)
2. **Reservation creation is atomic** using file-based CAS
3. **Reservation TTL is short** (60 seconds) to limit blocking
4. **Sessions created only after successful reservation**
5. **Final claim verifies reservation** inside transaction
6. **Failed reservations trigger job re-selection** (not error)

### 5.3 Why This Approach

| Requirement | How Addressed |
|-------------|---------------|
| Single-process safety | Atomic reservation creation |
| Multi-process safety | Reservation files visible to all processes |
| Distributed safety | Git sync propagates reservations |
| No external deps | File-based coordination |
| Graceful degradation | TTL auto-releases abandoned reservations |
| Backward compatible | Reservation is internal implementation detail |
| Minimal UX change | Single `af ready` command still works |

---

## 6. Implementation Plan

### 6.1 Phase 1: Atomic Reservation Creation (Priority: Critical)

**Goal:** Prevent duplicate reservations for same mote.

**Files to modify:**
- `src/alethfeld/session.clj`

**Changes:**

```clojure
;; New function: create-reservation-atomic!
(defn create-reservation-atomic!
  "Atomically create a reservation, failing if one exists for this mote/role."
  [repo-path mote-id role]
  (let [token (generate-reservation-token)
        res-dir (io/full-path repo-path (path/reservations-path))
        ;; Use mote-id in filename for atomic check
        lock-file (io/full-path res-dir (str "lock-" (munge mote-id) ".edn"))]
    (io/ensure-dir res-dir)
    ;; Atomic file creation (fails if exists)
    (try
      (io/create-file-exclusive! lock-file
        {:token token
         :mote-id mote-id
         :role role
         :created-at (java.util.Date.)
         :expires-at (-> (Instant/now) (.plusSeconds 60) Date/from)})
      {:success true :token token}
      (catch java.nio.file.FileAlreadyExistsException _
        ;; Check if existing reservation is expired
        (let [existing (io/read-edn lock-file)]
          (if (reservation-expired? existing)
            (do
              (io/delete-file lock-file)
              (recur repo-path mote-id role))  ; Retry
            {:success false :held-by existing}))))))
```

**New I/O function needed:**

```clojure
;; In io.clj
(defn create-file-exclusive!
  "Create file only if it doesn't exist (atomic). Throws FileAlreadyExistsException if exists."
  [path content]
  (let [opts (into-array [java.nio.file.StandardOpenOption/CREATE_NEW
                          java.nio.file.StandardOpenOption/WRITE])]
    (with-open [writer (-> (java.nio.file.Paths/get path (into-array String []))
                           (java.nio.file.Files/newBufferedWriter opts))]
      (.write writer (pr-str content)))))
```

**Estimated effort:** 4-6 hours

---

### 6.2 Phase 2: Integrate Reservations into cmd-ready (Priority: Critical)

**Goal:** Make reservation acquisition part of normal claim flow.

**Files to modify:**
- `src/alethfeld/cmd.clj`

**Changes to `cmd-ready`:**

```clojure
;; Replace lines 910-960 with:
(seq jobs-with-prompts)
(loop [candidates jobs-with-prompts]
  (if (empty? candidates)
    ;; All candidates reserved by others
    {:mode :no-jobs
     :jobs []
     :output "All available jobs are currently reserved. Try again shortly."}

    (let [job (first candidates)
          mote-id (:mote-id job)
          job-role (:role job)
          ;; Attempt atomic reservation
          res-result (session/create-reservation-atomic! repo-path mote-id job-role)]
      (if (:success res-result)
        ;; Got reservation - proceed with session and claim
        (let [token (:token res-result)
              sess (session/create-session! repo-path mote-id job-role agent ...)
              updated-mote (mote/set-claimed-by (:mote job) agent)]
          ;; Write claim and consume reservation atomically
          (tx/with-validation repo-path
            (str "Claim " mote-id " for " agent)
            (fn [_]
              (store/save-mote! repo-path updated-mote)
              (session/delete-reservation! repo-path token)))
          {:mode :claimed :jobs [...] ...})

        ;; Reservation failed - try next candidate
        (recur (rest candidates))))))
```

**Estimated effort:** 6-8 hours

---

### 6.3 Phase 3: Cleanup Expired Reservations (Priority: High)

**Goal:** Prevent reservation file accumulation.

**Files to modify:**
- `src/alethfeld/session.clj`
- `src/alethfeld/cmd.clj`

**Changes:**

```clojure
;; Enhance cleanup-expired-reservations! to use lock files
(defn cleanup-expired-reservations!
  "Remove expired reservation lock files."
  [repo-path]
  (let [res-dir (io/full-path repo-path (path/reservations-path))
        lock-files (filter #(str/starts-with? (fs/file-name %) "lock-")
                           (io/list-edn-files res-dir))
        now (Instant/now)]
    (->> lock-files
         (filter (fn [f]
                   (let [res (io/read-edn f)]
                     (reservation-expired? res :now now))))
         (map (fn [f] (io/delete-file f) 1))
         (reduce + 0))))

;; Call at start of cmd-ready (already have cleanup-stale-sessions-and-claims!)
(defn- cleanup-stale-sessions-and-claims! [repo-path]
  ;; ... existing code ...
  (session/cleanup-expired-reservations! repo-path))  ; Add this
```

**Estimated effort:** 2-3 hours

---

### 6.4 Phase 4: Update job/select-jobs to Exclude Reserved (Priority: High)

**Goal:** Don't show reserved motes as available.

**Files to modify:**
- `src/alethfeld/job.clj`
- `src/alethfeld/cmd.clj`

**Changes:**

```clojure
;; Option A: Pass active reservations to select-jobs
(defn select-jobs
  [motes & {:keys [role difficulty priority max claim-timeout active-reservations]
            :or {max 1 active-reservations #{}}}]
  (->> (vals motes)
       (filter #(workable? % :claim-timeout claim-timeout))
       (remove #(contains? active-reservations (:id %)))  ; NEW
       (filter #(matches-filter? % {...}))
       ...))

;; In cmd-ready:
(let [active-reservations (set (map :mote-id (session/list-active-reservations repo-path)))
      jobs (job/select-jobs motes
                            :active-reservations active-reservations
                            ...)]
  ...)
```

**Estimated effort:** 2-3 hours

---

### 6.5 Phase 5: Add Multi-Process Tests (Priority: Medium)

**Goal:** Verify fix works across processes.

**New test file:** `test/alethfeld/multiprocess_test.clj`

```clojure
(deftest multiprocess-claim-race-test
  (testing "Two processes claiming same mote - only one succeeds"
    (let [repo-path (create-test-repo!)
          ;; Spawn two af processes
          p1 (process/process ["clj" "-M:run" "ready" "--name" "agent-1"]
                              {:dir repo-path})
          p2 (process/process ["clj" "-M:run" "ready" "--name" "agent-2"]
                              {:dir repo-path})]
      ;; Wait for both
      @p1 @p2
      ;; Verify only one claim
      (let [mote (store/load-mote repo-path "1")]
        (is (contains? #{"agent-1" "agent-2"} (:claimed-by mote)))
        ;; Verify only one active session
        (is (= 1 (count (session/load-sessions-for-mote repo-path "1"))))))))
```

**Estimated effort:** 4-6 hours

---

### 6.6 Phase 6: Documentation Updates (Priority: Medium)

**Files to update:**
- `docs/TECH-SPEC.md` - Add reservation protocol section
- `docs/draft/transactions.md` - Document claim atomicity
- `CLAUDE.md` - Update known limitations

**Estimated effort:** 2-3 hours

---

### 6.7 Implementation Timeline

| Phase | Description | Effort | Dependencies |
|-------|-------------|--------|--------------|
| 1 | Atomic reservation creation | 4-6h | None |
| 2 | Integrate into cmd-ready | 6-8h | Phase 1 |
| 3 | Cleanup expired reservations | 2-3h | Phase 1 |
| 4 | Exclude reserved from select-jobs | 2-3h | Phase 1 |
| 5 | Multi-process tests | 4-6h | Phases 1-4 |
| 6 | Documentation | 2-3h | Phases 1-4 |

**Total estimated effort:** 20-29 hours

---

## 7. Testing Strategy

### 7.1 Unit Tests

| Test Case | File | Description |
|-----------|------|-------------|
| `create-reservation-atomic!-success` | `session_test.clj` | Creates reservation when none exists |
| `create-reservation-atomic!-conflict` | `session_test.clj` | Fails when reservation exists |
| `create-reservation-atomic!-expired` | `session_test.clj` | Succeeds after expiration |
| `select-jobs-excludes-reserved` | `job_test.clj` | Reserved motes not returned |

### 7.2 Integration Tests

| Test Case | File | Description |
|-----------|------|-------------|
| `cmd-ready-reserves-before-claim` | `cmd_test.clj` | Reservation created before session |
| `cmd-ready-retries-on-reserved` | `cmd_test.clj` | Falls back to next job |
| `cmd-ready-cleans-expired` | `cmd_test.clj` | Expired reservations removed |

### 7.3 Concurrency Tests

| Test Case | File | Description |
|-----------|------|-------------|
| `concurrent-reserve-same-mote` | `concurrency_test.clj` | Only one reservation succeeds |
| `concurrent-claim-different-motes` | `concurrency_test.clj` | Both succeed (no conflict) |
| `reservation-timeout-allows-reclaim` | `concurrency_test.clj` | Expired reservation freed |

### 7.4 Multi-Process Tests

| Test Case | File | Description |
|-----------|------|-------------|
| `multiprocess-claim-race` | `multiprocess_test.clj` | Spawn two `af` processes |
| `multiprocess-reservation-visibility` | `multiprocess_test.clj` | Reservation file seen by both |

### 7.5 Stress Tests

```bash
# Run 10 parallel agents claiming from same pool
for i in {1..10}; do
  af ready --name "agent-$i" &
done
wait

# Verify: exactly N claims where N = number of available jobs
af check  # Should pass
```

---

## 8. Appendices

### 8.1 Appendix A: Current Code Flow (cmd-ready)

```
cmd-ready
├── Check repo exists
├── Handle --claim-reservation mode (separate path)
├── Normal flow:
│   ├── cleanup-stale-sessions-and-claims!
│   ├── Parse filters (difficulty, priority)
│   ├── load-config
│   ├── load-all-motes                    ← RACE: Read outside lock
│   ├── select-jobs                       ← RACE: Check outside lock
│   ├── Enrich with prompts
│   ├── Mode dispatch:
│   │   ├── --reserve: create-reservation!
│   │   ├── list-mode: format and return
│   │   ├── --no-claim: preview only
│   │   └── claim-mode:
│   │       ├── create-session!           ← RACE: Session outside lock
│   │       ├── set-claimed-by
│   │       └── atomic-write!             ← Only this is locked
│   └── Return result
```

### 8.2 Appendix B: Proposed Code Flow

```
cmd-ready
├── Check repo exists
├── cleanup-stale-sessions-and-claims!
├── cleanup-expired-reservations!         ← NEW
├── Parse filters
├── load-config
├── load-all-motes
├── list-active-reservations              ← NEW
├── select-jobs (excluding reserved)      ← MODIFIED
├── Enrich with prompts
├── Mode dispatch:
│   ├── --reserve: create-reservation-atomic!  ← MODIFIED (atomic)
│   ├── list-mode: format and return
│   ├── --no-claim: preview only
│   └── claim-mode:
│       └── loop over candidates:
│           ├── create-reservation-atomic!     ← NEW (atomic)
│           │   ├── success: proceed
│           │   └── failure: try next
│           ├── create-session!
│           └── with-validation:               ← NEW (atomic block)
│               ├── save-mote! (claim)
│               └── delete-reservation!
└── Return result
```

### 8.3 Appendix C: File-Based CAS Mechanism

The `create-file-exclusive!` function uses `StandardOpenOption/CREATE_NEW` which is atomic on POSIX filesystems:

```java
// Java NIO guarantees:
// CREATE_NEW: Create a new file, failing if the file already exists.
// This check and creation is atomic with respect to other filesystem operations.
```

This provides cross-process atomicity without external coordination.

### 8.4 Appendix D: Reservation File Format

```clojure
;; File: .alethfeld/sessions/reservations/lock-1.2.3.edn
{:token "a7f3x2"
 :mote-id "1.2.3"
 :role :verifier
 :created-at #inst "2026-01-09T10:30:00.000Z"
 :expires-at #inst "2026-01-09T10:31:00.000Z"}
```

### 8.5 Appendix E: Related Issues

- `test/alethfeld/concurrency_test.clj` - Documents limitation in comments
- `CLAUDE.md` - Documents race window in Known Limitations
- `docs/draft/transactions.md` - Documents race window

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-09 | Analysis | Initial report |

---

*End of Report*
