# Testing

Approximately 11,500 lines of tests covering all modules. Test-driven development is the norm.

## Running Tests

```bash
# All tests
clj -M:test

# Specific namespace
clj -M:test -n alethfeld.dag-test
```

## Test Organization

Tests mirror source structure:

```
test/alethfeld/
├── schema_test.clj          # Schema validation
├── id_test.clj              # ID parsing
├── id_property_test.clj     # Property-based ID tests
├── mote_test.clj            # Mote transformations
├── io_test.clj              # File I/O
├── path_test.clj            # Path derivation
├── store_test.clj           # Persistence CRUD
├── dag_test.clj             # Graph validation
├── job_test.clj             # Job selection
├── git_test.clj             # Git operations
├── tx_test.clj              # Transactions
├── verify_test.clj          # Voting/quorum
├── proposal_test.clj        # Decomposition workflow
├── session_test.clj         # Session management
├── prompt_test.clj          # Prompt rendering
├── cli_test.clj             # CLI parsing
├── errors_test.clj          # Error formatting
├── cmd/                     # Command tests (17 files)
│   ├── init_test.clj
│   ├── show_test.clj
│   ├── create_test.clj
│   └── ...
├── integration_test.clj     # End-to-end workflows
├── concurrency_test.clj     # Thread safety
└── propagation_test.clj     # DAG propagation
```

## Conventions

### Namespace Naming

```clojure
;; Source
(ns alethfeld.foo)

;; Test
(ns alethfeld.foo-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.foo :as foo]))
```

### Test Structure

```clojure
(deftest function-name-test
  (testing "describes behavior under test"
    (is (= expected (function-under-test args)))))

(deftest another-function-test
  (testing "success case"
    (is (some? (fn-that-returns-value))))

  (testing "failure case"
    (is (thrown? ExceptionInfo (fn-that-throws)))))
```

### Fixtures

Common pattern for tests requiring temp directory:

```clojure
(defn with-temp-repo [f]
  (let [dir (fs/create-temp-dir)]
    (try
      (f dir)
      (finally
        (fs/delete-tree dir)))))

(deftest something-test
  (with-temp-repo
    (fn [repo-path]
      ;; test body
      )))
```

## Test Categories

### Unit Tests

Isolated function tests. No I/O, no state.

```clojure
(deftest parse-id-test
  (testing "parses dot-separated integers"
    (is (= [1 2 3] (id/parse-id "1.2.3")))))
```

### Integration Tests

Full command workflows with filesystem and git.

```clojure
(deftest full-verification-workflow-test
  (with-temp-repo
    (fn [repo]
      ;; Init repo
      (cmd/cmd-init! repo)

      ;; Create mote
      (cmd/cmd-create repo "1" "claim" "agent-1")

      ;; Vote
      (cmd/cmd-vote repo "1" :for "verifier-1")
      (cmd/cmd-vote repo "1" :for "verifier-2")
      (cmd/cmd-vote repo "1" :for "verifier-3")

      ;; Verify status changed
      (is (= :verified (:status (store/load-mote repo "1")))))))
```

### Property Tests

Generative testing for invariants.

```clojure
(defspec id-roundtrip-property 100
  (prop/for-all [components (gen/vector (gen/choose 1 1000) 1 5)]
    (= components
       (id/parse-id (id/format-id components)))))
```

### Concurrency Tests

Thread safety verification.

```clojure
(deftest concurrent-votes-test
  (with-temp-repo
    (fn [repo]
      (cmd/cmd-init! repo)
      (cmd/cmd-create repo "1" "claim" "agent")

      ;; 10 threads voting simultaneously
      (let [futures (for [i (range 10)]
                      (future
                        (cmd/cmd-vote repo "1" :for (str "v" i))))]
        (doseq [f futures] @f))

      ;; All votes recorded
      (is (= 10 (count (:votes (store/load-mote repo "1"))))))))
```

## Coverage Areas

### Schema Validation

- Valid structures accepted
- Invalid structures rejected with clear errors
- Edge cases (empty strings, nil values, boundary integers)

### ID Operations

- Parsing and formatting roundtrip
- Parent/child derivation
- Ancestry queries
- Next-child allocation

### DAG Validation

- Parent-child bidirectional consistency
- Cycle detection
- Internal reference validity
- Assumption graph acyclicity
- Proposal atomicity

### Transactions

- Lock acquisition and release
- Validation before commit
- Git commit on success
- Rollback on failure (no commit)

### Sessions

- Creation and expiration
- Role enforcement
- Action validation
- Contributor exclusion from voting

### Commands

Each command has dedicated tests:
- Success paths
- Error conditions
- Edge cases
- Output format verification

## Mocking

Git operations can be mocked for faster tests:

```clojure
(with-redefs [git/git-commit! (fn [& _] nil)]
  ;; test without actual commits
  )
```

Use sparingly—prefer real git operations for integration tests.

## Test Data

Common test fixtures in test namespaces:

```clojure
(def sample-mote
  {:id "1"
   :claim "Test claim"
   :status :fixed
   :taint #{}
   :priority :p2
   :difficulty 2
   :parent nil
   :children []
   :assumptions []
   :definitions []
   :votes []
   :created-by "test-agent"
   :created-at (java.util.Date.)})
```

## Debugging Tests

```bash
# Run with verbose output
clj -M:test -v

# Run single test
clj -M:test -v -n alethfeld.dag-test/detect-cycles-test
```

Add `(println ...)` or use `clojure.pprint/pprint` for inspection during development.
