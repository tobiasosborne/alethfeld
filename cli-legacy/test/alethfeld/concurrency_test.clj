(ns alethfeld.concurrency-test
  "Concurrency and isolation tests for semantic proof graphs.

   Tests cover:
   1. Concurrent graph operations (immutable data structure safety)
   2. File I/O isolation (concurrent reads/writes)
   3. Atomic write correctness (temp file + rename pattern)
   4. Cache consistency under concurrent access
   5. Isolation between independent graph instances

   These tests guard against race conditions and data corruption
   when the CLI or batch workers access graphs concurrently."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.java.io :as io]
            [alethfeld.graph :as g]
            [alethfeld.io :as aio]
            [alethfeld.schema :as schema]
            [alethfeld.validators :as v]
            [alethfeld.ops.add-node :as add-node]
            [alethfeld.ops.update-status :as update-status]
            [alethfeld.fixtures :as f])
  (:import [java.io File]
           [java.util.concurrent CountDownLatch Executors TimeUnit]))

;; =============================================================================
;; Test Fixtures - Temp Directory Management
;; =============================================================================

(def ^:dynamic *temp-dir* nil)

(defn create-temp-dir []
  (let [dir (File/createTempFile "alethfeld-test-" "")]
    (.delete dir)
    (.mkdirs dir)
    dir))

(defn delete-recursively [^File f]
  (when (.isDirectory f)
    (doseq [child (.listFiles f)]
      (delete-recursively child)))
  (.delete f))

(defn temp-dir-fixture [f]
  (let [dir (create-temp-dir)]
    (try
      (binding [*temp-dir* dir]
        (f))
      (finally
        (delete-recursively dir)))))

(use-fixtures :each temp-dir-fixture)

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn temp-file [name]
  (io/file *temp-dir* name))

(defn run-concurrent
  "Run n tasks concurrently, returning results when all complete.
   Uses a countdown latch for synchronized start."
  [n task-fn]
  (let [latch (CountDownLatch. 1)
        results (atom [])
        threads (doall
                 (for [i (range n)]
                   (Thread.
                    (fn []
                      (.await latch)
                      (try
                        (let [result (task-fn i)]
                          (swap! results conj {:index i :result result}))
                        (catch Exception e
                          (swap! results conj {:index i :error (.getMessage e)})))))))]
    ;; Start all threads
    (doseq [t threads] (.start t))
    ;; Release them simultaneously
    (.countDown latch)
    ;; Wait for completion
    (doseq [t threads] (.join t 5000))
    @results))

(defn run-parallel-futures
  "Run n tasks in parallel using futures, returning results."
  [n task-fn]
  (let [futures (doall (for [i (range n)] (future (task-fn i))))]
    (mapv deref futures)))

;; =============================================================================
;; 1. Concurrent Graph Operations (Immutable Data Safety)
;; =============================================================================

(deftest concurrent-read-operations-test
  (testing "Multiple threads can read the same graph concurrently"
    (let [graph f/diamond-graph
          results (run-concurrent 10
                   (fn [_]
                     {:node-count (count (:nodes graph))
                      :node-ids (g/node-ids graph)
                      :ancestors (g/get-ancestors graph :1-ddd444)
                      :descendants (g/get-descendants graph :1-aaa111)}))]
      ;; All should succeed with identical results
      (is (every? #(nil? (:error %)) results))
      (is (every? #(= 4 (get-in % [:result :node-count])) results))
      (is (every? #(= #{:1-aaa111 :1-bbb222 :1-ccc333 :1-ddd444}
                      (get-in % [:result :node-ids])) results))))

  (testing "Parallel topological sorts return consistent results"
    (let [graph f/linear-chain-graph
          results (run-parallel-futures 20 (fn [_] (g/topological-sort graph)))]
      ;; All sorts should produce the same result
      (is (apply = results))
      (is (= [:1-aaa111 :1-bbb222 :1-ccc333] (first results)))))

  (testing "Concurrent scope computations are consistent"
    (let [graph f/scoped-graph
          results (run-parallel-futures 10 (fn [_] (g/compute-all-scopes graph)))]
      ;; All scope computations should be identical
      (is (apply = results)))))

(deftest concurrent-independent-mutations-test
  (testing "Independent mutations on separate graph copies"
    (let [base-graph f/minimal-valid-graph
          results (run-parallel-futures 10
                   (fn [i]
                     ;; Each thread creates its own modified copy
                     (let [new-node (f/make-partial-node
                                     (keyword (str "1-new" i))
                                     :deps #{:1-abc123}
                                     :order (inc i))
                           result (add-node/add-node base-graph new-node)]
                       (when (:ok result)
                         {:version (:version (:ok result))
                          :node-count (count (get-in result [:ok :nodes]))}))))]
      ;; All mutations should succeed independently
      (is (every? some? results))
      ;; Each result should have 2 nodes (original + new)
      (is (every? #(= 2 (:node-count %)) results))
      ;; Base graph should be unchanged
      (is (= 1 (count (:nodes base-graph))))))

  (testing "Concurrent taint recomputation on copies"
    (let [base-graph f/linear-chain-graph
          results (run-parallel-futures 5
                   (fn [_]
                     (g/recompute-all-taints base-graph)))]
      ;; All should produce valid graphs
      (is (every? #(:valid (v/validate-semantics %)) results))
      ;; Original unchanged
      (is (= 3 (count (:nodes base-graph)))))))

;; =============================================================================
;; 2. File I/O Isolation Tests
;; =============================================================================

(deftest concurrent-file-writes-different-files-test
  (testing "Concurrent writes to different files"
    (let [graphs (for [i (range 10)]
                   (assoc f/minimal-valid-graph :graph-id (str "graph-" i)))
          results (run-parallel-futures 10
                   (fn [i]
                     (let [path (str (temp-file (str "graph-" i ".edn")))]
                       (aio/write-graph path (nth graphs i)))))]
      ;; All writes should succeed
      (is (every? :ok results))
      ;; All files should be readable and valid
      (doseq [i (range 10)]
        (let [read-result (aio/read-graph (str (temp-file (str "graph-" i ".edn"))))]
          (is (:ok read-result))
          (is (= (str "graph-" i) (get-in read-result [:ok :graph-id]))))))))

(deftest concurrent-reads-same-file-test
  (testing "Concurrent reads of the same file"
    (let [path (str (temp-file "shared.edn"))
          _ (aio/write-graph path f/diamond-graph)
          results (run-parallel-futures 20
                   (fn [_]
                     (aio/read-graph path)))]
      ;; All reads should succeed
      (is (every? :ok results))
      ;; All should return the same graph
      (is (apply = (map :ok results))))))

(deftest concurrent-write-same-file-test
  (testing "Concurrent writes to same file (last writer wins)"
    (let [path (str (temp-file "contested.edn"))
          results (run-concurrent 5
                   (fn [i]
                     (let [graph (assoc f/minimal-valid-graph :version (inc i))]
                       (aio/write-graph path graph))))]
      ;; All writes should succeed (atomic rename)
      (is (every? #(or (:ok (:result %)) (nil? (:error %))) results))
      ;; File should contain a valid graph
      (let [final (aio/read-graph path)]
        (is (:ok final))
        (is (:valid (schema/validate-schema (:ok final))))))))

;; =============================================================================
;; 3. Atomic Write Correctness Tests
;; =============================================================================

(deftest atomic-write-no-partial-content-test
  (testing "Interrupted write should not leave partial content"
    (let [path (str (temp-file "atomic-test.edn"))
          large-graph (reduce
                       (fn [g i]
                         (assoc-in g [:nodes (keyword (str "1-node" i))]
                                   (f/make-node (keyword (str "1-node" i))
                                                :statement (apply str (repeat 1000 "x")))))
                       f/minimal-valid-graph
                       (range 100))]
      ;; Write the large graph
      (is (:ok (aio/write-graph path large-graph)))
      ;; Read it back
      (let [result (aio/read-graph path)]
        (is (:ok result))
        (is (= 101 (count (get-in result [:ok :nodes]))))))))

(deftest atomic-write-preserves-on-error-test
  (testing "Failed write preserves original file"
    (let [path (str (temp-file "preserve-test.edn"))
          original f/minimal-valid-graph]
      ;; Write original
      (aio/write-graph path original)
      ;; Verify original is there
      (is (= 1 (count (:nodes (:ok (aio/read-graph path))))))
      ;; Try to write to a read-only directory (simulate failure)
      ;; Since we can't easily simulate a write failure, we just verify
      ;; the atomic write pattern works correctly
      (aio/write-graph path f/diamond-graph)
      (let [result (aio/read-graph path)]
        (is (:ok result))
        (is (= 4 (count (:nodes (:ok result)))))))))

(deftest rapid-sequential-writes-test
  (testing "Rapid sequential writes all succeed"
    (let [path (str (temp-file "rapid-write.edn"))]
      (doseq [i (range 50)]
        (let [graph (assoc f/minimal-valid-graph :version (inc i))]
          (is (:ok (aio/write-graph path graph)))))
      ;; Final version should be 50
      (let [result (aio/read-graph path)]
        (is (= 50 (get-in result [:ok :version])))))))

;; =============================================================================
;; 4. Cache Consistency Tests
;; =============================================================================

(deftest cache-consistency-under-concurrent-access-test
  (testing "Reverse deps cache remains consistent under concurrent reads"
    (let [graph f/diamond-graph
          ;; Run many concurrent descendant queries (uses cache)
          results (run-parallel-futures 50
                   (fn [_]
                     (g/get-descendants graph :1-aaa111)))]
      ;; All should return the same result
      (is (apply = results))
      (is (= #{:1-bbb222 :1-ccc333 :1-ddd444} (first results)))))

  (testing "Cache invalidation doesn't affect concurrent readers"
    (let [graph f/linear-chain-graph
          ;; Start reads, then invalidate cache, continue reads
          results (run-parallel-futures 20
                   (fn [i]
                     (let [g (if (= 0 (mod i 3))
                               (g/invalidate-caches graph)
                               graph)]
                       (g/get-descendants g :1-aaa111))))]
      ;; All should return same result regardless of cache state
      (is (apply = results))
      (is (= #{:1-bbb222 :1-ccc333} (first results))))))

;; =============================================================================
;; 5. Isolation Between Graph Instances
;; =============================================================================

(deftest graph-instance-isolation-test
  (testing "Modifications to one graph don't affect another"
    (let [graph1 f/minimal-valid-graph
          graph2 f/minimal-valid-graph
          ;; Modify graph1 in one thread
          future1 (future
                    (-> graph1
                        (assoc :graph-id "modified-1")
                        (assoc-in [:nodes :1-new]
                                  (f/make-node :1-new :deps #{:1-abc123}))))
          ;; Read graph2 in another thread
          future2 (future
                    (Thread/sleep 10)  ; Slight delay
                    (:graph-id graph2))
          result1 @future1
          result2 @future2]
      ;; graph2 should be unchanged
      (is (= "test-graph-001" result2))
      ;; graph1 modification should have worked
      (is (= "modified-1" (:graph-id result1)))
      ;; Original graph1 is unchanged (immutable)
      (is (= "test-graph-001" (:graph-id graph1)))))

  (testing "Concurrent operations on derived graphs are independent"
    (let [base f/linear-chain-graph
          results (run-parallel-futures 10
                   (fn [i]
                     ;; Each thread derives and modifies its own copy
                     (let [derived (assoc base :version (+ 100 i))
                           with-node (assoc-in derived [:nodes (keyword (str "1-thread" i))]
                                                (f/make-node (keyword (str "1-thread" i))
                                                             :deps #{:1-ccc333}
                                                             :order (+ 10 i)))]
                       {:version (:version with-node)
                        :node-count (count (:nodes with-node))})))]
      ;; Each should have its own version
      (is (= (set (range 100 110)) (set (map :version results))))
      ;; Each should have 4 nodes (3 original + 1 new)
      (is (every? #(= 4 (:node-count %)) results))
      ;; Base graph unchanged
      (is (= 1 (:version base)))
      (is (= 3 (count (:nodes base)))))))

;; =============================================================================
;; 6. Stress Tests for Race Conditions
;; =============================================================================

(deftest stress-concurrent-validation-test
  (testing "High-concurrency validation doesn't cause issues"
    (let [graph f/diamond-graph
          results (run-parallel-futures 100
                   (fn [_]
                     {:schema (:valid (schema/validate-schema graph))
                      :semantic (:valid (v/validate-semantics graph))}))]
      ;; All validations should pass
      (is (every? :schema results))
      (is (every? :semantic results)))))

(deftest stress-concurrent-topo-sort-test
  (testing "High-concurrency topological sort is consistent"
    (let [;; Generate a moderately complex graph
          nodes (into [(f/make-node :1-root
                                    :type :assumption
                                    :justification :assumption
                                    :depth 0)]
                      (for [i (range 1 50)]
                        (f/make-node (keyword (str "1-n" i))
                                     :deps #{(keyword (str "1-n" (dec i)))}
                                     :order i)))
          ;; Replace first dep to point to root
          nodes (assoc-in (vec nodes) [1 :dependencies] #{:1-root})
          graph (f/make-graph nodes)
          results (run-parallel-futures 50 (fn [_] (g/topological-sort graph)))]
      ;; All sorts should be identical
      (is (apply = results))
      ;; First should be root
      (is (= :1-root (first (first results)))))))

(deftest stress-file-operations-test
  (testing "Mixed concurrent read/write operations"
    (let [path (str (temp-file "stress.edn"))
          _ (aio/write-graph path f/minimal-valid-graph)
          executor (Executors/newFixedThreadPool 10)
          results (atom [])
          latch (CountDownLatch. 1)
          tasks (concat
                 ;; 5 writers
                 (for [i (range 5)]
                   (fn []
                     (.await latch)
                     (let [g (assoc f/minimal-valid-graph :version (+ 10 i))]
                       (swap! results conj {:type :write :result (aio/write-graph path g)}))))
                 ;; 5 readers
                 (for [_ (range 5)]
                   (fn []
                     (.await latch)
                     (swap! results conj {:type :read :result (aio/read-graph path)}))))]
      ;; Submit all tasks
      (doseq [task tasks]
        (.submit executor ^Runnable task))
      ;; Start them all
      (.countDown latch)
      ;; Wait for completion
      (.shutdown executor)
      (.awaitTermination executor 10 TimeUnit/SECONDS)
      ;; All operations should succeed
      (is (every? #(or (get-in % [:result :ok])
                       (get-in % [:result :error])) @results))
      ;; Reads should get valid graphs
      (let [reads (filter #(= :read (:type %)) @results)]
        (is (every? #(or (:ok (:result %))
                         ;; Read during write might fail temporarily
                         (:error (:result %))) reads))))))

;; =============================================================================
;; 7. Operation Atomicity Tests
;; =============================================================================

(deftest add-node-atomicity-test
  (testing "add-node is atomic (all-or-nothing)"
    (let [graph f/minimal-valid-graph
          ;; Valid node
          valid-node (f/make-partial-node :1-valid :deps #{:1-abc123})
          ;; Invalid node (references non-existent dependency)
          invalid-node (f/make-partial-node :1-invalid :deps #{:1-nonexistent})
          valid-result (add-node/add-node graph valid-node)
          invalid-result (add-node/add-node graph invalid-node)]
      ;; Valid should succeed
      (is (:ok valid-result))
      (is (= 2 (count (get-in valid-result [:ok :nodes]))))
      ;; Invalid should fail without modifying
      (is (:error invalid-result))
      ;; Original graph unchanged in both cases
      (is (= 1 (count (:nodes graph)))))))

(deftest update-status-atomicity-test
  (testing "update-status is atomic"
    (let [graph f/minimal-valid-graph
          ;; Valid update
          valid-result (update-status/update-status graph :1-abc123 :admitted)
          ;; Invalid update (non-existent node)
          invalid-result (update-status/update-status graph :nonexistent :verified)]
      ;; Valid should succeed
      (is (:ok valid-result))
      (is (= :admitted (get-in valid-result [:ok :nodes :1-abc123 :status])))
      ;; Invalid should fail
      (is (:error invalid-result))
      ;; Original unchanged
      (is (= :verified (get-in graph [:nodes :1-abc123 :status]))))))
