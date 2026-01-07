(ns alethfeld.fsm.queue-test
  "Tests for FSM queue operations.

   Tests cover:
   - add-to-expansion-queue / add-to-verification-queue
   - pop-expansion / pop-verification
   - get-queue-status
   - Queue ordering (FIFO)
   - Duplicate handling"
  (:require [clojure.test :refer [deftest testing is are]]
            [alethfeld.fsm.queue :as queue]
            [alethfeld.fsm.core :as fsm]
            [alethfeld.fixtures :as f]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(defn make-graph-with-queues
  "Create a test graph with FSM state and queues."
  [& {:keys [phase expansions verifications]
      :or {phase :expand-verify-loop
           expansions []
           verifications []}}]
  (assoc (f/make-graph [])
         :fsm {:phase phase
               :phase-entered-at "2024-01-01T12:00:00Z"
               :previous-phase nil
               :history []
               :pending {:expansions expansions
                         :verifications verifications}}))

;; =============================================================================
;; add-to-expansion-queue Tests
;; =============================================================================

(deftest add-to-expansion-queue-test
  (testing "Adds node-id to expansion queue"
    (let [g (make-graph-with-queues)
          result (queue/add-to-expansion-queue g :2-abc123)]
      (is (:ok result))
      (is (= [:2-abc123] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Appends to existing queue (FIFO)"
    (let [g (make-graph-with-queues :expansions [:2-first])
          result (queue/add-to-expansion-queue g :2-second)]
      (is (= [:2-first :2-second] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Handles multiple additions"
    (let [g (make-graph-with-queues)
          r1 (queue/add-to-expansion-queue g :2-a)
          r2 (queue/add-to-expansion-queue (:ok r1) :2-b)
          r3 (queue/add-to-expansion-queue (:ok r2) :2-c)]
      (is (= [:2-a :2-b :2-c] (get-in r3 [:ok :fsm :pending :expansions]))))))

(deftest add-to-expansion-queue-increments-version-test
  (testing "Adding to queue increments version"
    (let [g (make-graph-with-queues)
          result (queue/add-to-expansion-queue g :2-abc123)]
      (is (= 2 (:version (:ok result)))))))

(deftest add-to-expansion-queue-duplicate-test
  (testing "Does not add duplicate node-id"
    (let [g (make-graph-with-queues :expansions [:2-abc123])
          result (queue/add-to-expansion-queue g :2-abc123)]
      (is (:ok result))
      (is (= [:2-abc123] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Allows same node-id in different queues"
    (let [g (make-graph-with-queues :expansions [:2-abc123] :verifications [:2-abc123])]
      (is (= [:2-abc123] (get-in g [:fsm :pending :expansions])))
      (is (= [:2-abc123] (get-in g [:fsm :pending :verifications]))))))

(deftest add-to-expansion-queue-initializes-fsm-test
  (testing "Initializes FSM state if missing"
    (let [g (f/make-graph [])
          result (queue/add-to-expansion-queue g :2-abc123)]
      (is (:ok result))
      (is (some? (get-in result [:ok :fsm :pending])))
      (is (= [:2-abc123] (get-in result [:ok :fsm :pending :expansions]))))))

;; =============================================================================
;; add-to-verification-queue Tests
;; =============================================================================

(deftest add-to-verification-queue-test
  (testing "Adds node-id to verification queue"
    (let [g (make-graph-with-queues)
          result (queue/add-to-verification-queue g :2-abc123)]
      (is (:ok result))
      (is (= [:2-abc123] (get-in result [:ok :fsm :pending :verifications])))))

  (testing "Appends to existing queue (FIFO)"
    (let [g (make-graph-with-queues :verifications [:2-first])
          result (queue/add-to-verification-queue g :2-second)]
      (is (= [:2-first :2-second] (get-in result [:ok :fsm :pending :verifications])))))

  (testing "Does not add duplicate"
    (let [g (make-graph-with-queues :verifications [:2-abc123])
          result (queue/add-to-verification-queue g :2-abc123)]
      (is (= [:2-abc123] (get-in result [:ok :fsm :pending :verifications]))))))

(deftest add-to-verification-queue-increments-version-test
  (testing "Adding to queue increments version"
    (let [g (make-graph-with-queues)
          result (queue/add-to-verification-queue g :2-abc123)]
      (is (= 2 (:version (:ok result)))))))

;; =============================================================================
;; pop-expansion Tests
;; =============================================================================

(deftest pop-expansion-test
  (testing "Pops first item from expansion queue"
    (let [g (make-graph-with-queues :expansions [:2-first :2-second :2-third])
          result (queue/pop-expansion g)]
      (is (:ok result))
      (is (= :2-first (:node-id result)))
      (is (= [:2-second :2-third] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Returns nil node-id for empty queue"
    (let [g (make-graph-with-queues :expansions [])
          result (queue/pop-expansion g)]
      (is (:ok result))
      (is (nil? (:node-id result)))
      (is (= [] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Pop increments version"
    (let [g (make-graph-with-queues :expansions [:2-abc123])
          result (queue/pop-expansion g)]
      (is (= 2 (:version (:ok result)))))))

(deftest pop-expansion-fifo-test
  (testing "Pop follows FIFO order"
    (let [g (make-graph-with-queues :expansions [:2-a :2-b :2-c])
          r1 (queue/pop-expansion g)
          r2 (queue/pop-expansion (:ok r1))
          r3 (queue/pop-expansion (:ok r2))]
      (is (= :2-a (:node-id r1)))
      (is (= :2-b (:node-id r2)))
      (is (= :2-c (:node-id r3))))))

(deftest pop-expansion-initializes-fsm-test
  (testing "Returns nil node-id for graph without FSM"
    (let [g (f/make-graph [])
          result (queue/pop-expansion g)]
      (is (:ok result))
      (is (nil? (:node-id result))))))

;; =============================================================================
;; pop-verification Tests
;; =============================================================================

(deftest pop-verification-test
  (testing "Pops first item from verification queue"
    (let [g (make-graph-with-queues :verifications [:2-first :2-second])
          result (queue/pop-verification g)]
      (is (:ok result))
      (is (= :2-first (:node-id result)))
      (is (= [:2-second] (get-in result [:ok :fsm :pending :verifications])))))

  (testing "Returns nil node-id for empty queue"
    (let [g (make-graph-with-queues :verifications [])
          result (queue/pop-verification g)]
      (is (:ok result))
      (is (nil? (:node-id result)))))

  (testing "Pop increments version"
    (let [g (make-graph-with-queues :verifications [:2-abc123])
          result (queue/pop-verification g)]
      (is (= 2 (:version (:ok result)))))))

;; =============================================================================
;; get-queue-status Tests
;; =============================================================================

(deftest get-queue-status-test
  (testing "Returns both queues"
    (let [g (make-graph-with-queues :expansions [:2-a :2-b]
                                    :verifications [:2-c])
          status (queue/get-queue-status g)]
      (is (= [:2-a :2-b] (:expansions status)))
      (is (= [:2-c] (:verifications status)))))

  (testing "Returns empty vectors for empty queues"
    (let [g (make-graph-with-queues)
          status (queue/get-queue-status g)]
      (is (= [] (:expansions status)))
      (is (= [] (:verifications status)))))

  (testing "Returns empty for graph without FSM"
    (let [g (f/make-graph [])
          status (queue/get-queue-status g)]
      (is (= [] (:expansions status)))
      (is (= [] (:verifications status))))))

(deftest get-queue-status-counts-test
  (testing "Includes counts"
    (let [g (make-graph-with-queues :expansions [:2-a :2-b :2-c]
                                    :verifications [:2-d])
          status (queue/get-queue-status g)]
      (is (= 3 (:expansion-count status)))
      (is (= 1 (:verification-count status)))
      (is (= 4 (:total-pending status))))))

;; =============================================================================
;; queues-empty? Test
;; =============================================================================

(deftest queues-empty-test
  (testing "Returns true when both queues empty"
    (is (queue/queues-empty? (make-graph-with-queues)))
    (is (queue/queues-empty? (f/make-graph []))))

  (testing "Returns false when expansion queue has items"
    (is (not (queue/queues-empty? (make-graph-with-queues :expansions [:2-a])))))

  (testing "Returns false when verification queue has items"
    (is (not (queue/queues-empty? (make-graph-with-queues :verifications [:2-a]))))))

;; =============================================================================
;; Clear Queue Tests
;; =============================================================================

(deftest clear-expansion-queue-test
  (testing "Clears expansion queue"
    (let [g (make-graph-with-queues :expansions [:2-a :2-b])
          result (queue/clear-expansion-queue g)]
      (is (:ok result))
      (is (= [] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "Does not affect verification queue"
    (let [g (make-graph-with-queues :expansions [:2-a]
                                    :verifications [:2-b])
          result (queue/clear-expansion-queue g)]
      (is (= [:2-b] (get-in result [:ok :fsm :pending :verifications]))))))

(deftest clear-verification-queue-test
  (testing "Clears verification queue"
    (let [g (make-graph-with-queues :verifications [:2-a :2-b])
          result (queue/clear-verification-queue g)]
      (is (:ok result))
      (is (= [] (get-in result [:ok :fsm :pending :verifications])))))

  (testing "Does not affect expansion queue"
    (let [g (make-graph-with-queues :expansions [:2-a]
                                    :verifications [:2-b])
          result (queue/clear-verification-queue g)]
      (is (= [:2-a] (get-in result [:ok :fsm :pending :expansions]))))))

;; =============================================================================
;; Remove from Queue Tests
;; =============================================================================

(deftest remove-from-expansion-queue-test
  (testing "Removes specific node from expansion queue"
    (let [g (make-graph-with-queues :expansions [:2-a :2-b :2-c])
          result (queue/remove-from-expansion-queue g :2-b)]
      (is (:ok result))
      (is (= [:2-a :2-c] (get-in result [:ok :fsm :pending :expansions])))))

  (testing "No-op if node not in queue"
    (let [g (make-graph-with-queues :expansions [:2-a])
          result (queue/remove-from-expansion-queue g :2-not-there)]
      (is (:ok result))
      (is (= [:2-a] (get-in result [:ok :fsm :pending :expansions]))))))

(deftest remove-from-verification-queue-test
  (testing "Removes specific node from verification queue"
    (let [g (make-graph-with-queues :verifications [:2-a :2-b :2-c])
          result (queue/remove-from-verification-queue g :2-b)]
      (is (:ok result))
      (is (= [:2-a :2-c] (get-in result [:ok :fsm :pending :verifications]))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest nil-graph-handling-test
  (testing "Handles nil graph gracefully for get-queue-status"
    (let [status (queue/get-queue-status nil)]
      (is (= [] (:expansions status)))
      (is (= [] (:verifications status))))))

(deftest multiple-queue-operations-test
  (testing "Complex sequence of operations"
    (let [g (make-graph-with-queues)
          ;; Add several items
          r1 (queue/add-to-expansion-queue g :2-a)
          r2 (queue/add-to-expansion-queue (:ok r1) :2-b)
          r3 (queue/add-to-verification-queue (:ok r2) :2-c)
          ;; Pop one expansion
          r4 (queue/pop-expansion (:ok r3))
          ;; Check state
          status (queue/get-queue-status (:ok r4))]
      (is (= :2-a (:node-id r4)))
      (is (= [:2-b] (:expansions status)))
      (is (= [:2-c] (:verifications status)))
      (is (= 2 (:total-pending status))))))
