(ns alethfeld.ops.external-ref-test
  (:require [clojure.test :refer [deftest testing is]]
            [alethfeld.ops.external-ref :as ext-ref]
            [alethfeld.schema :as schema]
            [alethfeld.fixtures :as f]))

(deftest add-external-ref-test
  (testing "Add external ref with DOI"
    (let [ref {:doi "10.1234/example"
               :claimed-statement "The theorem states..."}
          result (ext-ref/add-external-ref f/empty-nodes-graph ref)]
      (is (:ok result))
      (is (string? (:ref-id result)))
      (let [g (:ok result)
            added-ref (get-in g [:external-refs (:ref-id result)])]
        (is (= :pending (:verification-status added-ref)))
        (is (= "10.1234/example" (:doi added-ref))))))

  (testing "Add external ref with arXiv"
    (let [ref {:arxiv "2401.12345"
               :claimed-statement "The lemma shows..."}
          result (ext-ref/add-external-ref f/empty-nodes-graph ref)]
      (is (:ok result))))

  (testing "Add external ref with URL only"
    (let [ref {:url "https://example.com/paper.pdf"
               :claimed-statement "According to..."}
          result (ext-ref/add-external-ref f/empty-nodes-graph ref)]
      (is (:ok result))))

  (testing "Reject ref without identifier"
    (let [ref {:claimed-statement "No identifier"}
          result (ext-ref/add-external-ref f/empty-nodes-graph ref)]
      (is (:error result))
      (is (some #(= :no-identifier (:type %)) (:error result)))))

  (testing "Reject ref without claimed statement"
    (let [ref {:doi "10.1234/example"}
          result (ext-ref/add-external-ref f/empty-nodes-graph ref)]
      (is (:error result))
      (is (some #(= :missing-claimed-statement (:type %)) (:error result))))))

(deftest update-external-ref-test
  (testing "Update ref to verified"
    (let [;; First add a ref
          add-result (ext-ref/add-external-ref f/empty-nodes-graph
                                               {:doi "10.1234/example"
                                                :claimed-statement "Claim"})
          graph (:ok add-result)
          ref-id (:ref-id add-result)
          ;; Then update it
          update-result (ext-ref/update-external-ref graph ref-id
                                                     {:status :verified
                                                      :verified-statement "Verified claim"
                                                      :bibdata {:authors ["A"]
                                                                :title "Title"
                                                                :year 2024}})]
      (is (:ok update-result))
      (let [updated (get-in (:ok update-result) [:external-refs ref-id])]
        (is (= :verified (:verification-status updated)))
        (is (= "Verified claim" (:verified-statement updated)))
        (is (= 2024 (get-in updated [:bibdata :year]))))))

  (testing "Update ref to mismatch"
    (let [add-result (ext-ref/add-external-ref f/empty-nodes-graph
                                               {:doi "10.1234/example"
                                                :claimed-statement "Claim"})
          graph (:ok add-result)
          ref-id (:ref-id add-result)
          update-result (ext-ref/update-external-ref graph ref-id
                                                     {:status :mismatch
                                                      :notes "Statement differs"})]
      (is (:ok update-result))
      (is (= :mismatch (get-in (:ok update-result) [:external-refs ref-id :verification-status])))))

  (testing "Reject update of non-existent ref"
    (let [result (ext-ref/update-external-ref f/empty-nodes-graph "nonexistent"
                                              {:status :verified})]
      (is (:error result))
      (is (some #(= :ref-not-found (:type %)) (:error result)))))

  (testing "Reject invalid status"
    (let [add-result (ext-ref/add-external-ref f/empty-nodes-graph
                                               {:doi "10.1234/example"
                                                :claimed-statement "Claim"})
          graph (:ok add-result)
          ref-id (:ref-id add-result)
          result (ext-ref/update-external-ref graph ref-id {:status :invalid})]
      (is (:error result))
      (is (some #(= :invalid-status (:type %)) (:error result))))))

(deftest multiple-refs-test
  (testing "Multiple refs can coexist"
    (let [result1 (ext-ref/add-external-ref f/empty-nodes-graph
                                            {:doi "10.1234/first"
                                             :claimed-statement "First"})
          result2 (ext-ref/add-external-ref (:ok result1)
                                            {:arxiv "2401.00001"
                                             :claimed-statement "Second"})]
      (is (:ok result2))
      (is (= 2 (count (:external-refs (:ok result2))))))))

(deftest version-increment-test
  (testing "Version incremented after add"
    (let [result (ext-ref/add-external-ref f/empty-nodes-graph
                                           {:doi "10.1234/example"
                                            :claimed-statement "Claim"})]
      (is (= 2 (:version (:ok result)))))))
