(ns alethfeld.util
  "Shared utility functions and definitions.

   This namespace contains common code used across multiple modules.")

;; -----------------------------------------------------------------------------
;; Levenshtein Distance
;; -----------------------------------------------------------------------------

(defn levenshtein-distance
  "Calculate the Levenshtein (edit) distance between two strings.
   Returns the minimum number of single-character edits (insertions,
   deletions, or substitutions) required to transform s1 into s2."
  [s1 s2]
  (let [len1 (count s1)
        len2 (count s2)]
    (cond
      (zero? len1) len2
      (zero? len2) len1
      :else
      (let [;; Create initial row [0 1 2 ... len2]
            initial-row (vec (range (inc len2)))]
        (loop [i 0
               prev-row initial-row]
          (if (>= i len1)
            (last prev-row)
            (let [c1 (nth s1 i)
                  curr-row (loop [j 0
                                  row [(inc i)]]
                             (if (>= j len2)
                               row
                               (let [c2 (nth s2 j)
                                     cost (if (= c1 c2) 0 1)
                                     insert (inc (nth row j))
                                     delete (inc (nth prev-row (inc j)))
                                     substitute (+ (nth prev-row j) cost)]
                                 (recur (inc j)
                                        (conj row (min insert delete substitute))))))]
              (recur (inc i) curr-row))))))))

;; -----------------------------------------------------------------------------
;; Role Definitions
;; -----------------------------------------------------------------------------

(def valid-roles
  "Map of valid role keywords to their descriptions."
  {:proposer      "Break claims into sub-claims"
   :advisor       "Review and approve/reject proposals"
   :prover        "Add references and refine claims"
   :verifier      "Vote on claim validity"
   :ref-checker   "Validate external references"
   :counterexample "Find flaws and counterexamples"})

(def valid-role-names
  "Vector of valid role names as strings for CLI display."
  (mapv name (keys valid-roles)))
