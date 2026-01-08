(ns alethfeld.id
  "MoteId parsing and manipulation functions.

   MoteIds are hierarchical Lamport-style identifiers like \"1\", \"1.2\", \"1.2.3\".
   Each component is a positive integer. The hierarchy represents parent-child
   relationships in the proof DAG."
  (:require [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Parsing
;; -----------------------------------------------------------------------------

(defn parse-id
  "Parse a MoteId string into a vector of integer components.

   Examples:
     (parse-id \"1\")     => [1]
     (parse-id \"1.2.3\") => [1 2 3]

   Returns nil if the ID is invalid."
  [id]
  (when (and (string? id)
             (not (str/blank? id))
             (re-matches #"\d+(\.\d+)*" id))
    (mapv parse-long (str/split id #"\."))))

(defn valid-id?
  "Check if a string is a valid MoteId."
  [id]
  (some? (parse-id id)))

(defn format-id
  "Format a vector of components back into a MoteId string.

   Examples:
     (format-id [1])     => \"1\"
     (format-id [1 2 3]) => \"1.2.3\""
  [components]
  (str/join "." components))

;; -----------------------------------------------------------------------------
;; Navigation
;; -----------------------------------------------------------------------------

(defn id-depth
  "Return the depth of an ID (number of components).
   Root motes have depth 1.

   Examples:
     (id-depth \"1\")     => 1
     (id-depth \"1.2.3\") => 3"
  [id]
  (when-let [parts (parse-id id)]
    (count parts)))

(defn root-id
  "Return the root ID for a given ID.

   Examples:
     (root-id \"1\")     => \"1\"
     (root-id \"1.2.3\") => \"1\""
  [id]
  (when-let [parts (parse-id id)]
    (str (first parts))))

(defn parent-id
  "Return the parent ID, or nil if this is a root mote.

   Examples:
     (parent-id \"1\")     => nil
     (parent-id \"1.2\")   => \"1\"
     (parent-id \"1.2.3\") => \"1.2\""
  [id]
  (when-let [parts (parse-id id)]
    (when (> (count parts) 1)
      (format-id (butlast parts)))))

(defn child-id
  "Create a child ID by appending a component number.

   Examples:
     (child-id \"1\" 2)   => \"1.2\"
     (child-id \"1.2\" 3) => \"1.2.3\""
  [id n]
  (when-let [parts (parse-id id)]
    (when (and (integer? n) (pos? n))
      (format-id (conj parts n)))))

(defn next-child-id
  "Given a parent ID and existing children, return the next available child ID.

   Examples:
     (next-child-id \"1\" [])              => \"1.1\"
     (next-child-id \"1\" [\"1.1\" \"1.2\"]) => \"1.3\"
     (next-child-id \"1\" [\"1.1\" \"1.3\"]) => \"1.4\" ; gaps are not filled"
  [parent-id existing-children]
  (when (valid-id? parent-id)
    (let [child-nums (->> existing-children
                          (keep parse-id)
                          (filter #(= (count %) (inc (count (parse-id parent-id)))))
                          (map last))
          next-num (if (empty? child-nums)
                     1
                     (inc (apply max child-nums)))]
      (child-id parent-id next-num))))

;; -----------------------------------------------------------------------------
;; Ancestry
;; -----------------------------------------------------------------------------

(defn is-ancestor?
  "Check if ancestor-id is an ancestor of descendant-id.
   A mote is not considered its own ancestor.

   Examples:
     (is-ancestor? \"1\" \"1.2\")     => true
     (is-ancestor? \"1\" \"1.2.3\")   => true
     (is-ancestor? \"1.2\" \"1.2.3\") => true
     (is-ancestor? \"1\" \"1\")       => false
     (is-ancestor? \"1.2\" \"1.3\")   => false
     (is-ancestor? \"2\" \"1.2\")     => false"
  [ancestor-id descendant-id]
  (when-let [ancestor-parts (parse-id ancestor-id)]
    (when-let [descendant-parts (parse-id descendant-id)]
      (let [ancestor-count (count ancestor-parts)]
        (and (< ancestor-count (count descendant-parts))
             (= ancestor-parts (subvec descendant-parts 0 ancestor-count)))))))

(defn is-descendant?
  "Check if descendant-id is a descendant of ancestor-id.
   Inverse of is-ancestor?."
  [descendant-id ancestor-id]
  (is-ancestor? ancestor-id descendant-id))

(defn is-sibling?
  "Check if two IDs are siblings (share same parent).
   A mote is not considered its own sibling.

   Examples:
     (is-sibling? \"1.1\" \"1.2\") => true
     (is-sibling? \"1.1\" \"1.1\") => false
     (is-sibling? \"1.1\" \"2.1\") => false"
  [id1 id2]
  (and (not= id1 id2)
       (= (parent-id id1) (parent-id id2))
       (some? (parent-id id1))))

(defn ancestor-ids
  "Return a vector of all ancestor IDs, from immediate parent to root.

   Examples:
     (ancestor-ids \"1\")     => []
     (ancestor-ids \"1.2\")   => [\"1\"]
     (ancestor-ids \"1.2.3\") => [\"1.2\" \"1\"]"
  [id]
  (when-let [parts (parse-id id)]
    (loop [current (butlast parts)
           result []]
      (if (empty? current)
        result
        (recur (butlast current)
               (conj result (format-id current)))))))

(defn common-ancestor
  "Find the deepest common ancestor of two IDs, or nil if none.

   Examples:
     (common-ancestor \"1.2.3\" \"1.2.4\") => \"1.2\"
     (common-ancestor \"1.2\" \"1.3\")     => \"1\"
     (common-ancestor \"1\" \"2\")         => nil"
  [id1 id2]
  (when-let [parts1 (parse-id id1)]
    (when-let [parts2 (parse-id id2)]
      (let [common (take-while (fn [[a b]] (= a b))
                               (map vector parts1 parts2))
            common-parts (map first common)]
        (when (seq common-parts)
          (format-id (vec common-parts)))))))
