(ns alethfeld.convert
  "Convert legacy proof format to v4 semantic graph schema."
  (:require [alethfeld.config :as config]
            [clojure.string :as str]))

;; =============================================================================
;; ID Generation
;; =============================================================================

(defn- normalize-id
  "Convert legacy IDs like :<1>1 to valid keywords like :1-001."
  [id]
  (if (keyword? id)
    (let [s (name id)]
      (if (re-matches #"<\d+>\d+" s)
        ;; Convert <1>1 to 1-001 format
        (let [[_ depth num] (re-matches #"<(\d+)>(\d+)" s)]
          (keyword (str depth "-" (format "%03d" (Integer/parseInt num)))))
        id))
    (keyword (str id))))

(defn- step-depth
  "Extract depth from step ID like :<1>1 -> 1."
  [id]
  (if-let [[_ depth] (re-matches #"<(\d+)>(\d+)" (name id))]
    (Integer/parseInt depth)
    1))

;; =============================================================================
;; Node Conversion
;; =============================================================================

(defn- make-provenance []
  {:created-at (config/current-iso8601)
   :created-by :orchestrator
   :round 0
   :revision-of nil})

(defn- convert-assumption
  "Convert legacy assumption to v4 node."
  [assumption order]
  (let [id (normalize-id (:id assumption))
        statement (:statement assumption)]
    {:id id
     :type :assumption
     :statement statement
     :content-hash (config/compute-content-hash statement)
     :dependencies #{}
     :scope #{}
     :justification :assumption
     :status :verified
     :taint :clean
     :depth 0
     :parent nil
     :display-order order
     :assumption-label (:id assumption)
     :provenance (make-provenance)}))

(defn- convert-definition
  "Convert legacy definition to v4 node."
  [definition order]
  (let [id (normalize-id (:id definition))
        statement (str (:name definition) ": " (:statement definition))]
    {:id id
     :type :definition
     :statement statement
     :content-hash (config/compute-content-hash statement)
     :dependencies #{}
     :scope #{}
     :justification :definition-expansion
     :status :verified
     :taint :clean
     :depth 0
     :parent nil
     :display-order order
     :provenance (make-provenance)}))

(def ^:private valid-justifications
  #{:assumption :local-assumption :discharge :definition-expansion :substitution
    :modus-ponens :universal-elim :universal-intro :existential-intro :existential-elim
    :equality-rewrite :algebraic-rewrite :case-split :induction-base :induction-step
    :contradiction :conjunction-intro :conjunction-elim :disjunction-intro
    :disjunction-elim :implication-intro :lemma-application :external-application
    :admitted :qed})

(defn- normalize-justification
  "Map legacy justifications to valid v4 justifications."
  [j]
  (if (contains? valid-justifications j)
    j
    ;; Map common legacy justifications
    (case j
      :equivalence-elim :modus-ponens
      :monotonicity :algebraic-rewrite
      :by-definition :definition-expansion
      :by-assumption :assumption
      :rewrite :algebraic-rewrite
      :apply :modus-ponens
      ;; Default
      :modus-ponens)))

(defn- convert-step
  "Convert legacy step to v4 node."
  [step order parent-id all-ids]
  (let [id (normalize-id (:id step))
        statement (or (:claim step) (:statement step) "")
        depth (step-depth (:id step))
        ;; Normalize dependencies
        deps (->> (or (:using step) [])
                  (map normalize-id)
                  (filter #(contains? all-ids %))
                  set)
        status (case (:status step)
                 :verified :verified
                 :admitted :admitted
                 :rejected :rejected
                 :proposed)
        justification (normalize-justification (or (:justification step) :modus-ponens))]
    {:id id
     :type :claim
     :statement statement
     :content-hash (config/compute-content-hash statement)
     :dependencies deps
     :scope #{}
     :justification justification
     :status status
     :taint (if (= :admitted status) :self-admitted :clean)
     :depth depth
     :parent parent-id
     :display-order order
     :provenance (make-provenance)}))

(defn- flatten-steps
  "Flatten nested steps structure into a flat list with parent references."
  [steps parent-id order-start all-ids]
  (loop [remaining steps
         result []
         order order-start]
    (if (empty? remaining)
      result
      (let [step (first remaining)
            id (normalize-id (:id step))
            node (convert-step step order parent-id all-ids)
            ;; Recursively flatten substeps
            substeps (:substeps step)
            sub-results (when (seq substeps)
                          (flatten-steps substeps id (inc order) all-ids))
            new-order (if sub-results
                        (+ order 1 (count sub-results))
                        (inc order))]
        (recur (rest remaining)
               (concat result [node] sub-results)
               new-order)))))

;; =============================================================================
;; Symbol Conversion
;; =============================================================================

(defn- convert-symbol
  "Convert legacy symbol to v4 format."
  [sym idx]
  (let [sym-name (or (:symbol sym) (str "sym" idx))
        id (keyword (str/replace sym-name #"[^a-zA-Z0-9_-]" "_"))]
    [id {:id id
         :name sym-name
         :type (str (or (:type sym) "unknown"))
         :tex (str (or (:tex sym) sym-name))
         :constraints (str (or (:description sym) ""))
         :scope :global
         :introduced-at :theorem}]))

;; =============================================================================
;; Main Conversion
;; =============================================================================

(defn- collect-all-ids
  "Collect all IDs that will exist in the converted graph."
  [old-graph]
  (let [assumption-ids (set (map #(normalize-id (:id %)) (:assumptions old-graph)))
        definition-ids (set (map #(normalize-id (:id %)) (:definitions old-graph)))
        ;; Recursively collect step IDs
        step-ids (atom #{})
        collect-step-ids (fn collect [steps]
                           (doseq [step steps]
                             (swap! step-ids conj (normalize-id (:id step)))
                             (when (:substeps step)
                               (collect (:substeps step)))))]
    (collect-step-ids (:steps old-graph))
    (clojure.set/union assumption-ids definition-ids @step-ids)))

(defn- normalize-assumptions
  "Normalize assumptions to a vector format."
  [assumptions]
  (cond
    (nil? assumptions) []
    (vector? assumptions) assumptions
    (map? assumptions) (vec (vals assumptions))
    :else []))

(defn- normalize-symbols
  "Normalize symbols to a vector format."
  [symbols]
  (cond
    (nil? symbols) []
    (vector? symbols) symbols
    (map? symbols) (mapv (fn [[k v]] (merge {:symbol (name k)} v)) symbols)
    :else []))

(defn convert-legacy-to-v4
  "Convert a legacy proof format to v4 semantic graph.

   Input: Legacy format with :meta, :theorem (string or map), :assumptions, :definitions, :steps
   Output: v4 SemanticGraph format"
  [old-graph & {:keys [graph-id] :or {graph-id nil}}]
  (let [all-ids (collect-all-ids old-graph)

        ;; Convert theorem - handle both string and map formats
        raw-theorem (:theorem old-graph)
        theorem-statement (cond
                           (string? raw-theorem) raw-theorem
                           (map? raw-theorem) (or (:statement raw-theorem) "Theorem statement")
                           :else "Theorem statement")
        theorem {:id :theorem
                 :statement theorem-statement
                 :content-hash (config/compute-content-hash theorem-statement)}

        ;; Convert assumptions - handle both vector and map formats
        assumptions (normalize-assumptions (:assumptions old-graph))
        assumption-nodes (map-indexed (fn [i a] (convert-assumption a i)) assumptions)

        ;; Convert definitions
        definitions (or (:definitions old-graph) [])
        def-start (count assumptions)
        definition-nodes (map-indexed (fn [i d] (convert-definition d (+ def-start i))) definitions)

        ;; Convert steps (flattened)
        steps (or (:steps old-graph) [])
        step-start (+ def-start (count definitions))
        step-nodes (flatten-steps steps nil step-start all-ids)

        ;; Build nodes map
        all-nodes (concat assumption-nodes definition-nodes step-nodes)
        nodes-map (into {} (map (juxt :id identity) all-nodes))

        ;; Convert symbols - handle both vector and map formats
        symbols (normalize-symbols (:symbols old-graph))
        symbols-map (into {} (map-indexed convert-symbol symbols))

        ;; Build metadata - normalize date format
        old-meta (or (:meta old-graph) {})
        raw-date (or (:generated-at old-meta) (config/current-iso8601))
        ;; Convert date-only format to ISO8601
        created-at (if (re-matches #"\d{4}-\d{2}-\d{2}" raw-date)
                     (str raw-date "T00:00:00")
                     raw-date)
        metadata {:created-at created-at
                  :last-modified (config/current-iso8601)
                  :proof-mode (or (:proof-mode old-graph) :strict-mathematics)
                  :iteration-counts {:verification {}
                                     :expansion {}
                                     :strategy (get-in old-meta [:iterations :total] 0)}
                  :context-budget {:max-tokens 100000
                                   :current-estimate 0}}]

    {:graph-id (or graph-id (str "converted-" (config/generate-uuid-prefix)))
     :version 1
     :theorem theorem
     :nodes nodes-map
     :symbols symbols-map
     :external-refs {}
     :lemmas {}
     :obligations (vec (or (:obligations old-meta) []))
     :archived-nodes {}
     :metadata metadata}))

;; =============================================================================
;; Lemma Format Conversion
;; =============================================================================

(defn- convert-lemma-node
  "Convert a node from lemma format to v4 format."
  [node order]
  (let [id (:id node)
        statement (:statement node)]
    (merge node
           {:scope (or (:scope node) #{})
            :display-order order
            :content-hash (or (:content-hash node)
                              (config/compute-content-hash statement))
            :provenance (or (:provenance node) (make-provenance))})))

(defn- convert-external-dependency
  "Convert external dependency to v4 external-ref format."
  [[id dep] order]
  (let [statement (:statement dep)
        id-str (name id)]
    ;; Return [string-key ref-map] for map-of :string ExternalRef
    [id-str {:id id-str
             :claimed-statement statement
             :verification-status :verified
             :verified-statement statement}]))

(defn convert-lemma-to-v4
  "Convert a lemma format file to v4 semantic graph.

   Input: Lemma format with :lemma-id, :name, :statement, :nodes, :external-dependencies
   Output: v4 SemanticGraph format"
  [lemma & {:keys [graph-id] :or {graph-id nil}}]
  (let [;; Convert lemma statement to theorem (always compute fresh hash)
        theorem-statement (:statement lemma)
        theorem {:id :theorem
                 :statement theorem-statement
                 :content-hash (config/compute-content-hash theorem-statement)}

        ;; Convert nodes with added v4 fields
        old-nodes (:nodes lemma)
        nodes-map (->> old-nodes
                       (map-indexed (fn [i [id node]] [id (convert-lemma-node node i)]))
                       (into {}))

        ;; Convert external dependencies to external-refs (definitions become nodes)
        ext-deps (:external-dependencies lemma)
        external-refs (->> ext-deps
                           (filter (fn [[_ dep]] (not= :definition (:type dep))))
                           (map-indexed (fn [i [id dep]] (convert-external-dependency [id dep] i)))
                           (into {}))

        ;; Convert definitions from external-dependencies to nodes
        def-nodes (->> ext-deps
                       (filter (fn [[_ dep]] (= :definition (:type dep))))
                       (map-indexed (fn [i [id dep]]
                                      [id {:id id
                                           :type :definition
                                           :statement (:statement dep)
                                           :content-hash (config/compute-content-hash (:statement dep))
                                           :dependencies #{}
                                           :scope #{}
                                           :justification :definition-expansion
                                           :status :verified
                                           :taint :clean
                                           :depth 0
                                           :parent nil
                                           :display-order (+ (count old-nodes) i)
                                           :provenance (make-provenance)}]))
                       (into {}))

        ;; Merge definition nodes into nodes-map
        all-nodes (merge nodes-map def-nodes)

        ;; Convert symbols
        old-symbols (:symbols lemma)
        symbols-map (if (map? old-symbols)
                      (->> old-symbols
                           (map (fn [[id sym]]
                                  [id {:id id
                                       :name (or (:name sym) (name id))
                                       :type (or (:type sym) "unknown")
                                       :tex (or (:tex sym) (name id))
                                       :constraints ""
                                       :scope :global
                                       :introduced-at :theorem}]))
                           (into {}))
                      {})

        ;; Build metadata
        metadata {:created-at (config/current-iso8601)
                  :last-modified (config/current-iso8601)
                  :proof-mode :strict-mathematics
                  :iteration-counts {:verification {}
                                     :expansion {}
                                     :strategy 0}
                  :context-budget {:max-tokens 100000
                                   :current-estimate 0}}]

    {:graph-id (or graph-id (str "lemma-" (:lemma-id lemma) "-" (config/generate-uuid-prefix)))
     :version (or (:version lemma) 1)
     :theorem theorem
     :nodes all-nodes
     :symbols symbols-map
     :external-refs external-refs
     :lemmas {}
     :obligations []
     :archived-nodes {}
     :metadata metadata}))

(defn- is-lemma-format?
  "Check if the EDN file is in lemma format."
  [data]
  (and (:lemma-id data) (:nodes data)))

;; =============================================================================
;; CLI Support
;; =============================================================================

(defn convert-file
  "Read a legacy EDN file and convert to v4 format.
   Returns {:ok graph} or {:error message}."
  [input-path]
  (try
    (let [content (slurp input-path)
          old-graph (clojure.edn/read-string content)
          ;; Detect if already v4 format
          is-v4? (and (:graph-id old-graph) (:nodes old-graph) (:theorem old-graph))
          is-lemma? (is-lemma-format? old-graph)]
      (cond
        is-v4?
        {:ok old-graph :already-v4 true}

        is-lemma?
        {:ok (convert-lemma-to-v4 old-graph)}

        :else
        {:ok (convert-legacy-to-v4 old-graph)}))
    (catch Exception e
      {:error (str "Failed to convert: " (.getMessage e))})))
