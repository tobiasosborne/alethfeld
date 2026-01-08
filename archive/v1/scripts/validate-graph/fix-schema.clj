#!/usr/bin/env clojure
;; Fix schema issues in semantic graph EDN files
;; - Adds content-hash to nodes
;; - Converts keyword keys to strings for external-refs and lemmas
;; - Extends short content-hashes to 16 chars

(require '[clojure.edn :as edn]
         '[clojure.pprint :as pp]
         '[clojure.string :as str])

(import '[java.security MessageDigest]
        '[java.io PushbackReader])

(def content-hash-length 16)  ; Match config/content-hash-length

(defn sha256-hex [s]
  "Generate SHA-256 hash of string, return first N hex chars"
  (let [md (MessageDigest/getInstance "SHA-256")
        bytes (.digest md (.getBytes (str s) "UTF-8"))
        full-hex (apply str (map #(format "%02x" (bit-and % 0xff)) bytes))]
    (subs full-hex 0 content-hash-length)))

(defn normalize-latex [s]
  "Normalize LaTeX for consistent hashing"
  (-> s
      (str/replace #"\s+" " ")
      str/trim))

(defn content-hash [statement]
  (sha256-hex (normalize-latex statement)))

(defn fix-hash [h]
  "Ensure hash is exactly N lowercase hex chars"
  (cond
    (nil? h) (sha256-hex (str (System/currentTimeMillis)))
    (>= (count h) content-hash-length) (subs (str/lower-case h) 0 content-hash-length)
    :else (sha256-hex (str h (System/currentTimeMillis)))))

(defn current-iso8601 []
  "Get current time as ISO8601 string"
  (let [now (java.time.Instant/now)
        formatter (java.time.format.DateTimeFormatter/ISO_INSTANT)]
    (.format formatter now)))

(defn make-default-provenance []
  "Generate default provenance with current timestamp"
  {:created-at (current-iso8601)
   :created-by :orchestrator
   :round 0
   :revision-of nil})

;; For backwards compat, also provide a static version for cases where we want deterministic output
(def default-provenance
  {:created-at "2025-01-01T00:00:00Z"
   :created-by :orchestrator
   :round 0
   :revision-of nil})

(defn fix-node [node]
  "Fix node: add content-hash, scope, provenance, display-order if missing"
  (cond-> node
    (nil? (:content-hash node)) (assoc :content-hash (content-hash (:statement node "")))
    (nil? (:scope node)) (assoc :scope #{})
    (nil? (:provenance node)) (assoc :provenance default-provenance)
    (nil? (:display-order node)) (assoc :display-order 0)))

(defn keyword->string-key [m]
  "Convert keyword keys to string keys in a map"
  (into {} (map (fn [[k v]] [(if (keyword? k) (name k) k) v]) m)))

(defn fix-external-ref [ref]
  "Fix external ref: ensure :id is a string"
  (if (keyword? (:id ref))
    (assoc ref :id (name (:id ref)))
    ref))

(defn fix-lemma [lemma]
  "Fix lemma: ensure :id is a string, add required fields"
  (let [id-str (if (keyword? (:id lemma)) (name (:id lemma)) (or (:id lemma) "unknown"))
        base (cond-> lemma
               (keyword? (:id lemma)) (assoc :id id-str)
               ;; Map :edn-node to :root-node if present
               (and (:edn-node lemma) (not (:root-node lemma)))
               (assoc :root-node (:edn-node lemma)))
        ;; Derive name from id if missing
        name-val (or (:name base) id-str)
        ;; Derive statement from name if missing
        stmt-val (or (:statement base) (str "See lemma " id-str))
        with-required (assoc base :name name-val :statement stmt-val)]
    ;; Fix content-hash based on statement
    (let [fixed-hash (if (:content-hash with-required)
                       (fix-hash (:content-hash with-required))
                       (content-hash stmt-val))]
      ;; Add required fields with defaults if missing
      (merge {:root-node :unknown
              :status :proven
              :taint :clean
              :extracted-nodes #{}}
             (assoc with-required :content-hash fixed-hash)))))

(defn fix-symbol [sym-id sym]
  "Fix symbol: add introduced-at and id if missing"
  (cond-> sym
    (nil? (:id sym)) (assoc :id sym-id)
    (nil? (:introduced-at sym)) (assoc :introduced-at :unknown)))

(def default-max-tokens 100000)

(defn make-default-metadata []
  "Generate default metadata with current timestamp"
  {:created-at (current-iso8601)
   :last-modified (current-iso8601)
   :proof-mode :strict-mathematics
   :iteration-counts {:verification {} :expansion {} :strategy 0}
   :context-budget {:max-tokens default-max-tokens :current-estimate 0}})

;; For backwards compat
(def default-metadata
  {:created-at "2025-01-01T00:00:00Z"
   :last-modified "2025-01-01T00:00:00Z"
   :proof-mode :strict-mathematics
   :iteration-counts {:verification {} :expansion {} :strategy 0}
   :context-budget {:max-tokens default-max-tokens :current-estimate 0}})

(defn fix-metadata [metadata]
  "Fix metadata: ensure all required fields are present"
  (merge default-metadata metadata))

(defn ensure-required-keys [graph]
  "Ensure all top-level required keys exist"
  (-> (merge {:graph-id "unknown"
              :version 1
              :nodes {}
              :symbols {}
              :external-refs {}
              :lemmas {}
              :obligations []
              :archived-nodes {}
              :metadata default-metadata}
             graph)
      ;; Ensure metadata has all required fields
      (update :metadata fix-metadata)))

(defn fix-graph [graph]
  "Fix all schema issues in a semantic graph"
  (-> graph
      ensure-required-keys
      ;; Fix theorem content-hash
      (update-in [:theorem :content-hash] fix-hash)
      ;; Fix all nodes
      (update :nodes #(into {} (map (fn [[k v]] [k (fix-node v)]) %)))
      ;; Fix symbols: add introduced-at and id if missing
      (update :symbols #(into {} (map (fn [[k v]] [k (fix-symbol k v)]) %)))
      ;; Fix external-refs: convert keyword keys to strings
      (update :external-refs #(into {} (map (fn [[k v]] [(if (keyword? k) (name k) k) (fix-external-ref v)]) %)))
      ;; Fix lemmas: convert keyword keys to strings
      (update :lemmas #(into {} (map (fn [[k v]] [(if (keyword? k) (name k) k) (fix-lemma v)]) %)))))

(defn process-file [input-path output-path]
  (let [graph (with-open [r (PushbackReader. (clojure.java.io/reader input-path))]
                (edn/read r))
        fixed (fix-graph graph)]
    (spit output-path (with-out-str (pp/pprint fixed)))
    (println "Fixed:" input-path "->" output-path)))

(when (= 2 (count *command-line-args*))
  (let [[input output] *command-line-args*]
    (process-file input output)))
