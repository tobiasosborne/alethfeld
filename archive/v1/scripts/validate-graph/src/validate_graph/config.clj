(ns validate-graph.config
  "Configuration constants for semantic proof graph validation.")

;; =============================================================================
;; Schema Constants
;; =============================================================================

(def content-hash-length
  "Length of content hash hex strings (SHA256 prefix)."
  16)

(def content-hash-pattern
  "Regex pattern for valid content hashes."
  (re-pattern (str "^[a-f0-9]{" content-hash-length "}$")))

;; =============================================================================
;; Default Values for fix-schema
;; =============================================================================

(def default-max-tokens
  "Default maximum context tokens for proof budget."
  100000)

(def default-proof-mode
  "Default proof mode for new graphs."
  :strict-mathematics)

(defn current-iso8601
  "Get current time as ISO8601 string with timezone."
  []
  (let [now (java.time.Instant/now)
        formatter (java.time.format.DateTimeFormatter/ISO_INSTANT)]
    (.format formatter now)))

(defn default-provenance
  "Generate default provenance with current timestamp.
   Optionally override created-by (default :orchestrator)."
  ([] (default-provenance :orchestrator))
  ([created-by]
   {:created-at (current-iso8601)
    :created-by created-by
    :round 0
    :revision-of nil}))

(defn default-metadata
  "Generate default metadata with current timestamp."
  []
  {:created-at (current-iso8601)
   :last-modified (current-iso8601)
   :proof-mode default-proof-mode
   :iteration-counts {:verification {} :expansion {} :strategy 0}
   :context-budget {:max-tokens default-max-tokens :current-estimate 0}})
