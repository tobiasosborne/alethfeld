(ns alethfeld.config
  "Configuration constants for semantic proof graph operations.")

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
;; Default Values
;; =============================================================================

(def default-max-tokens
  "Default maximum context tokens for proof budget."
  100000)

(def default-proof-mode
  "Default proof mode for new graphs."
  :strict-mathematics)

(def tokens-per-char
  "Estimated tokens per character for context budget calculation."
  0.25)

;; =============================================================================
;; Timestamp Functions
;; =============================================================================

(defn current-iso8601
  "Get current time as ISO8601 string."
  []
  (let [now (java.time.Instant/now)
        formatter (java.time.format.DateTimeFormatter/ISO_INSTANT)]
    (.format formatter now)))

;; =============================================================================
;; ID Generation
;; =============================================================================

(defn generate-uuid-prefix
  "Generate a 6-character hex string from UUID."
  []
  (subs (str (java.util.UUID/randomUUID)) 0 6))

(defn generate-node-id
  "Generate a new node ID with format :<depth>-<6-hex>."
  [depth]
  (keyword (str depth "-" (generate-uuid-prefix))))

;; =============================================================================
;; Content Hash
;; =============================================================================

(defn compute-content-hash
  "Compute SHA256 content hash (prefix) for a string."
  [content]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")
        bytes (.digest md (.getBytes (str content) "UTF-8"))]
    (subs (apply str (map #(format "%02x" (bit-and % 0xff)) bytes))
          0 content-hash-length)))

;; =============================================================================
;; Default Structures
;; =============================================================================

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
