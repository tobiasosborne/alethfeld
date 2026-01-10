(ns alethfeld.mote.util
  "Utility functions for mote operations: ID generation, time handling, and claim expiration."
  (:import [java.time LocalDateTime Instant Duration]
           [java.time.format DateTimeFormatter]
           [java.util Date]))

;; =============================================================================
;; ID Generation
;; =============================================================================

;; Timestamp format for ID generation: YYYYMMDD-HHmmssSSS
(def ^:private id-timestamp-format "yyyyMMdd-HHmmssSSS")

;; Max value for random suffix (0x10000 = 65536) to produce 4 hex digits (0000-ffff)
(def ^:private random-suffix-max 0x10000)

(defn generate-id
  "Generate a unique ID suffix for proposals/jobs."
  []
  (let [ts (LocalDateTime/now)
        fmt (DateTimeFormatter/ofPattern id-timestamp-format)
        random-suffix (format "%04x" (rand-int random-suffix-max))]
    (str (.format ts fmt) "-" random-suffix)))

;; =============================================================================
;; Timestamp Helpers
;; =============================================================================

(def ^:dynamic *clock*
  "Clock function for getting current time. Rebindable for testing."
  #(Date.))

(defn now
  "Returns current time. Uses *clock* which can be rebound in tests."
  []
  (*clock*))

;; =============================================================================
;; Claim Expiration
;; =============================================================================

(defn claim-expired?
  "Check if a mote's claim has expired.

   Arguments:
   - mote: The mote to check
   - timeout-minutes: Number of minutes after which a claim expires

   Options:
   - now: Optional java.time.Instant for the current time (defaults to Instant/now).
          Useful for testing and ensuring consistent time comparisons.

   Returns true if:
   - The mote has a claimed-at timestamp
   - The claim is older than timeout-minutes

   Returns false if:
   - The mote is not claimed
   - The claim has no timestamp
   - The claim is within the timeout window"
  [mote timeout-minutes & {:keys [now]}]
  (if-let [claimed-at (:claimed-at mote)]
    (let [current-instant (or now (Instant/now))
          claimed-instant (Instant/ofEpochMilli (.getTime claimed-at))
          timeout (Duration/ofMinutes timeout-minutes)
          expiration-instant (.plus claimed-instant timeout)]
      (.isAfter current-instant expiration-instant))
    false))
