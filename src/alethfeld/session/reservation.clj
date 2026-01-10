(ns alethfeld.session.reservation
  "Lightweight job reservations for orchestrators."
  (:require [alethfeld.io :as io]
            [alethfeld.path :as path]
            [alethfeld.session.core :as core]
            [clojure.string :as str])
  (:import [java.time Instant]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const default-reservation-duration-seconds 60)

(def ^:const reservation-token-length
  "Length of reservation tokens. Short tokens (6 alphanumeric characters)
   are easy to type while providing sufficient uniqueness for short-lived
   reservations (60-second default lifetime)."
  6)

;; -----------------------------------------------------------------------------
;; Private Helpers
;; -----------------------------------------------------------------------------

(defn- generate-reservation-token
  "Generate a short, memorable reservation token.
   Format: reservation-token-length alphanumeric characters."
  []
  (let [chars "abcdefghijklmnopqrstuvwxyz0123456789"
        rand-char #(nth chars (rand-int (count chars)))]
    (apply str (repeatedly reservation-token-length rand-char))))

(defn- reservation-file-path
  "Get full path to a reservation file."
  [repo-path token]
  (io/full-path repo-path (path/reservation-path token)))

(defn- reservation-lock-path
  "Get full path to a mote reservation lock file.
   Lock files are used for atomic reservation creation."
  [repo-path mote-id]
  (io/full-path repo-path (str (path/reservations-path) "/lock-" mote-id ".edn")))

;; -----------------------------------------------------------------------------
;; Reservation Status
;; -----------------------------------------------------------------------------

(defn reservation-expired?
  "Check if a reservation has expired.

   Arguments:
   - reservation: The reservation map

   Options:
   - :now - Override current time (for testing)"
  [reservation & {:keys [now]}]
  (let [now (or now (Instant/now))
        expires-at (:expires-at reservation)]
    (when expires-at
      (.isAfter now (.toInstant expires-at)))))

;; -----------------------------------------------------------------------------
;; Reservation Creation
;; -----------------------------------------------------------------------------

(defn create-reservation-atomic!
  "Atomically create a reservation for a mote/role combination.

   Uses a per-mote lock file to prevent race conditions when multiple
   agents try to reserve the same mote simultaneously.

   Lock files are stored at: .alethfeld/sessions/reservations/lock-{mote-id}.edn

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote to reserve
   - role: The role for the reservation

   Options:
   - :duration-seconds - Reservation duration (default: 60)

   Returns a map with one of:
   - {:success true :token token :reservation reservation-map}
   - {:success false :held-by existing-reservation-map}"
  [repo-path mote-id role & {:keys [duration-seconds]
                              :or {duration-seconds default-reservation-duration-seconds}}]
  (let [lock-path (reservation-lock-path repo-path mote-id)]
    ;; Ensure reservations directory exists
    (io/ensure-dir (io/full-path repo-path (path/reservations-path)))

    (let [token (generate-reservation-token)
          now (Instant/now)
          expires (.plusSeconds now duration-seconds)
          reservation {:token token
                       :mote-id mote-id
                       :role role
                       :created-at (java.util.Date/from now)
                       :expires-at (java.util.Date/from expires)}]

      ;; Try to create lock file atomically
      (if (io/create-file-exclusive! lock-path reservation)
        ;; Success - lock file created, also write the standard reservation file
        (let [res-path (reservation-file-path repo-path token)]
          (io/write-edn res-path reservation)
          {:success true
           :token token
           :reservation reservation})

        ;; Lock file already exists - check if expired
        ;; TOCTOU FIX: Handle case where file was deleted between our create attempt
        ;; and this read (returns nil). In that case, retry immediately.
        (let [existing (io/read-edn lock-path)]
          (cond
            ;; File was deleted by another process - retry
            (nil? existing)
            (create-reservation-atomic! repo-path mote-id role
                                        :duration-seconds duration-seconds)

            ;; Expired - delete lock and retry
            (reservation-expired? existing :now now)
            (do
              (io/delete-file lock-path)
              (create-reservation-atomic! repo-path mote-id role
                                          :duration-seconds duration-seconds))

            ;; Active reservation held by another agent
            :else
            {:success false
             :held-by existing}))))))

(defn create-reservation!
  "Create a reservation for a mote/role combination.

   Reservations are lightweight pre-claims that:
   - Lock a mote for a specific role
   - Expire quickly (60 seconds by default)
   - Must be explicitly claimed to create a session

   This function uses atomic file creation to prevent race conditions
   when multiple agents try to reserve the same mote simultaneously.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote to reserve
   - role: The role for the reservation

   Options:
   - :duration-seconds - Reservation duration (default: 60)

   Returns the reservation map with :token for claiming.
   Throws ExceptionInfo with :type :reservation-conflict if already reserved."
  [repo-path mote-id role & {:keys [duration-seconds]
                              :or {duration-seconds default-reservation-duration-seconds}}]
  (let [result (create-reservation-atomic! repo-path mote-id role
                                            :duration-seconds duration-seconds)]
    (if (:success result)
      (:reservation result)
      (throw (ex-info "Mote already reserved"
                      {:type :reservation-conflict
                       :mote-id mote-id
                       :role role
                       :held-by (:held-by result)})))))

;; -----------------------------------------------------------------------------
;; Reservation Loading
;; -----------------------------------------------------------------------------

(defn load-reservation
  "Load a reservation by token.

   Returns the reservation map or nil if not found/expired."
  [repo-path token]
  (let [file-path (reservation-file-path repo-path token)]
    (when (io/file-exists? file-path)
      (let [reservation (io/read-edn file-path)]
        (when-not (reservation-expired? reservation)
          reservation)))))

;; -----------------------------------------------------------------------------
;; Reservation Deletion
;; -----------------------------------------------------------------------------

(defn delete-reservation!
  "Delete a reservation (consumed or expired).

   Arguments:
   - repo-path: Path to the repository root
   - token: The reservation token"
  [repo-path token]
  (let [file-path (reservation-file-path repo-path token)]
    (when (io/file-exists? file-path)
      (io/delete-file file-path))))

;; -----------------------------------------------------------------------------
;; Reservation Claiming
;; -----------------------------------------------------------------------------

(defn claim-reservation!
  "Claim a reservation and create a full session.

   Arguments:
   - repo-path: Path to the repository root
   - token: The reservation token
   - agent: Agent identifier string

   Options:
   - :duration-minutes - Session duration (default: 30)

   Returns the created session, or throws if reservation invalid/expired."
  [repo-path token agent & {:keys [duration-minutes] :as opts}]
  (if-let [reservation (load-reservation repo-path token)]
    (let [{:keys [mote-id role]} reservation
          session (apply core/create-session! repo-path mote-id role agent
                         (mapcat identity opts))]
      ;; Delete the reservation after successful claim
      (delete-reservation! repo-path token)
      session)
    (throw (ex-info "Invalid or expired reservation"
                    {:type :invalid-reservation
                     :token token}))))

;; -----------------------------------------------------------------------------
;; Cleanup Operations
;; -----------------------------------------------------------------------------

(defn cleanup-expired-reservations!
  "Remove expired reservation files.

   Arguments:
   - repo-path: Path to the repository root

   Returns count of removed reservations."
  [repo-path]
  (let [res-dir (io/full-path repo-path (path/reservations-path))]
    (if (io/dir-exists? res-dir)
      (let [files (io/list-edn-files res-dir)
            now (Instant/now)]
        (->> files
             (filter (fn [f]
                       (let [reservation (io/read-edn f)]
                         (reservation-expired? reservation :now now))))
             (map (fn [f]
                    (io/delete-file f)
                    1))
             (reduce + 0)))
      0)))

;; -----------------------------------------------------------------------------
;; Reservation Queries
;; -----------------------------------------------------------------------------

(defn list-active-reservations
  "List all active (non-expired) reservations.

   Arguments:
   - repo-path: Path to the repository root

   Returns a vector of reservation maps.
   Note: Excludes lock files (lock-*.edn) which are used for atomic reservation creation."
  [repo-path]
  (let [res-dir (io/full-path repo-path (path/reservations-path))]
    (if (io/dir-exists? res-dir)
      (let [files (io/list-edn-files res-dir)
            ;; Filter out lock files (used for atomic reservation creation)
            reservation-files (remove #(str/includes? % "/lock-") files)
            now (Instant/now)]
        (->> reservation-files
             (map io/read-edn)
             (remove #(reservation-expired? % :now now))
             vec))
      [])))

(defn mote-has-reservation?
  "Check if a mote has an active reservation for a given role.

   Arguments:
   - repo-path: Path to the repository root
   - mote-id: The mote ID to check
   - role: The role to check for (optional - checks any role if nil)

   Returns true if a matching active reservation exists."
  [repo-path mote-id & [role]]
  (let [reservations (list-active-reservations repo-path)]
    (some (fn [res]
            (and (= mote-id (:mote-id res))
                 (or (nil? role) (= role (:role res)))))
          reservations)))
