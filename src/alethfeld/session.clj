(ns alethfeld.session
  "Session management for role-based mote operations.

   Sessions provide:
   - Role enforcement (only allowed actions per role)
   - Claim tracking (one session per mote)
   - Audit trail (actions recorded)
   - Expiration (default 30 minutes)

   Directory structure:
   - .alethfeld/sessions/active/<session-id>.edn
   - .alethfeld/sessions/completed/<session-id>.edn

   This is a facade namespace that re-exports functions from:
   - alethfeld.session.role - Role permissions
   - alethfeld.session.contributor - Contributor tracking
   - alethfeld.session.core - Session CRUD
   - alethfeld.session.enforcement - Session validation
   - alethfeld.session.cleanup - Stale session cleanup
   - alethfeld.session.reservation - Job reservations
   - alethfeld.session.resolution - Session alias resolution"
  (:require [alethfeld.session.role :as role]
            [alethfeld.session.contributor :as contributor]
            [alethfeld.session.core :as core]
            [alethfeld.session.enforcement :as enforcement]
            [alethfeld.session.cleanup :as cleanup]
            [alethfeld.session.reservation :as reservation]
            [alethfeld.session.resolution :as resolution]))

;; -----------------------------------------------------------------------------
;; Re-exports from session.role
;; -----------------------------------------------------------------------------

(def role-actions role/role-actions)
(def sessionless-commands role/sessionless-commands)
(def allowed? role/allowed?)
(def requires-session? role/requires-session?)
(def get-allowed-actions role/get-allowed-actions)
(def get-roles-for-action role/get-roles-for-action)

;; -----------------------------------------------------------------------------
;; Re-exports from session.contributor
;; -----------------------------------------------------------------------------

(def can-vote? contributor/can-vote?)
(def add-contributor contributor/add-contributor)
(def get-contributors contributor/get-contributors)

;; -----------------------------------------------------------------------------
;; Re-exports from session.core
;; -----------------------------------------------------------------------------

(def default-session-duration-minutes core/default-session-duration-minutes)
(def session-id-display-length core/session-id-display-length)
(def generate-session-id core/generate-session-id)
(def valid-session-id? core/valid-session-id?)
(def create-session core/create-session)
(def create-session! core/create-session!)
(def load-session core/load-session)
(def load-active-session core/load-active-session)
(def load-all-active-sessions core/load-all-active-sessions)
(def load-sessions-for-mote core/load-sessions-for-mote)
(def load-sessions-for-agent core/load-sessions-for-agent)
(def session-active? core/session-active?)
(def session-expired? core/session-expired?)
(def record-action! core/record-action!)
(def end-session! core/end-session!)
(def archive-session! core/archive-session!)
(def delete-session! core/delete-session!)
(def ensure-session-dirs! core/ensure-session-dirs!)
(def validate-session core/validate-session)

;; -----------------------------------------------------------------------------
;; Re-exports from session.enforcement
;; -----------------------------------------------------------------------------

(def enforce-session! enforcement/enforce-session!)
(def validate-session! enforcement/validate-session!)

;; -----------------------------------------------------------------------------
;; Re-exports from session.cleanup
;; -----------------------------------------------------------------------------

(def pid-alive? cleanup/pid-alive?)
(def session-stale? cleanup/session-stale?)
(def cleanup-expired-sessions! cleanup/cleanup-expired-sessions!)
(def cleanup-stale-sessions! cleanup/cleanup-stale-sessions!)

;; -----------------------------------------------------------------------------
;; Re-exports from session.reservation
;; -----------------------------------------------------------------------------

(def default-reservation-duration-seconds reservation/default-reservation-duration-seconds)
(def reservation-token-length reservation/reservation-token-length)
(def reservation-expired? reservation/reservation-expired?)
(def create-reservation-atomic! reservation/create-reservation-atomic!)
(def create-reservation! reservation/create-reservation!)
(def load-reservation reservation/load-reservation)
(def delete-reservation! reservation/delete-reservation!)
(def claim-reservation! reservation/claim-reservation!)
(def cleanup-expired-reservations! reservation/cleanup-expired-reservations!)
(def list-active-reservations reservation/list-active-reservations)
(def mote-has-reservation? reservation/mote-has-reservation?)

;; -----------------------------------------------------------------------------
;; Re-exports from session.resolution
;; -----------------------------------------------------------------------------

(def resolve-session-alias resolution/resolve-session-alias)
(def resolve-session resolution/resolve-session)
