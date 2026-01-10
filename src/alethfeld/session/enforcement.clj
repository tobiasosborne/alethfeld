(ns alethfeld.session.enforcement
  "Session validation and enforcement for commands."
  (:require [alethfeld.session.core :as core]
            [alethfeld.session.role :as role]))

;; -----------------------------------------------------------------------------
;; Session Enforcement
;; -----------------------------------------------------------------------------

(defn enforce-session!
  "Enforce session validity for an action on a mote.

   Arguments:
   - repo-path: Path to the repository root
   - session-id: The session token
   - action: The action being performed (keyword)
   - mote-id: The mote being acted upon

   Validates:
   1. Session exists and is active
   2. Session is not expired
   3. Session is locked to the correct mote
   4. Role is permitted to perform the action

   On success, records the action in the session audit trail.
   Returns the session map.

   Throws ExceptionInfo on any validation failure."
  [repo-path session-id action mote-id]
  (let [session (core/load-active-session repo-path session-id)]
    (cond
      ;; Session doesn't exist or not active
      (nil? session)
      (throw (ex-info "Invalid session"
                      {:type :invalid-session
                       :session-id session-id}))

      ;; Session has expired
      (core/session-expired? session)
      (throw (ex-info "Session expired"
                      {:type :session-expired
                       :session-id session-id
                       :expires-at (:expires-at session)}))

      ;; Session is locked to a different mote
      (not= mote-id (:mote-id session))
      (throw (ex-info "Session locked to different mote"
                      {:type :session-mote-mismatch
                       :session-id session-id
                       :session-mote-id (:mote-id session)
                       :requested-mote-id mote-id}))

      ;; Role is not allowed to perform this action
      (not (role/allowed? (:role session) action))
      (throw (ex-info "Action not allowed for role"
                      {:type :action-not-allowed
                       :session-id session-id
                       :role (:role session)
                       :action action
                       :allowed-actions (role/get-allowed-actions (:role session))}))

      ;; All validations passed - record action and return session
      :else
      (do
        (core/record-action! repo-path session-id action)
        session))))

(defn validate-session!
  "Validate a session exists and is for the correct mote (no action check).

   This is a lighter-weight validation that just ensures:
   1. Session exists and is active
   2. Session is not expired
   3. Session is locked to the correct mote

   Unlike enforce-session!, this does NOT check role permissions.
   Use for operations that any session holder can perform.

   Returns the session map.
   Throws ExceptionInfo on validation failure."
  [repo-path session-id mote-id]
  (let [session (core/load-active-session repo-path session-id)]
    (cond
      (nil? session)
      (throw (ex-info "Invalid session"
                      {:type :invalid-session
                       :session-id session-id}))

      (core/session-expired? session)
      (throw (ex-info "Session expired"
                      {:type :session-expired
                       :session-id session-id
                       :expires-at (:expires-at session)}))

      (not= mote-id (:mote-id session))
      (throw (ex-info "Session locked to different mote"
                      {:type :session-mote-mismatch
                       :session-id session-id
                       :session-mote-id (:mote-id session)
                       :requested-mote-id mote-id}))

      :else
      session)))
