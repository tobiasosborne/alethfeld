(ns alethfeld.session.role
  "Role-action matrix and permission checking for sessions.")

;; -----------------------------------------------------------------------------
;; Role-Action Matrix
;; -----------------------------------------------------------------------------

(def role-actions
  "Defines which actions each role is permitted to perform.

   Each role has a specific set of capabilities:
   - :proposer - Creates proposals and adds definitions/assumptions/refs
   - :advisor - Reviews proposals (approve/reject)
   - :prover - Similar to proposer but can also remove taints
   - :verifier - Votes on motes and can add/remove taints (workflow control)
   - :ref-checker - Manages references and can remove taints
   - :counterexample - Votes and can update status (refutation)"
  {:proposer      #{:propose :add-definition :add-assumption :add-ref :done}
   :advisor       #{:approve :reject :done}
   :prover        #{:propose :add-definition :add-assumption :add-ref
                    :taint-remove :done}
   :verifier      #{:vote :taint-add :taint-remove :done}
   :ref-checker   #{:add-ref :taint-remove :done}
   :counterexample #{:vote :update-status :done}})

(def sessionless-commands
  "Commands that don't require an active session.

   These are read-only or administrative operations that any agent
   can perform without claiming a mote."
  #{:init :ready :show :tree :status :check :log :help :config})

(defn allowed?
  "Check if a role is permitted to perform an action.

   Arguments:
   - role: The session role (keyword)
   - action: The action to check (keyword)

   Returns true if the role can perform the action, false otherwise."
  [role action]
  (contains? (get role-actions role) action))

(defn requires-session?
  "Check if a command requires an active session.

   Arguments:
   - command: The command keyword (e.g., :propose, :show)

   Returns true if the command requires a session, false otherwise."
  [command]
  (not (contains? sessionless-commands command)))

(defn get-allowed-actions
  "Get the set of actions allowed for a role.

   Arguments:
   - role: The session role (keyword)

   Returns a set of allowed action keywords, or nil if role is invalid."
  [role]
  (get role-actions role))

(defn get-roles-for-action
  "Get all roles that can perform a given action.

   Arguments:
   - action: The action keyword

   Returns a set of roles that can perform the action."
  [action]
  (->> role-actions
       (filter (fn [[_role actions]] (contains? actions action)))
       (map first)
       set))
