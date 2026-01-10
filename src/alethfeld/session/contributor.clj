(ns alethfeld.session.contributor
  "Contributor tracking and self-vote prevention.")

;; -----------------------------------------------------------------------------
;; Contributors & Self-Vote Prevention
;; -----------------------------------------------------------------------------

(defn can-vote?
  "Check if an agent can vote on a mote.

   An agent cannot vote if they contributed to the mote's creation or refinement.
   This prevents self-voting and ensures independent verification.

   Arguments:
   - mote: The mote map
   - agent: The agent identifier string

   Returns true if the agent can vote, false if they are a contributor."
  [mote agent]
  (let [{:keys [created-by proposed-by refined-by refs-checked-by]}
        (:contributors mote)]
    (and (not= agent created-by)
         (not= agent proposed-by)
         (not (contains? (or refined-by #{}) agent))
         (not (contains? (or refs-checked-by #{}) agent)))))

(defn add-contributor
  "Add an agent as a contributor in a specific role.

   Arguments:
   - mote: The mote map
   - agent: The agent identifier string
   - role: The contribution type (:proposed-by, :refined-by, :refs-checked-by)

   Returns the updated mote."
  [mote agent role]
  (let [contributors (or (:contributors mote) {:created-by (:created-by mote)})]
    (assoc mote :contributors
           (case role
             :proposed-by (assoc contributors :proposed-by agent)
             :refined-by (update contributors :refined-by
                                 (fnil conj #{}) agent)
             :refs-checked-by (update contributors :refs-checked-by
                                       (fnil conj #{}) agent)
             contributors))))

(defn get-contributors
  "Get set of all contributors to a mote.

   Arguments:
   - mote: The mote map

   Returns a set of agent identifiers who contributed."
  [mote]
  (let [{:keys [created-by proposed-by refined-by refs-checked-by]}
        (:contributors mote)]
    (cond-> #{created-by}
      proposed-by (conj proposed-by)
      refined-by (into refined-by)
      refs-checked-by (into refs-checked-by))))
