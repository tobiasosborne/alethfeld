(ns alethfeld.mote.core
  "Mote constructors."
  (:require [alethfeld.mote.util :as util]))

(defn make-mote
  "Create a mote with explicit values. Low-level constructor.

   Required:
   - id: Mote ID (string)
   - claim: The mathematical statement (string)
   - created-by: Agent name (string)

   Options:
   - :status - Defaults to :fixed
   - :taint - Defaults to #{:needs-verification}
   - :priority - Defaults to :p2
   - :difficulty - Defaults to 3
   - :parent - Parent mote ID (nil for roots)
   - :children - Vector of child IDs, defaults to []
   - :proposal - Active proposal, defaults to nil
   - :assumptions - Vector of assumptions, defaults to []
   - :definitions - Vector of definitions, defaults to []
   - :depends-on - Vector of dependencies, defaults to nil
   - :votes - Vector of votes, defaults to []
   - :claimed-by - Agent name, defaults to nil
   - :claimed-at - Timestamp, defaults to nil
   - :created-at - Timestamp, defaults to now
   - :updated-at - Timestamp, defaults to now
   - :contributors - Contributors tracking map (auto-initialized)
   - :meta - Additional metadata map"
  [id claim created-by & {:keys [status taint priority difficulty
                                  parent children proposal
                                  assumptions definitions depends-on votes
                                  claimed-by claimed-at
                                  created-at updated-at contributors meta]}]
  (let [ts (or created-at (util/now))
        default-contributors {:created-by created-by}]
    (cond-> {:id id
             :claim claim
             :status (or status :fixed)
             :taint (or taint #{:needs-verification})
             :priority (or priority :p2)
             :difficulty (or difficulty 3)
             :children (or children [])
             :assumptions (or assumptions [])
             :definitions (or definitions [])
             :votes (or votes [])
             :created-by created-by
             :created-at ts
             :updated-at (or updated-at ts)
             :contributors (or contributors default-contributors)}
      parent (assoc :parent parent)
      proposal (assoc :proposal proposal)
      depends-on (assoc :depends-on depends-on)
      claimed-by (assoc :claimed-by claimed-by)
      claimed-at (assoc :claimed-at claimed-at)
      meta (assoc :meta meta))))

(defn make-root-mote
  "Create a root mote (no parent).

   Arguments:
   - id: Mote ID (typically a single number like \"1\", \"2\")
   - claim: The mathematical statement
   - created-by: Agent name

   Options:
   - :priority - Defaults to :p2
   - :difficulty - Defaults to 3
   - Other options passed through to make-mote"
  [id claim created-by & {:keys [priority difficulty] :as opts}]
  (apply make-mote id claim created-by
         (mapcat identity (dissoc opts :parent))))

(defn make-child-mote
  "Create a child mote, inheriting priority/difficulty from parent.

   Arguments:
   - id: Mote ID (e.g., \"1.2.3\")
   - claim: The mathematical statement
   - created-by: Agent name
   - parent-mote: The parent mote map (to inherit from)

   Options:
   - :priority - Defaults to parent's priority
   - :difficulty - Defaults to parent's difficulty
   - Other options passed through to make-mote"
  [id claim created-by parent-mote & {:keys [priority difficulty] :as opts}]
  (apply make-mote id claim created-by
         :parent (:id parent-mote)
         :priority (or priority (:priority parent-mote) :p2)
         :difficulty (or difficulty (:difficulty parent-mote) 3)
         (mapcat identity (dissoc opts :parent :priority :difficulty))))
