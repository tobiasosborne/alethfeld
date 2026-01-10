(ns alethfeld.cmd.voting
  "Voting and taint command implementations."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.mote :as mote]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [alethfeld.verify :as verify]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Vote Command
;; -----------------------------------------------------------------------------

(defn cmd-vote!
  "Cast a verification vote on a mote.

   Arguments (in context):
   - :id - The mote ID to vote on (required)

   Options:
   - :session - Session token (required)
   - :for - Vote in favor of verification
   - :against - Vote against verification
   - :reason - Reason for vote (optional)
   - :agent - Agent name (defaults to session agent)
   - :propagate - Auto-vote on parents when all children verified
   - :dry-run - Show what would happen without executing

   Exactly one of --for or --against must be provided.

   When quorum is reached:
   - :verified if unanimous for votes
   - :refuted if unanimous against votes
   - :contested if mixed votes

   When --propagate is used:
   - After voting, checks if all siblings are verified
   - If yes and agent can vote on parent, auto-votes on parent
   - Recursively continues up the tree

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :pending, :verified, :refuted, or :contested
   - :status-changed - Whether the mote status changed
   - :new-status - The new mote status
   - :propagated - Vector of parent IDs that were auto-voted (if --propagate)"
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [for against reason session propagate dry-run]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to vote on"]})))

    (when (and for against)
      (throw (ex-info "Cannot vote both for and against"
                      {:type :validation-failed
                       :errors ["Provide either --for or --against, not both"]})))

    (when (and (not for) (not against))
      (throw (ex-info "Vote direction required"
                      {:type :validation-failed
                       :errors ["Provide --for or --against"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            config (store/load-config repo-path)
            vote-type (if for "FOR" "AGAINST")
            current-votes (:votes mote)
            for-votes (count (filter #(= :for (:type %)) current-votes))
            against-votes (count (filter #(= :against (:type %)) current-votes))
            quorum (:vote-quorum config 1)
            new-for (if for (inc for-votes) for-votes)
            new-against (if against (inc against-votes) against-votes)
            total-votes (+ new-for new-against)
            would-reach-quorum? (>= total-votes quorum)
            predicted-status (when would-reach-quorum?
                               (cond
                                 (and (pos? new-for) (zero? new-against)) :verified
                                 (and (zero? new-for) (pos? new-against)) :refuted
                                 :else :contested))]
        (core/dry-run-result
         :output (str "Would vote " vote-type " on " id
                      "\n\nCurrent votes: " for-votes " for, " against-votes " against (quorum: " quorum ")"
                      "\nAfter vote: " new-for " for, " new-against " against"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached! Status would change to: " (name predicted-status))
                        (str "\n\nQuorum not yet reached. Need " (- quorum total-votes) " more votes.")))
         :would-update [{:id id :change (str "add " vote-type " vote"
                                             (when would-reach-quorum?
                                               (str ", change status to " (name predicted-status))))}]
         :next-actions [(core/done-action (or session "<session>"))
                        (core/show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session :vote id)
            agent (or (:name options) (:agent sess))
            vote-type (if for :for :against)
            result (verify/cast-vote! repo-path id agent vote-type :reason reason)
            vote-result (:result result)
            quorum-status (:quorum-status vote-result)
            ;; Handle propagation if requested and vote was for (not against)
            final-result (if (and propagate for (= :verified quorum-status))
                           (let [propagated (verify/propagate-verification! repo-path id agent :reason reason)]
                             (assoc vote-result :propagated propagated))
                           vote-result)
            ;; Generate intelligent next-actions based on state
            next-acts (core/generate-vote-next-actions repo-path id session agent quorum-status)
            ;; Get quorum info for pending message
            pending-message (when (= :pending quorum-status)
                              (let [status (verify/verification-status repo-path id)]
                                (str "Vote recorded. " (:votes-for status) "/" (:quorum status) " for, "
                                     (:votes-against status) " against"
                                     (when (pos? (:votes-needed status))
                                       (str " (need " (:votes-needed status) " more for quorum)")))))]
        (assoc final-result
               :next-actions next-acts
               :message (case quorum-status
                          :verified "Mote verified! Quorum reached."
                          :refuted "Mote refuted. Quorum reached."
                          :contested "Mote contested - votes are mixed."
                          :pending pending-message))))))

;; -----------------------------------------------------------------------------
;; Batch Vote Command
;; -----------------------------------------------------------------------------

(defn- find-eligible-motes-for-voting
  "Find all motes that an agent can vote on.

   Returns motes that:
   - Need verification (status :fixed with :needs-verification taint)
   - Agent hasn't already voted on
   - Agent can vote on (not a contributor)

   Arguments:
   - repo-path: Path to the repository
   - agent: Agent identifier

   Returns sequence of [mote-id mote] pairs."
  [repo-path agent]
  (let [all-motes (store/load-all-motes repo-path)]
    (->> all-motes
         (filter (fn [[_id mote]]
                   (and (verify/needs-verification? mote)
                        (not (verify/has-voted? mote agent))
                        (session/can-vote? mote agent))))
         (sort-by first))))

(defn cmd-vote-all!
  "Cast verification votes on multiple motes at once.

   Options:
   - :session - Session token (required)
   - :for - Vote in favor of verification
   - :against - Vote against verification
   - :reason - Reason for votes (optional)
   - :agent - Agent name (defaults to session agent)
   - :pending - Only vote on motes needing verification (default true)
   - :dry-run - Show what would be voted on without voting

   Finds all motes that need verification and that the agent can vote on
   (excluding self-votes), then casts the specified vote on each.

   Returns map with:
   - :voted - Vector of mote IDs that were voted on
   - :skipped - Vector of maps with :mote-id and :reason for skipped motes
   - :total-voted - Count of votes cast
   - :total-skipped - Count of motes skipped
   - :dry-run - True if this was a dry run"
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [for against reason session dry-run]} options]

    ;; Validation
    (when (and for against)
      (throw (ex-info "Cannot vote both for and against"
                      {:type :validation-failed
                       :errors ["Provide either --for or --against, not both"]})))

    (when (and (not for) (not against))
      (throw (ex-info "Vote direction required"
                      {:type :validation-failed
                       :errors ["Provide --for or --against"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (but allow viewing dry-run without session)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (let [;; Get agent from session or options
          sess (when session
                 (session/load-session repo-path session))
          agent (or (:name options)
                    (:agent sess)
                    (when dry-run "dry-run-agent"))

          _ (when (and (not dry-run) (not agent))
              (throw (ex-info "Agent name is required"
                              {:type :validation-failed
                               :errors ["Provide --name or use a valid session"]})))

          ;; Find eligible motes
          eligible (find-eligible-motes-for-voting repo-path agent)
          eligible-ids (map first eligible)]

      (if dry-run
        ;; Dry run - just report what would be voted on
        {:voted []
         :would-vote (vec eligible-ids)
         :total-would-vote (count eligible-ids)
         :dry-run true
         :next-actions [(core/make-action (str "af vote-all " (if for "--for" "--against") " --session <session>")
                                     "Execute batch vote")
                        (core/status-action)]}

        ;; Actually cast votes
        (let [vote-type (if for :for :against)
              results (reduce
                       (fn [acc [mote-id _mote]]
                         (try
                           (verify/cast-vote! repo-path mote-id agent vote-type :reason reason)
                           (update acc :voted conj mote-id)
                           (catch Exception e
                             (update acc :skipped conj
                                     {:mote-id mote-id
                                      :reason (ex-message e)}))))
                       {:voted [] :skipped []}
                       eligible)]
          (assoc results
                 :total-voted (count (:voted results))
                 :total-skipped (count (:skipped results))
                 :dry-run false
                 :next-actions [(core/done-action session)
                                (core/status-action)]
                 :message (str "Voted on " (count (:voted results)) " motes.")))))))

;; -----------------------------------------------------------------------------
;; Taint Command
;; -----------------------------------------------------------------------------

(def ^:private valid-taints
  "Valid taint values."
  #{:needs-decomposition :needs-proposal-review :needs-refinement
    :needs-verification :needs-refs :needs-votes :needs-counterexample})

(defn- parse-taint
  "Parse taint string to keyword. Returns nil if invalid."
  [s]
  (when s
    (let [kw (keyword (str/replace (str/lower-case s) #"^:" ""))]
      (when (valid-taints kw)
        kw))))

(defn cmd-taint!
  "Add or remove taints from a mote.

   Arguments (in context):
   - :id - The mote ID to modify (required)

   Options:
   - :session - Session token (required)
   - :add - Taint to add (can be specified multiple times)
   - :remove - Taint to remove (can be specified multiple times)
   - :dry-run - Show what would change without executing

   Valid taints:
   - needs-decomposition
   - needs-proposal-review
   - needs-refinement
   - needs-verification
   - needs-refs
   - needs-votes
   - needs-counterexample

   At least one of --add or --remove must be provided.
   Adding taints requires :taint-add permission (verifier role).
   Removing taints requires :taint-remove permission (prover, ref-checker roles).

   Returns the updated mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [add remove session dry-run]} options
        ;; Support both single value and vector for add/remove
        adds (if (sequential? add) add (when add [add]))
        removes (if (sequential? remove) remove (when remove [remove]))]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to modify taints"]})))

    (when (and (empty? adds) (empty? removes))
      (throw (ex-info "No taint changes provided"
                      {:type :validation-failed
                       :errors ["Provide at least one --add or --remove"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run) (not session))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Parse and validate taints
      (let [parsed-adds (map parse-taint adds)
            parsed-removes (map parse-taint removes)]
        (when-let [invalid (first (filter nil? (concat
                                                 (when (seq adds) parsed-adds)
                                                 (when (seq removes) parsed-removes))))]
          (let [invalid-values (concat
                                 (filter #(nil? (parse-taint %)) adds)
                                 (filter #(nil? (parse-taint %)) removes))]
            (throw (ex-info "Invalid taint"
                            {:type :validation-failed
                             :errors [(str "Invalid taint: " (first invalid-values)
                                           ". Valid taints: " (str/join ", " (map name valid-taints)))]}))))

        (if dry-run
          ;; Dry run - show what would change
          (let [current-taints (set (:taint current-mote))
                new-taints (-> current-taints
                               (into (filter some? parsed-adds))
                               (disj (filter some? parsed-removes)))
                changes (cond-> []
                          (seq adds) (conj (str "add: " (str/join ", " (map name (filter some? parsed-adds)))))
                          (seq removes) (conj (str "remove: " (str/join ", " (map name (filter some? parsed-removes))))))]
            (core/dry-run-result
             :output (str "Current taints: " (if (seq current-taints)
                                               (str/join ", " (map name current-taints))
                                               "(none)")
                          (core/format-would-update
                           [{:id id :change (str/join "; " changes)}]))
             :would-update [{:id id :change (str/join "; " changes)}]
             :next-actions [(core/done-action (or session "<session>"))
                            (core/show-action id)]))

          ;; Execute
          (do
            ;; Enforce session - check both actions if both operations requested
            (when (seq adds)
              (session/enforce-session! repo-path session :taint-add id))
            (when (seq removes)
              (session/enforce-session! repo-path session :taint-remove id))

            ;; Apply taint changes
            (let [updated-mote (as-> current-mote m
                                (reduce mote/add-taint m (filter some? parsed-adds))
                                (reduce mote/remove-taint m (filter some? parsed-removes)))]
              (tx/atomic-write! repo-path
                                (str "Update taints on " id)
                                [updated-mote])
              (assoc updated-mote
                     :next-actions [(core/done-action session)
                                    (core/show-action id)]))))))))
