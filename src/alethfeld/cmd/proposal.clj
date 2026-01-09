(ns alethfeld.cmd.proposal
  "Proposal lifecycle commands: propose, approve, approve-all, reject."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.id :as id]
            [alethfeld.proposal :as proposal]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(defn- parse-claims
  "Parse claims from command-line args.

   Each claim is a string. Can optionally include difficulty with @ notation
   and atomic marker with ! notation:
   'My claim @3' -> {:claim 'My claim' :difficulty 3}
   'My claim !' -> {:claim 'My claim' :atomic true}
   'My claim @3!' -> {:claim 'My claim' :difficulty 3 :atomic true}
   'My claim' -> {:claim 'My claim'}

   Returns vector of {:claim ... :difficulty ... :atomic ...} maps."
  [args]
  (mapv (fn [arg]
          (let [;; Check for trailing ! (atomic marker)
                [arg-without-atomic atomic?] (if (str/ends-with? arg "!")
                                               [(subs arg 0 (dec (count arg))) true]
                                               [arg false])
                ;; Check for @N difficulty notation
                [claim difficulty] (if-let [[_ c d] (re-matches #"(.+?)\s*@(\d+)\s*$" arg-without-atomic)]
                                     [(str/trim c) (Integer/parseInt d)]
                                     [arg-without-atomic nil])]
            (cond-> {:claim claim}
              difficulty (assoc :difficulty difficulty)
              atomic? (assoc :atomic true))))
        args))

(defn- merge-option-claims
  "Merge claims from --claim options with --difficulty and --atomic options.

   The --difficulty and --atomic options are positional and apply to claims
   in order. If there are fewer difficulty/atomic values than claims, the
   remaining claims inherit from parent (difficulty) or default to false (atomic).

   Arguments:
   - claim-texts: Vector of claim text strings from --claim options
   - difficulties: Vector of difficulty values from --difficulty options
   - atomics: Vector of booleans from --atomic options

   Returns vector of {:claim ... :difficulty ... :atomic ...} maps."
  [claim-texts difficulties atomics]
  (mapv (fn [idx claim-text]
          (let [difficulty (get difficulties idx)
                atomic? (get atomics idx)]
            (cond-> {:claim claim-text}
              difficulty (assoc :difficulty difficulty)
              atomic? (assoc :atomic true))))
        (range (count claim-texts))
        claim-texts))

(defn- find-motes-with-proposals
  "Find all motes that have pending proposals the agent can vote on."
  [repo-path agent]
  (let [all-motes (store/load-all-motes repo-path)]
    (->> all-motes
         (filter (fn [[_id mote]]
                   (when-let [prop (:proposal mote)]
                     (and (= :pending (:status prop))
                          (not (proposal/has-voted? prop agent))))))
         (sort-by first))))

;; -----------------------------------------------------------------------------
;; Propose Command
;; -----------------------------------------------------------------------------

(defn cmd-propose!
  "Create a proposal to decompose a mote into children.

   Arguments (in context):
   - :id - The parent mote ID (required)
   - :args - Child claims (required unless --claim used)
             Each claim can optionally include difficulty with @ notation:
             'My claim @3' sets difficulty to 3
             Add ! suffix to mark as atomic: 'My claim !' or 'My claim @3!'

   Options:
   - :session - Session token (required)
   - :claim - Claim text (repeatable, alternative to positional args)
   - :difficulty - Difficulty for claims (repeatable, positional)
   - :atomic - Mark claim as atomic (repeatable, positional)
   - :agent - Agent name (defaults to session agent)
   - :dry-run - Show what would be created without executing

   Creates proposed children with :proposed status and attaches
   a proposal to the parent. Sets parent taint to :needs-proposal-review.
   Atomic claims get :needs-verification taint instead of :needs-decomposition.

   Returns map with:
   - :proposal - The created proposal
   - :children - Vector of created child motes"
  [{:keys [id args options]}]
  (let [repo-path "."
        session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID"]})))

    ;; Get claims from both args and --claim options
    (let [option-claims (:claim options)
          positional-claims args]
      (when (and (empty? positional-claims) (empty? option-claims))
        (throw (ex-info "At least one claim is required"
                        {:type :validation-failed
                         :errors ["Provide claims as arguments or with --claim"]})))

      ;; Check repository exists
      (when-not (store/repo-exists? repo-path)
        (throw (ex-info "Not an Alethfeld repository"
                        {:type :not-initialized
                         :path repo-path})))

      ;; Session enforcement (skip for dry-run)
      (when (and (not dry-run?) (not session-id))
        (throw (ex-info "Session token is required"
                        {:type :validation-failed
                         :errors ["Provide --session with session token"]})))

      ;; Parse positional claims (with @N and ! notation support)
      (let [parsed-positional (parse-claims positional-claims)
            ;; Parse option-based claims (merge with --difficulty and --atomic)
            parsed-options (when (seq option-claims)
                            (merge-option-claims option-claims
                                                 (:difficulty options)
                                                 (:atomic options)))
            ;; Combine claims (positional first, then options)
            claims (vec (concat parsed-positional parsed-options))]

        (if dry-run?
          ;; Dry run - show what would be created
          (let [parent (store/load-mote repo-path id)
                _ (when-not parent
                    (throw (ex-info "Parent mote not found"
                                    {:type :not-found
                                     :mote-id id})))
                existing-children (:children parent)
                ;; Calculate what IDs would be assigned
                child-infos (map-indexed
                             (fn [idx claim-info]
                               (let [child-id (id/next-child-id id (concat existing-children
                                                                            (map :id (take idx []))))]
                                 {:id (str id "." (+ 1 idx (count existing-children)))
                                  :status :proposed
                                  :claim (:claim claim-info)
                                  :atomic (:atomic claim-info)}))
                             claims)
                config (store/load-config repo-path)]
            (core/dry-run-result
             :output (str (core/format-would-create child-infos)
                          (core/format-would-update
                           [{:id id :change "set taint :needs-proposal-review"}])
                          "\n\nWould require " (:proposal-quorum config 1) " advisor votes to approve.")
             :would-create (vec child-infos)
             :would-update [{:id id :change "set taint :needs-proposal-review"}]
             :next-actions [(core/done-action (or session-id "<session>"))
                            (core/show-action id)]))

          ;; Execute
          (let [sess (session/enforce-session! repo-path session-id :propose id)
                agent (or (:name options) (:agent sess))
                result (proposal/create-proposal! repo-path id claims agent)
                proposal-result (:result result)
                child-count (count (:children proposal-result))]
            (assoc proposal-result
                   :next-actions [(core/done-action session-id)
                                  (core/show-action id)]
                   :message (str "Created proposal with " child-count " children. Waiting for advisor approval."))))))))

;; -----------------------------------------------------------------------------
;; Approve Command
;; -----------------------------------------------------------------------------

(defn cmd-approve!
  "Vote to approve a proposal on a mote.

   Arguments (in context):
   - :id - The mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :agent - Agent name (defaults to session agent)
   - :reason - Reason for approval (optional)
   - :dry-run - Show what would happen without executing

   If quorum is reached:
   - Children move from proposed/ to motes/ with :fixed status
   - Parent :children is populated
   - Parent proposal is cleared

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :approved or :pending
   - :promoted-children - Child IDs if approved"
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        reason (:reason options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run?
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            proposal (:proposal mote)
            _ (when-not proposal
                (throw (ex-info "No active proposal on this mote"
                                {:type :no-proposal
                                 :mote-id id})))
            config (store/load-config repo-path)
            current-approvals (count (filter #(= :approve (:type %)) (:votes proposal)))
            quorum (:proposal-quorum config 1)
            would-reach-quorum? (>= (inc current-approvals) quorum)]
        (core/dry-run-result
         :output (str "Would record approval vote on " id
                      "\n\nCurrent votes: " current-approvals "/" quorum " approvals"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached!"
                             (core/format-would-update
                              (mapv (fn [child-id] {:id child-id :change "promote to :fixed status"})
                                    (:children proposal)))
                             (core/format-would-update [{:id id :change "clear proposal, update children list"}]))
                        (str "\n\nQuorum not yet reached. " (- quorum (inc current-approvals)) " more votes needed.")))
         :would-update (if would-reach-quorum?
                         (conj (mapv (fn [child-id] {:id child-id :change "promote"})
                                     (:children proposal))
                               {:id id :change "clear proposal"})
                         [{:id id :change "add approval vote"}])
         :next-actions [(core/done-action (or session-id "<session>"))
                        (core/show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session-id :approve id)
            agent (or (:name options) (:agent sess))
            result (proposal/approve-proposal! repo-path id agent :reason reason)
            approve-result (:result result)
            quorum-status (:quorum-status approve-result)]
        (assoc approve-result
               :next-actions (if (= :approved quorum-status)
                               ;; Quorum reached - children promoted
                               [(core/done-action session-id)]
                               ;; Still pending - waiting for more votes
                               [(core/done-action session-id)
                                (core/show-action id)])
               :message (if (= :approved quorum-status)
                          "Proposal approved! Children promoted to fixed status."
                          "Vote recorded. Waiting for more advisor votes."))))))

;; -----------------------------------------------------------------------------
;; Approve-All Command
;; -----------------------------------------------------------------------------

(defn cmd-approve-all!
  "Approve all pending proposals in session scope.

   Options:
   - :session - Session token (required)
   - :name - Agent name (defaults to session agent)
   - :reason - Reason for all approvals (optional)
   - :dry-run - Show what would be approved without approving

   Finds all motes that have pending proposals that the agent can vote on
   (excluding those already voted on), then casts an approval vote on each.

   Returns map with:
   - :approved - Vector of mote IDs that were approved
   - :skipped - Vector of maps with :mote-id and :reason for skipped motes
   - :total-approved - Count of approvals cast
   - :total-skipped - Count of motes skipped
   - :dry-run - True if this was a dry run"
  [{:keys [options]}]
  (let [repo-path "."
        {:keys [session reason dry-run]} options]

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

          ;; Find motes with pending proposals
          eligible (find-motes-with-proposals repo-path agent)
          eligible-ids (map first eligible)]

      (if dry-run
        ;; Dry run - just report what would be approved
        {:approved []
         :would-approve (vec eligible-ids)
         :total-would-approve (count eligible-ids)
         :dry-run true
         :output (str "Would approve " (count eligible-ids) " proposals: "
                      (str/join ", " eligible-ids))
         :next-actions [(core/make-action "af approve-all --session <session> --reason \"...\""
                                     "Execute batch approval")
                        (core/status-action)]}

        ;; Actually cast approvals
        (let [results (reduce
                       (fn [acc [mote-id _mote]]
                         (try
                           (proposal/approve-proposal! repo-path mote-id agent :reason reason)
                           (update acc :approved conj mote-id)
                           (catch Exception e
                             (update acc :skipped conj
                                     {:mote-id mote-id
                                      :reason (ex-message e)}))))
                       {:approved [] :skipped []}
                       eligible)]
          (assoc results
                 :total-approved (count (:approved results))
                 :total-skipped (count (:skipped results))
                 :dry-run false
                 :output (str "Approved " (count (:approved results)) " proposals: "
                              (str/join ", " (:approved results)))
                 :next-actions [(core/done-action session)
                                (core/status-action)]
                 :message (str "Approved " (count (:approved results)) " proposals.")))))))

;; -----------------------------------------------------------------------------
;; Reject Command
;; -----------------------------------------------------------------------------

(defn cmd-reject!
  "Vote to reject a proposal on a mote.

   Arguments (in context):
   - :id - The mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :agent - Agent name (defaults to session agent)
   - :reason - Reason for rejection (optional)
   - :dry-run - Show what would happen without executing

   If quorum is reached:
   - Children move from proposed/ to archive/ with :rejected status
   - Parent proposal is cleared
   - Parent gets :needs-decomposition taint

   Returns map with:
   - :vote-cast - The vote that was cast
   - :quorum-status - :rejected or :pending
   - :archived-children - Child IDs if rejected"
  [{:keys [id options]}]
  (let [repo-path "."
        session-id (:session options)
        reason (:reason options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID with proposal"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session enforcement (skip for dry-run)
    (when (and (not dry-run?) (not session-id))
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    (if dry-run?
      ;; Dry run - show what would happen
      (let [mote (store/load-mote repo-path id)
            _ (when-not mote
                (throw (ex-info "Mote not found"
                                {:type :not-found
                                 :mote-id id})))
            proposal (:proposal mote)
            _ (when-not proposal
                (throw (ex-info "No active proposal on this mote"
                                {:type :no-proposal
                                 :mote-id id})))
            config (store/load-config repo-path)
            current-rejections (count (filter #(= :reject (:type %)) (:votes proposal)))
            quorum (:proposal-quorum config 1)
            would-reach-quorum? (>= (inc current-rejections) quorum)]
        (core/dry-run-result
         :output (str "Would record rejection vote on " id
                      "\n\nCurrent votes: " current-rejections "/" quorum " rejections"
                      (if would-reach-quorum?
                        (str "\n\nQuorum would be reached!"
                             (core/format-would-delete (:children proposal))
                             (core/format-would-update [{:id id :change "clear proposal, add :needs-decomposition taint"}]))
                        (str "\n\nQuorum not yet reached. " (- quorum (inc current-rejections)) " more votes needed.")))
         :would-delete (when would-reach-quorum? (:children proposal))
         :would-update [{:id id :change (if would-reach-quorum?
                                          "clear proposal, add :needs-decomposition"
                                          "add rejection vote")}]
         :next-actions [(core/done-action (or session-id "<session>"))
                        (core/show-action id)]))

      ;; Execute
      (let [sess (session/enforce-session! repo-path session-id :reject id)
            agent (or (:name options) (:agent sess))
            result (proposal/reject-proposal! repo-path id agent :reason reason)
            reject-result (:result result)
            quorum-status (:quorum-status reject-result)]
        (assoc reject-result
               :next-actions (if (= :rejected quorum-status)
                               ;; Quorum reached - children archived
                               [(core/done-action session-id)]
                               ;; Still pending - waiting for more votes
                               [(core/done-action session-id)
                                (core/show-action id)])
               :message (if (= :rejected quorum-status)
                          "Proposal rejected. Children archived."
                          "Vote recorded. Waiting for more advisor votes."))))))
