(ns alethfeld.cmd.reference
  "Reference and dependency management commands.

   Includes commands for:
   - Withdrawing proposals
   - Adding external references
   - Adding internal assumptions (mote references)
   - Adding symbol definitions
   - Adding mote dependencies"
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.mote :as mote]
            [alethfeld.proposal :as proposal]
            [alethfeld.session :as session]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]))

;; -----------------------------------------------------------------------------
;; Withdraw Command
;; -----------------------------------------------------------------------------

(defn cmd-withdraw!
  "Withdraw a proposal that you created.

   Arguments (in context):
   - :id - The parent mote ID with the proposal (required)

   Options:
   - :session - Session token (required)
   - :dry-run - Show what would happen without executing

   Only the original proposer can withdraw their own proposal.
   The proposal must be pending (not yet approved or rejected).

   On withdrawal:
   - Proposed children are archived
   - Parent gets :needs-decomposition taint back
   - Parent proposal is cleared

   Returns map with:
   - :withdrawn-children - Vector of archived child IDs
   - :mote-id - The parent mote ID"
  [{:keys [id options repo-path] :or {repo-path "."}}]
  (let [session-id (:session options)
        dry-run? (:dry-run options)]

    ;; Validation
    (when-not id
      (throw (ex-info "Parent mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide parent mote ID with the proposal"]})))

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
            children (:children proposal)]
        (core/dry-run-result
         :output (str "Would withdraw proposal on " id
                      (core/format-would-delete children)
                      (core/format-would-update
                       [{:id id :change "clear proposal, add :needs-decomposition taint"}]))
         :would-delete children
         :would-update [{:id id :change "clear proposal"}]
         :next-actions [(core/done-action (or session-id "<session>"))
                        (core/show-action id)]))

      ;; Execute
      (let [sess (session/load-active-session repo-path session-id)]
        (when-not sess
          (throw (ex-info "Session not found or expired"
                          {:type :invalid-session
                           :session-id session-id})))
        (when (session/session-expired? sess)
          (throw (ex-info "Session has expired"
                          {:type :session-expired
                           :session-id session-id})))

        (let [agent (:agent sess)
              result (proposal/withdraw-proposal! repo-path id agent)]
          (assoc (:result result)
                 :mote-id id
                 :message "Proposal withdrawn. Children archived."
                 :next-actions [(core/done-action session-id)
                                (core/show-action id)]))))))

;; -----------------------------------------------------------------------------
;; Add-Ref Command
;; -----------------------------------------------------------------------------

(defn cmd-add-ref!
  "Add an external reference to a mote.

   Arguments (in context):
   - :id - The mote ID to add reference to (required)

   Options:
   - :session - Session token (required)
   - :ref - The citation/reference text (required)
   - :note - Optional note explaining what the reference provides

   Returns the updated mote."
  [{:keys [id options repo-path] :or {repo-path "."}}]
  ;; Note: Session enforcement handled by middleware
  (let [{:keys [ref note session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add reference to"]})))

    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the citation"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session validation (check token exists - enforcement done by middleware)
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Create external reference and add to mote
      (let [external-ref (cond-> {:type :external :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote external-ref)]
        (tx/atomic-write! repo-path
                          (str "Add external reference to " id)
                          [updated-mote])
        (assoc updated-mote
               :message "Reference added."
               :next-actions [(core/make-action (str "af add-ref " id " --session " session " --ref \"...\"")
                                           "Add another reference")
                              (core/done-action session)
                              (core/show-action id)])))))

;; -----------------------------------------------------------------------------
;; Add-Assumption Command
;; -----------------------------------------------------------------------------

(defn cmd-add-assumption!
  "Add an internal assumption (reference to another mote) to a mote.

   Arguments (in context):
   - :id - The mote ID to add assumption to (required)

   Options:
   - :session - Session token (required)
   - :ref - The referenced mote ID (required)
   - :note - Optional note explaining why this assumption is needed

   Returns the updated mote."
  [{:keys [id options repo-path] :or {repo-path "."}}]
  ;; Note: Session enforcement handled by middleware
  (let [{:keys [ref note session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add assumption to"]})))

    (when-not ref
      (throw (ex-info "Reference is required"
                      {:type :validation-failed
                       :errors ["Provide --ref with the mote ID to reference"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session validation (check token exists - enforcement done by middleware)
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Validate referenced mote exists
      (when-not (store/load-mote repo-path ref)
        (throw (ex-info "Referenced mote not found"
                        {:type :not-found
                         :mote-id ref})))

      ;; Create internal reference and add to mote
      (let [internal-ref (cond-> {:type :internal :ref ref}
                           note (assoc :note note))
            updated-mote (mote/add-assumption current-mote internal-ref)]
        (tx/atomic-write! repo-path
                          (str "Add internal assumption to " id)
                          [updated-mote])
        (assoc updated-mote
               :message "Assumption added."
               :next-actions [(core/make-action (str "af add-assumption " id " --session " session " --ref <mote-id>")
                                           "Add another assumption")
                              (core/done-action session)
                              (core/show-action id)])))))

;; -----------------------------------------------------------------------------
;; Add-Definition Command
;; -----------------------------------------------------------------------------

(defn cmd-add-definition!
  "Add a symbol definition to a mote.

   Arguments (in context):
   - :id - The mote ID to add definition to (required)

   Options:
   - :session - Session token (required)
   - :symbol - The symbol to define (required)
   - :meaning - The meaning/definition of the symbol (required)

   Returns the updated mote."
  [{:keys [id options repo-path] :or {repo-path "."}}]
  ;; Note: Session enforcement handled by middleware
  (let [{:keys [symbol meaning session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add definition to"]})))

    (when-not symbol
      (throw (ex-info "Symbol is required"
                      {:type :validation-failed
                       :errors ["Provide --symbol to define"]})))

    (when-not meaning
      (throw (ex-info "Meaning is required"
                      {:type :validation-failed
                       :errors ["Provide --meaning for the symbol"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session validation (check token exists - enforcement done by middleware)
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Create definition and add to mote
      (let [definition {:symbol symbol :meaning meaning}
            updated-mote (mote/add-definition current-mote definition)]
        (tx/atomic-write! repo-path
                          (str "Add definition to " id)
                          [updated-mote])
        (assoc updated-mote
               :message (str "Definition added: " symbol)
               :next-actions [(core/make-action (str "af add-definition " id " --session " session " --symbol \"...\" --meaning \"...\"")
                                           "Add another definition")
                              (core/done-action session)
                              (core/show-action id)])))))

;; -----------------------------------------------------------------------------
;; Add-Dependency Command
;; -----------------------------------------------------------------------------

(defn cmd-add-dep!
  "Add a dependency to a mote (mote X depends on mote Y).

   Arguments (in context):
   - :id - The mote ID to add dependency to (required)

   Options:
   - :session - Session token (required)
   - :depends-on - The mote ID that this mote depends on (required)
   - :reason - Optional note explaining why this dependency exists

   Returns the updated mote."
  [{:keys [id options repo-path] :or {repo-path "."}}]
  ;; Note: Session enforcement handled by middleware
  (let [{:keys [depends-on reason session]} options]

    ;; Validation
    (when-not id
      (throw (ex-info "Mote ID is required"
                      {:type :validation-failed
                       :errors ["Provide mote ID to add dependency to"]})))

    (when-not depends-on
      (throw (ex-info "Dependency target is required"
                      {:type :validation-failed
                       :errors ["Provide --depends-on with the mote ID"]})))

    (when (= id depends-on)
      (throw (ex-info "Mote cannot depend on itself"
                      {:type :validation-failed
                       :errors ["A mote cannot have a dependency on itself"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    ;; Session validation (check token exists - enforcement done by middleware)
    (when-not session
      (throw (ex-info "Session token is required"
                      {:type :validation-failed
                       :errors ["Provide --session with session token"]})))

    ;; Load and validate mote exists
    (let [current-mote (store/load-mote repo-path id)]
      (when-not current-mote
        (throw (ex-info "Mote not found"
                        {:type :not-found
                         :mote-id id})))

      ;; Validate dependency target exists
      (when-not (store/load-mote repo-path depends-on)
        (throw (ex-info "Dependency target mote not found"
                        {:type :not-found
                         :mote-id depends-on})))

      ;; Check for duplicate dependency
      (when (some #(= depends-on (:ref %)) (:depends-on current-mote))
        (throw (ex-info "Dependency already exists"
                        {:type :validation-failed
                         :errors [(str "Mote " id " already depends on " depends-on)]})))

      ;; Create dependency and add to mote
      (let [dependency (cond-> {:ref depends-on}
                          reason (assoc :reason reason))
            updated-mote (mote/add-dep current-mote dependency)]
        (tx/atomic-write! repo-path
                          (str "Add dependency " id " -> " depends-on)
                          [updated-mote])
        (assoc updated-mote
               :message (str "Dependency added: " id " -> " depends-on)
               :next-actions [(core/make-action (str "af add-dep " id " --session " session " --depends-on <mote-id>")
                                           "Add another dependency")
                              (core/done-action session)
                              (core/show-action id)])))))
