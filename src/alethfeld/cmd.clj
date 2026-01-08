(ns alethfeld.cmd
  "CLI command implementations.

   Each command function follows the pattern:
   - Takes a context map with :id, :args, :options
   - Returns data to be formatted and output
   - Throws ExceptionInfo for errors"
  (:require [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.tx :as tx]
            [alethfeld.cli :as cli]
            [alethfeld.mote :as mote]
            [alethfeld.id :as id]))

;; -----------------------------------------------------------------------------
;; Init Command
;; -----------------------------------------------------------------------------

(defn cmd-init!
  "Initialize an Alethfeld repository.

   Creates .alethfeld/ directory structure with:
   - config.edn (project configuration)
   - motes/ directory
   - proposed/ directory
   - archive/ directory

   Also initializes git and commits the initial structure.

   Options:
   - :name - Project name (default: 'Alethfeld Project')

   Returns the config that was created."
  [{:keys [options]}]
  (let [repo-path "."
        project-name (:name options "Alethfeld Project")]
    ;; Check if already initialized
    (when (store/repo-exists? repo-path)
      (throw (ex-info "Repository already initialized"
                      {:type :already-initialized
                       :path repo-path})))
    ;; Initialize git first (so we can commit the init)
    (git/git-init! repo-path)
    ;; Configure git user if needed
    (when-not (git/git-config repo-path "user.name")
      (git/git-config! repo-path "user.name" "alethfeld"))
    (when-not (git/git-config repo-path "user.email")
      (git/git-config! repo-path "user.email" "alethfeld@local"))
    ;; Initialize repository structure
    (let [config (store/init-repo! repo-path :project-name project-name)]
      ;; Commit the initial structure
      (git/git-add-all! repo-path)
      (git/git-commit! repo-path (str "Initialize Alethfeld: " project-name))
      {:message (str "Initialized Alethfeld repository: " project-name)
       :config config})))

;; -----------------------------------------------------------------------------
;; Show Command
;; -----------------------------------------------------------------------------

(defn cmd-show
  "Display a mote's details.

   Arguments (in context):
   - :id - The mote ID to display

   Returns the mote map, or throws if not found."
  [{:keys [id]}]
  (let [repo-path "."
        mote (store/load-mote repo-path id)]
    (if mote
      mote
      (throw (ex-info "Mote not found"
                      {:type :not-found
                       :mote-id id})))))

;; -----------------------------------------------------------------------------
;; Create Command
;; -----------------------------------------------------------------------------

(defn- next-root-id
  "Get the next available root mote ID.
   Scans existing motes and returns the next integer as a string."
  [repo-path]
  (let [motes (store/load-all-motes repo-path)
        root-ids (->> (keys motes)
                      (filter #(= 1 (id/id-depth %)))
                      (map #(parse-long %))
                      (filter some?))]
    (str (if (empty? root-ids)
           1
           (inc (apply max root-ids))))))

(defn cmd-create!
  "Create a new mote.

   Arguments (in context):
   - :id - Parent mote ID (required unless --root)

   Options:
   - :claim - The claim text (required)
   - :root - Create root mote (no parent)
   - :difficulty - Difficulty 1-5 (optional, inherits from parent or defaults to 3)
   - :priority - Priority :p0-:p4 (optional, inherits from parent or defaults to :p2)
   - :agent - Agent name (default: 'cli-user')

   For root motes:
   - Generates next available root ID (1, 2, 3, ...)

   For child motes:
   - Parent must exist
   - Generates next child ID based on parent's existing children
   - Inherits priority/difficulty from parent if not specified

   Returns the created mote."
  [{:keys [id options]}]
  (let [repo-path "."
        {:keys [claim root difficulty priority agent]} options
        agent (or agent "cli-user")]

    ;; Validation
    (when-not claim
      (throw (ex-info "Claim is required"
                      {:type :validation-failed
                       :errors ["--claim is required"]})))

    (when (and root id)
      (throw (ex-info "Cannot specify both --root and parent ID"
                      {:type :validation-failed
                       :errors ["Use either --root or provide a parent ID, not both"]})))

    (when (and (not root) (not id))
      (throw (ex-info "Parent ID required for non-root motes"
                      {:type :validation-failed
                       :errors ["Provide parent ID or use --root for root motes"]})))

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (if root
      ;; Create root mote
      (let [new-id (next-root-id repo-path)
            new-mote (mote/make-root-mote new-id claim agent
                                          :difficulty (or difficulty 3)
                                          :priority (or priority :p2))
            _ (tx/atomic-write! repo-path
                                (str "Create root mote " new-id)
                                [new-mote])]
        new-mote)

      ;; Create child mote
      (let [parent (store/load-mote repo-path id)]
        (when-not parent
          (throw (ex-info "Parent mote not found"
                          {:type :not-found
                           :mote-id id})))

        (let [existing-children (:children parent)
              new-id (id/next-child-id id existing-children)
              new-mote (mote/make-child-mote new-id claim agent parent
                                             :difficulty (or difficulty (:difficulty parent))
                                             :priority (or priority (:priority parent)))
              updated-parent (mote/add-child parent new-id)
              _ (tx/atomic-write! repo-path
                                  (str "Create child mote " new-id)
                                  [new-mote updated-parent])]
          new-mote)))))

;; -----------------------------------------------------------------------------
;; Handler Registration
;; -----------------------------------------------------------------------------

(defn register-handlers!
  "Register all command handlers with the CLI."
  []
  (cli/register-handler! "init" cmd-init!)
  (cli/register-handler! "show" cmd-show)
  (cli/register-handler! "create" cmd-create!))

;; Auto-register handlers when namespace is loaded
(register-handlers!)
