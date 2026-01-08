(ns alethfeld.cmd
  "CLI command implementations.

   Each command function follows the pattern:
   - Takes a context map with :id, :args, :options
   - Returns data to be formatted and output
   - Throws ExceptionInfo for errors"
  (:require [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.tx :as tx]
            [alethfeld.cli :as cli]))

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
;; Handler Registration
;; -----------------------------------------------------------------------------

(defn register-handlers!
  "Register all command handlers with the CLI."
  []
  (cli/register-handler! "init" cmd-init!)
  (cli/register-handler! "show" cmd-show))

;; Auto-register handlers when namespace is loaded
(register-handlers!)
