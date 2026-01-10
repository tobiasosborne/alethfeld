(ns alethfeld.cmd.init
  "Init command implementation."
  (:require [alethfeld.store :as store]
            [alethfeld.git :as git]
            [alethfeld.session :as session]
            [alethfeld.cmd.core :as core]))

(defn cmd-init!
  "Initialize an Alethfeld repository.

   Creates .alethfeld/ directory structure with:
   - config.edn (project configuration)
   - motes/ directory
   - proposed/ directory
   - archive/ directory
   - sessions/active/ directory
   - sessions/completed/ directory

   Also initializes git and commits the initial structure.

   Options:
   - :name - Project name (default: 'Alethfeld Project')
   - :dry-run - Show what would be created without executing

   Returns the config that was created."
  [{:keys [options repo-path] :or {repo-path "."}}]
  (let [project-name (:name options "Alethfeld Project")
        dry-run? (:dry-run options)]

    ;; Check if already initialized
    (when (store/repo-exists? repo-path)
      (throw (ex-info "Repository already initialized"
                      {:type :already-initialized
                       :path repo-path})))

    (if dry-run?
      ;; Dry run - show what would be created
      (core/dry-run-result
       :output (str "Would initialize Alethfeld repository: " project-name
                    (core/format-would-create
                     [".alethfeld/config.edn"
                      ".alethfeld/motes/"
                      ".alethfeld/proposed/"
                      ".alethfeld/archive/"
                      ".alethfeld/sessions/active/"
                      ".alethfeld/sessions/completed/"])
                    "\n\nWould create git commit: \"Initialize Alethfeld: " project-name "\"")
       :would-create [".alethfeld/"])
      ;; Execute
      (do
        ;; Initialize git first (so we can commit the init)
        (git/git-init! repo-path)
        ;; Configure git user if needed
        (when-not (git/git-config repo-path "user.name")
          (git/git-config! repo-path "user.name" "alethfeld"))
        (when-not (git/git-config repo-path "user.email")
          (git/git-config! repo-path "user.email" "alethfeld@local"))
        ;; Initialize repository structure
        (let [config (store/init-repo! repo-path :project-name project-name)]
          ;; Initialize session directories
          (session/ensure-session-dirs! repo-path)
          ;; Commit the initial structure
          (git/git-add-all! repo-path)
          (git/git-commit! repo-path (str "Initialize Alethfeld: " project-name))
          {:message (str "Initialized Alethfeld repository: " project-name)
           :config config
           :next-actions [(core/make-action "af create --root --claim \"Your main theorem\""
                                            "Create your first proof goal")
                          (core/status-action)]})))))
