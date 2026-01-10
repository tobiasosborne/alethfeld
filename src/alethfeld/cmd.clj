(ns alethfeld.cmd
  "CLI command implementations - aggregator namespace.

   This namespace re-exports all command functions from cmd/ submodules
   for backward compatibility. New code should import from specific
   submodules directly:

   - alethfeld.cmd.core      - Shared helpers (actions, dry-run)
   - alethfeld.cmd.init      - Repository initialization
   - alethfeld.cmd.show      - Mote display
   - alethfeld.cmd.create    - Mote creation
   - alethfeld.cmd.ready     - Job discovery and claiming
   - alethfeld.cmd.proposal  - Propose, approve, reject workflows
   - alethfeld.cmd.update    - Mote field updates
   - alethfeld.cmd.voting    - Verification voting and taints
   - alethfeld.cmd.session   - Session lifecycle (claim, unclaim, done)
   - alethfeld.cmd.reference - References, assumptions, dependencies
   - alethfeld.cmd.utility   - Check, repair, log, sync, tree, status
   - alethfeld.cmd.config    - Configuration management

   Each command function follows the pattern:
   - Takes a context map with :id, :args, :options
   - Returns data to be formatted and output
   - Throws ExceptionInfo for errors

   All commands return a :next-actions key with suggested next steps:
   [{:command \"af ...\" :description \"...\"}]"
  (:require [alethfeld.cli :as cli]
            [alethfeld.cmd.init :as init]
            [alethfeld.cmd.show :as show]
            [alethfeld.cmd.create :as create]
            [alethfeld.cmd.ready :as ready]
            [alethfeld.cmd.proposal :as proposal]
            [alethfeld.cmd.update :as update]
            [alethfeld.cmd.voting :as voting]
            [alethfeld.cmd.session :as session]
            [alethfeld.cmd.reference :as reference]
            [alethfeld.cmd.utility :as utility]
            [alethfeld.cmd.config :as config]
            [alethfeld.cmd.workflow :as workflow]
            [alethfeld.cmd.sessions :as sessions]))

;; -----------------------------------------------------------------------------
;; Re-exported Commands (for backward compatibility)
;; -----------------------------------------------------------------------------

;; Init
(def cmd-init! init/cmd-init!)

;; Show
(def cmd-show show/cmd-show)

;; Create
(def cmd-create! create/cmd-create!)

;; Ready
(def cmd-ready ready/cmd-ready)

;; Proposal lifecycle
(def cmd-propose! proposal/cmd-propose!)
(def cmd-approve! proposal/cmd-approve!)
(def cmd-approve-all! proposal/cmd-approve-all!)
(def cmd-reject! proposal/cmd-reject!)

;; Update
(def cmd-update! update/cmd-update!)

;; Voting
(def cmd-vote! voting/cmd-vote!)
(def cmd-vote-all! voting/cmd-vote-all!)
(def cmd-taint! voting/cmd-taint!)

;; Session management
(def cmd-claim! session/cmd-claim!)
(def cmd-unclaim! session/cmd-unclaim!)
(def cmd-done! session/cmd-done!)

;; Reference management
(def cmd-withdraw! reference/cmd-withdraw!)
(def cmd-add-ref! reference/cmd-add-ref!)
(def cmd-add-assumption! reference/cmd-add-assumption!)
(def cmd-add-definition! reference/cmd-add-definition!)
(def cmd-add-dep! reference/cmd-add-dep!)

;; Utility commands
(def cmd-check utility/cmd-check)
(def cmd-repair utility/cmd-repair)
(def cmd-log utility/cmd-log)
(def cmd-sync! utility/cmd-sync!)
(def cmd-tree utility/cmd-tree)
(def cmd-status utility/cmd-status)

;; Config
(def cmd-config config/cmd-config)

;; Workflow
(def cmd-workflow workflow/cmd-workflow)

;; Sessions
(def cmd-sessions sessions/cmd-sessions)

;; -----------------------------------------------------------------------------
;; Private helpers re-exported for tests
;; (Tests use #'cmd/private-fn to access these)
;; -----------------------------------------------------------------------------

;; From core.clj
(def ^:private name-looks-like-role? (deref #'alethfeld.cmd.core/name-looks-like-role?))
(def ^:private format-role-hint (deref #'alethfeld.cmd.core/format-role-hint))

;; From ready.clj
(def ^:private cleanup-stale-sessions-and-claims! (deref #'ready/cleanup-stale-sessions-and-claims!))
(def ^:private parse-difficulty-spec (deref #'ready/parse-difficulty-spec))
(def ^:private parse-priority-spec (deref #'ready/parse-priority-spec))
(def ^:private resolve-children (deref #'ready/resolve-children))

;; From proposal.clj
(def ^:private parse-claims (deref #'proposal/parse-claims))

;; From update.clj
(def ^:private parse-priority (deref #'update/parse-priority))

;; From voting.clj
(def ^:private find-eligible-motes-for-voting (deref #'voting/find-eligible-motes-for-voting))
(def ^:private parse-taint (deref #'voting/parse-taint))

;; From utility.clj
(def ^:private format-status (deref #'utility/format-status))
(def ^:private format-taints (deref #'utility/format-taints))
(def ^:private truncate-claim (deref #'utility/truncate-claim))
(def ^:private render-tree (deref #'utility/render-tree))

;; -----------------------------------------------------------------------------
;; Handler Registration
;; -----------------------------------------------------------------------------

(defn register-handlers!
  "Register all command handlers with the CLI."
  []
  (cli/register-handler! "init" cmd-init!)
  (cli/register-handler! "show" cmd-show)
  (cli/register-handler! "create" cmd-create!)
  (cli/register-handler! "ready" cmd-ready)
  (cli/register-handler! "propose" cmd-propose!)
  (cli/register-handler! "approve" cmd-approve!)
  (cli/register-handler! "reject" cmd-reject!)
  (cli/register-handler! "update" cmd-update!)
  (cli/register-handler! "vote" cmd-vote!)
  (cli/register-handler! "vote-all" cmd-vote-all!)
  (cli/register-handler! "approve-all" cmd-approve-all!)
  (cli/register-handler! "taint" cmd-taint!)
  (cli/register-handler! "claim" cmd-claim!)
  (cli/register-handler! "unclaim" cmd-unclaim!)
  (cli/register-handler! "done" cmd-done!)
  (cli/register-handler! "withdraw" cmd-withdraw!)
  (cli/register-handler! "add-ref" cmd-add-ref!)
  (cli/register-handler! "add-assumption" cmd-add-assumption!)
  (cli/register-handler! "add-definition" cmd-add-definition!)
  (cli/register-handler! "add-dep" cmd-add-dep!)
  (cli/register-handler! "check" cmd-check)
  (cli/register-handler! "repair" cmd-repair)
  (cli/register-handler! "log" cmd-log)
  (cli/register-handler! "sync" cmd-sync!)
  (cli/register-handler! "config" cmd-config)
  (cli/register-handler! "tree" cmd-tree)
  (cli/register-handler! "status" cmd-status)
  (cli/register-handler! "workflow" cmd-workflow)
  (cli/register-handler! "sessions" cmd-sessions))

;; Auto-register handlers when namespace is loaded
(register-handlers!)
