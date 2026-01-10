(ns alethfeld.cli
  "Alethfeld CLI entry point and infrastructure.

   Provides:
   - Argument parsing with clojure.tools.cli
   - Command dispatch routing
   - Output formatting (EDN/JSON)
   - Error handling and exit codes"
  (:require [clojure.tools.cli :as cli]
            [clojure.string :as str]
            [clojure.data.json :as json]
            [clojure.pprint :as pprint]
            [alethfeld.errors :as err]
            [alethfeld.store :as store]
            [alethfeld.session :as session]
            [alethfeld.middleware :as middleware]
            [alethfeld.util :as util])
  (:gen-class))

;; Command handlers are registered by alethfeld.cmd namespace.
;; Require it at runtime to avoid circular dependency.
(defn- ensure-handlers!
  "Ensure command handlers are loaded."
  []
  (require 'alethfeld.cmd))

;; -----------------------------------------------------------------------------
;; Version
;; -----------------------------------------------------------------------------

(def version "0.2.0")

(defn suggest-command
  "Find the closest matching command to the given input.
   Returns the suggestion if Levenshtein distance is <= 2, otherwise nil."
  [input known-commands]
  (let [input-lower (str/lower-case input)
        distances (for [cmd known-commands]
                    [cmd (util/levenshtein-distance input-lower cmd)])
        [best-cmd best-dist] (reduce (fn [[bc bd] [c d]]
                                       (if (< d bd) [c d] [bc bd]))
                                     [nil Integer/MAX_VALUE]
                                     distances)]
    (when (and best-cmd (<= best-dist 2))
      best-cmd)))

;; -----------------------------------------------------------------------------
;; Environment Variables
;; -----------------------------------------------------------------------------

(defn get-default-name
  "Get the default agent name from AF_NAME (or legacy AF_AGENT) environment variable.
   Returns nil if not set. Prefers AF_NAME over AF_AGENT."
  []
  (or (System/getenv "AF_NAME")
      (System/getenv "AF_AGENT")))

(defn get-default-session
  "Get the default session token from AF_SESSION environment variable.
   Returns nil if not set."
  []
  (System/getenv "AF_SESSION"))

;; -----------------------------------------------------------------------------
;; Deprecated Option Support
;; -----------------------------------------------------------------------------

(def ^:dynamic *deprecation-warnings*
  "Atom to collect deprecation warnings during argument parsing."
  (atom []))

(defn deprecated-agent-option
  "Create a deprecated --agent option that maps to :name.
   Collects a warning when used."
  [description]
  [nil "--agent NAME" (str description " (DEPRECATED: use --name)")
   :assoc-fn (fn [m _k v]
               (swap! *deprecation-warnings* conj
                      "Warning: --agent is deprecated, use --name instead")
               (assoc m :name v))])

;; -----------------------------------------------------------------------------
;; Session Auto-Inference
;; -----------------------------------------------------------------------------

(def ^:dynamic *session-inference-message*
  "Atom to capture session auto-inference message for display."
  (atom nil))

(defn- try-auto-infer-session
  "Try to auto-infer session when agent has exactly one active session.

   This implements the priority order:
   1. Explicit --session flag (already handled before this)
   2. AF_SESSION environment variable (already handled before this)
   3. Auto-inference via @current (this function)

   Arguments:
   - options: Parsed options map (may contain :session and :name)

   Returns updated options map with :session set if auto-inferred,
   or original options if auto-inference not possible/applicable.

   Side effects: Sets *session-inference-message* atom with status message."
  [options]
  (if (:session options)
    ;; Session already provided - no inference needed
    options
    ;; Try auto-inference if we have an agent name
    (if-let [agent (:name options)]
      (let [repo-path "."
            result (session/resolve-session repo-path {:agent agent})]
        (cond
          ;; Successfully auto-resolved - update options and set message
          (:auto-resolved? result)
          (do
            (reset! *session-inference-message* (:message result))
            (assoc options :session (:session-id result)))

          ;; Multiple sessions - set error message for later handling
          (= :multiple-sessions (:error result))
          (do
            (reset! *session-inference-message*
                    {:error true
                     :type :multiple-sessions
                     :message (:message result)
                     :sessions (:sessions result)})
            options)

          ;; No sessions - leave as-is, command may not need session
          :else
          options))
      ;; No agent name - can't auto-infer
      options)))

(defn- format-multiple-sessions-error
  "Format error message when agent has multiple active sessions."
  [error-info]
  (let [{:keys [message sessions]} error-info]
    (str message "\n"
         (str/join "\n"
                   (map (fn [{:keys [session-id role mote-id]}]
                          (str "  --session " (subs session-id 0 (min 11 (count session-id)))
                               "...  (role: " (name role) ", mote: " mote-id ")"))
                        sessions)))))

;; -----------------------------------------------------------------------------
;; Exit Codes
;; -----------------------------------------------------------------------------

(def exit-codes
  "Standard exit codes."
  {:success 0
   :error 1
   :invalid-args 2
   :not-found 3
   :validation-error 4
   :conflict 5})

;; -----------------------------------------------------------------------------
;; Output Formatting
;; -----------------------------------------------------------------------------

(defn format-edn
  "Format data as pretty-printed EDN string."
  [data]
  (with-out-str (pprint/pprint data)))

(defn format-json
  "Format data as JSON string."
  [data]
  (json/write-str data :escape-slash false))

(defn format-next-actions
  "Format next-actions for human-readable output."
  [next-actions]
  (when (seq next-actions)
    (str "\nNext steps:\n"
         (str/join "\n"
                   (map (fn [{:keys [command description]}]
                          (str "  → " command (when description (str "    " description))))
                        next-actions)))))

(defn format-human
  "Format data for human-readable output.

   Extracts :output or :message from the result, and appends
   formatted :next-actions if present.

   Returns nil if no human-readable content is available."
  [data]
  (when (map? data)
    (let [main-output (or (:output data) (:message data))
          next-actions (:next-actions data)
          terminate-msg (:terminate-message data)]
      (when (or main-output next-actions terminate-msg)
        (str/join "\n"
                  (remove nil?
                          [main-output
                           terminate-msg
                           (format-next-actions next-actions)]))))))

(defn format-output
  "Format data according to specified format.

   Arguments:
   - data: The data to format
   - fmt: :text, :edn, or :json (default :text)

   For :text format, extracts human-readable :output/:message and
   :next-actions. Falls back to EDN if no human content available.

   Returns formatted string."
  [data fmt]
  (case fmt
    :json (format-json data)
    :edn (format-edn data)
    :text (or (format-human data) (format-edn data))
    ;; Default to text (human-readable)
    (or (format-human data) (format-edn data))))

;; -----------------------------------------------------------------------------
;; Exit Handling
;; -----------------------------------------------------------------------------

(def ^:dynamic *exit-fn*
  "Function to call for exit. Bound to System/exit in production,
   can be rebound for testing."
  (fn [code] (System/exit code)))

(defn exit!
  "Exit with code and optional message.

   Arguments:
   - code: Exit code keyword or number
   - message: Optional message to print

   Options:
   - :stream - :out or :err (default :out for success, :err for errors)"
  ([code]
   (exit! code nil))
  ([code message & {:keys [stream]}]
   (let [code-num (if (keyword? code)
                    (get exit-codes code 1)
                    code)
         stream (or stream (if (zero? code-num) :out :err))]
     (when message
       (binding [*out* (if (= stream :err) *err* *out*)]
         (println message)))
     (*exit-fn* code-num))))

;; -----------------------------------------------------------------------------
;; Error Handling
;; -----------------------------------------------------------------------------

(def ^:dynamic *verbose*
  "When true, error messages include stack traces."
  false)

(defn error-message
  "Generate user-friendly error message from exception.
   Delegates to alethfeld.errors/format-error for consistent formatting."
  [ex]
  (err/format-error ex))

(defn- format-stack-trace
  "Format exception stack trace for verbose output."
  [ex]
  (let [sw (java.io.StringWriter.)
        pw (java.io.PrintWriter. sw)]
    (.printStackTrace ex pw)
    (str sw)))

(defn handle-error
  "Handle an exception and exit appropriately.

   Arguments:
   - ex: The exception to handle
   - fmt: Output format (:edn or :json)
   - verbose: Whether to include stack traces"
  ([ex fmt]
   (handle-error ex fmt false))
  ([ex fmt verbose]
   (let [data (ex-data ex)
         code (err/error-type->exit-code (:type data))]
     (if (= fmt :json)
       (do
         (println (format-json (cond-> {:error (ex-message ex)
                                        :type (:type data)
                                        :details (dissoc data :type)}
                                 verbose (assoc :stack-trace (format-stack-trace ex)))))
         (*exit-fn* (get exit-codes code 1)))
       (do
         (binding [*out* *err*]
           (println (error-message ex))
           (when verbose
             (println)
             (println "Stack trace:")
             (println (format-stack-trace ex))))
         (*exit-fn* (get exit-codes code 1)))))))

;; -----------------------------------------------------------------------------
;; Global Options
;; -----------------------------------------------------------------------------

(def global-options
  "Global CLI options available to all commands."
  [["-f" "--format FORMAT" "Output format: text (default), edn, or json"
    :default :text
    :parse-fn keyword
    :validate [#{:text :edn :json} "Must be 'text', 'edn', or 'json'"]]
   [nil "--verbose" "Show detailed error messages with stack traces"]
   ["-h" "--help" "Show help"]
   ["-v" "--version" "Show version"]])

;; -----------------------------------------------------------------------------
;; Command Definitions
;; -----------------------------------------------------------------------------

(def commands
  "Map of command names to their metadata.
   Each command has:
   - :description - Short description
   - :usage - Usage string
   - :options - Command-specific CLI options
   - :handler - Function to handle the command (set later)"
  {"init" {:description "Initialize .alethfeld/ in current directory"
           :usage "af init [--name NAME]"
           :options [["-n" "--name NAME" "Project name"
                      :default "Alethfeld Project"]]}

   "show" {:description "Display mote details"
           :usage "af show <id>"
           :options []
           :requires-id true}

   "create" {:description "Create a mote"
             :usage "af create <parent-id> --claim TEXT [OPTIONS]\n       af create --root --claim TEXT [OPTIONS]"
             :options [["-c" "--claim TEXT" "The claim text (required)"
                        :missing "Claim is required"]
                       ["-r" "--root" "Create root mote (no parent)"]
                       ["-d" "--difficulty N" "Difficulty 1-5"
                        :parse-fn #(Integer/parseInt %)
                        :validate [#(<= 1 % 5) "Must be 1-5"]]
                       ["-p" "--priority P" "Priority (p0-p4)"
                        :parse-fn keyword
                        :validate [#{:p0 :p1 :p2 :p3 :p4} "Must be p0-p4"]]
                       ["-n" "--name NAME" "Agent name (created-by)"
                        :default "cli-user"]
                       (deprecated-agent-option "Agent name")]
             :optional-id true}

   "ready" {:description "Get next job(s) for an agent"
            :usage "af ready [OPTIONS]"
            :options [["-n" "--name NAME" "Agent name (auto-claims job)"]
                      ["-r" "--role ROLE" "Filter by role"
                       :parse-fn keyword
                       :validate [#{:proposer :advisor :prover :verifier :ref-checker :counterexample}
                                  "Invalid role"]]
                      ["-d" "--difficulty SPEC" "Difficulty filter (N or N-M)"]
                      ["-p" "--priority SPEC" "Priority filter (pN or pN-pM)"]
                      ["-M" "--mote ID" "Request specific mote (by ID)"]
                      ["-m" "--max N" "Max jobs to return"
                       :default 1
                       :parse-fn #(Integer/parseInt %)
                       :validate [pos? "Must be positive"]]
                      [nil "--no-claim" "Don't auto-claim jobs"]
                      [nil "--reserve" "Reserve job without claiming (for orchestrators)"]
                      [nil "--claim-reservation TOKEN" "Claim a previously reserved job"]
                      (deprecated-agent-option "Agent name")]}

   "propose" {:description "Propose decomposition into children"
              :usage "af propose <parent-id> --session TOKEN --claim TEXT [--difficulty N] [--claim TEXT ...]"
              :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                        ["-c" "--claim TEXT" "Claim text (repeatable)"
                         :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                        ["-d" "--difficulty N" "Difficulty for claims (repeatable)"
                         :parse-fn #(Integer/parseInt %)
                         :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                        ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                        (deprecated-agent-option "Agent name")]
              :requires-id true}

   "approve" {:description "Vote to approve a proposal"
              :usage "af approve <parent-id> --session TOKEN [--reason TEXT]"
              :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                        ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                        ["-R" "--reason TEXT" "Reason for approval"]
                        (deprecated-agent-option "Agent name")]
              :requires-id true}

   "reject" {:description "Vote to reject a proposal"
             :usage "af reject <parent-id> --session TOKEN [--reason TEXT]"
             :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                       ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                       ["-R" "--reason TEXT" "Reason for rejection"]
                       (deprecated-agent-option "Agent name")]
             :requires-id true}

   "vote" {:description "Cast verification vote"
           :usage "af vote <id> --session TOKEN --for|--against [--reason TEXT] [--propagate]"
           :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                     ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                     [nil "--for" "Vote for (valid)"]
                     [nil "--against" "Vote against (invalid)"]
                     ["-R" "--reason TEXT" "Reason for vote"]
                     [nil "--propagate" "Auto-vote on parents when all siblings verified"]
                     (deprecated-agent-option "Agent name")]
           :requires-id true}

   "vote-all" {:description "Batch vote on multiple motes"
               :usage "af vote-all --session TOKEN --for|--against [--reason TEXT]"
               :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                         ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                         [nil "--for" "Vote for (valid)"]
                         [nil "--against" "Vote against (invalid)"]
                         ["-R" "--reason TEXT" "Reason for all votes"]
                         [nil "--pending" "Only vote on motes needing verification (default)"]
                         [nil "--dry-run" "Show what would be voted on without voting"]
                         (deprecated-agent-option "Agent name")]}

   "approve-all" {:description "Approve all pending proposals in session scope"
                  :usage "af approve-all --session TOKEN [--reason TEXT]"
                  :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                            ["-n" "--name NAME" "Agent name (defaults to session agent)"]
                            ["-R" "--reason TEXT" "Reason for all approvals"]
                            [nil "--dry-run" "Show what would be approved without approving"]
                            (deprecated-agent-option "Agent name")]}

   "update" {:description "Update mote fields"
             :usage "af update <id> --session TOKEN [OPTIONS]"
             :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                       [nil "--status STATUS" "New status"
                        :parse-fn keyword]
                       ["-p" "--priority P" "New priority"
                        :parse-fn keyword]
                       ["-d" "--difficulty N" "New difficulty"
                        :parse-fn #(Integer/parseInt %)]
                       ["-c" "--claim TEXT" "New claim text"]]
             :requires-id true}

   "taint" {:description "Add/remove taint flags"
            :usage "af taint <id> --session TOKEN --add TAINT | --remove TAINT"
            :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                      [nil "--add TAINT" "Add taint flag"
                       :parse-fn keyword
                       :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                      [nil "--remove TAINT" "Remove taint flag"
                       :parse-fn keyword
                       :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]]
            :requires-id true}

   "claim" {:description "Claim mote for work"
            :usage "af claim <id> --name NAME --role ROLE"
            :options [["-n" "--name NAME" "Agent name (required)"
                       :missing "Agent name is required"]
                      ["-r" "--role ROLE" "Role for this session (required)"
                       :parse-fn keyword
                       :validate [#{:proposer :advisor :prover :verifier :ref-checker :counterexample}
                                  "Invalid role"]
                       :missing "Role is required"]
                      (deprecated-agent-option "Agent name")]
            :requires-id true}

   "unclaim" {:description "Release claim on mote"
              :usage "af unclaim <id> --session TOKEN"
              :options [["-s" "--session TOKEN" "Session token (required for mutations)"]]
              :requires-id true}

   "done" {:description "End session and release mote"
           :usage "af done --session TOKEN"
           :options [["-s" "--session TOKEN" "Session token (required)"
                      :missing "Session token is required"]]}

   "add-ref" {:description "Add external reference"
              :usage "af add-ref <id> --session TOKEN --ref CITATION [--note TEXT]"
              :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                        ["-r" "--ref REF" "Citation/reference (required)"
                         :missing "Reference is required"]
                        ["-n" "--note TEXT" "Note about reference"]]
              :requires-id true}

   "add-assumption" {:description "Add internal assumption"
                     :usage "af add-assumption <id> --session TOKEN --ref MOTE-ID [--note TEXT]"
                     :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                               ["-r" "--ref ID" "Referenced mote ID (required)"
                                :missing "Reference mote ID is required"]
                               ["-n" "--note TEXT" "Note about assumption"]]
                     :requires-id true}

   "add-definition" {:description "Add definition"
                     :usage "af add-definition <id> --session TOKEN --symbol SYM --meaning TEXT"
                     :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                               [nil "--symbol SYM" "Symbol to define (required)"
                                :missing "Symbol is required"]
                               ["-m" "--meaning TEXT" "Meaning of symbol (required)"
                                :missing "Meaning is required"]]
                     :requires-id true}

   "add-dep" {:description "Add dependency link"
              :usage "af add-dep <id> --depends-on MOTE-ID [--reason TEXT] --session TOKEN"
              :options [["-s" "--session TOKEN" "Session token (required for mutations)"]
                        ["-d" "--depends-on ID" "Mote ID that this mote depends on (required)"
                         :missing "Dependency target is required"]
                        ["-r" "--reason TEXT" "Reason for dependency"]]
              :requires-id true}

   "check" {:description "Validate DAG integrity"
            :usage "af check"
            :options []}

   "repair" {:description "Detect and repair DAG inconsistencies"
             :usage "af repair [--dry-run | --auto]"
             :options [[nil "--dry-run" "Show what would be fixed without fixing"]
                       [nil "--auto" "Automatically fix all repairable issues"]]}

   "log" {:description "Show git history for mote"
          :usage "af log <id> [--limit N]"
          :options [["-l" "--limit N" "Max entries to show"
                     :default 10
                     :parse-fn #(Integer/parseInt %)]]
          :requires-id true}

   "sync" {:description "Pull, commit, push"
           :usage "af sync"
           :options []}

   "config" {:description "Manage project configuration"
             :usage "af config <list|get|set> [key] [value]"
             :options []
             :optional-id true}

   "withdraw" {:description "Withdraw own proposal"
               :usage "af withdraw <parent-id> --session TOKEN"
               :options [["-s" "--session TOKEN" "Session token (required)"
                          :missing "Session token is required"]]
               :requires-id true}

   "tree" {:description "Display mote tree"
           :usage "af tree <id> [--depth N]"
           :options [["-d" "--depth N" "Maximum depth to display"
                      :parse-fn #(Integer/parseInt %)
                      :validate [pos? "Must be positive"]]]
           :requires-id true}

   "status" {:description "Display project status summary"
             :usage "af status"
             :options []}

   "roles" {:description "Show available roles and their descriptions"
            :usage "af roles"
            :options []}

   "workflow" {:description "Display the proof workflow steps"
               :usage "af workflow"
               :options []}

   "sessions" {:description "List all active sessions"
               :usage "af sessions [--details]"
               :options [[nil "--details" "Show additional session details"]]}

   "help" {:description "Show help"
           :usage "af help [command]"
           :options []}})

;; -----------------------------------------------------------------------------
;; Command-Action Mapping (for middleware enforcement)
;; -----------------------------------------------------------------------------

(def command-actions
  "Maps commands to their session enforcement requirements.

   Each entry defines:
   - :action - The permission action to check (e.g., :propose, :vote)
   - :validate-only - If true, use validate-session! instead of enforce-session!
                      (lighter check, no role permission verification)
   - :dynamic-action - Function (options -> action) for commands where action
                       depends on options (e.g., taint --add vs --remove)

   Commands not in this map don't require session enforcement.

   This metadata enables middleware-based enforcement (pull-based) instead of
   requiring each handler to call enforce-session! manually (push-based)."
  {"propose"        {:action :propose}
   "approve"        {:action :approve}
   "reject"         {:action :reject}
   "vote"           {:action :vote}
   "vote-all"       {:action :vote}
   "approve-all"    {:action :approve}
   "taint"          {:dynamic-action
                     (fn [options]
                       (cond
                         (seq (:add options)) :taint-add
                         (seq (:remove options)) :taint-remove
                         :else :taint-add))}  ; default if neither specified
   "add-ref"        {:action :add-ref}
   "add-assumption" {:action :add-assumption}
   "add-definition" {:action :add-definition}
   "add-dep"        {:action :add-dep}
   "unclaim"        {:action :done :validate-only true}
   "done"           {:action :done}
   "withdraw"       {:action :propose}})  ; withdrawing own proposal = proposer action

(defn get-command-action
  "Get the action keyword for a command, resolving dynamic actions if needed.

   Arguments:
   - command: Command name string
   - options: Parsed options map (needed for dynamic actions like 'taint')

   Returns the action keyword, or nil if command doesn't require enforcement."
  [command options]
  (when-let [cmd-meta (get command-actions command)]
    (if-let [dynamic-fn (:dynamic-action cmd-meta)]
      (dynamic-fn options)
      (:action cmd-meta))))

(defn command-requires-session?
  "Check if a command requires session enforcement.

   Arguments:
   - command: Command name string

   Returns true if the command requires a session."
  [command]
  (contains? command-actions command))

(defn command-validate-only?
  "Check if a command uses validate-only mode (no role permission check).

   Arguments:
   - command: Command name string

   Returns true if the command should use validate-session! instead of enforce-session!."
  [command]
  (get-in command-actions [command :validate-only] false))

;; -----------------------------------------------------------------------------
;; Command Aliases
;; -----------------------------------------------------------------------------

(def command-aliases
  "Map of alias names to their target commands.
   Some aliases also inject additional arguments.

   Simple aliases just map to another command name.
   Complex aliases are maps with :command and :inject-args keys."
  {"list"      {:command "status"}
   "verify"    {:command "vote" :inject-args ["--for"]}
   "refute"    {:command "vote" :inject-args ["--against"]}
   "decompose" {:command "propose"}
   "jobs"      {:command "ready" :inject-args ["--no-claim"]}})

(defn resolve-alias
  "Resolve a command alias to its target command and any injected args.

   Arguments:
   - cmd: The command name (might be an alias)
   - args: The remaining arguments

   Returns a map with:
   - :command - The resolved command name
   - :args - The args with any injected args prepended"
  [cmd args]
  (if-let [alias-info (get command-aliases cmd)]
    {:command (:command alias-info)
     :args (concat (:inject-args alias-info) args)}
    {:command cmd
     :args args}))

;; -----------------------------------------------------------------------------
;; Help Generation
;; -----------------------------------------------------------------------------

(def alias-descriptions
  "Human-readable descriptions for command aliases."
  {"list"      "Show project status"
   "verify"    "Shortcut for 'vote --for'"
   "refute"    "Shortcut for 'vote --against'"
   "decompose" "Alternative for 'propose'"
   "jobs"      "List available work"})

(defn generate-help
  "Generate help text for a command or global help."
  ([]
   (str "Alethfeld v" version "\n"
        "CLI tool for collaborative proof verification.\n\n"
        "Usage: af <command> [options]\n\n"
        "Commands:\n"
        (str/join "\n"
                  (for [[name {:keys [description]}] (sort commands)]
                    (format "  %-16s %s" name description)))
        "\n\nAliases:\n"
        (str/join "\n"
                  (for [[alias info] (sort command-aliases)]
                    (format "  %-16s %s (-> %s)"
                            alias
                            (get alias-descriptions alias "")
                            (:command info))))
        "\n\nGlobal options:\n"
        (str/join "\n"
                  (for [[short long desc] global-options]
                    (format "  %s, %-20s %s"
                            (or short "  ")
                            long
                            (or desc ""))))
        "\n\nRun 'af <command> --help' for command-specific help."))
  ([cmd]
   (if-let [{:keys [description usage options]} (get commands cmd)]
     (str description "\n\n"
          "Usage: " usage "\n"
          (when (seq options)
            (str "\nOptions:\n"
                 (:summary (cli/parse-opts [] (concat options global-options))))))
     (str "Unknown command: " cmd "\n\n"
          (generate-help)))))

;; -----------------------------------------------------------------------------
;; Argument Parsing
;; -----------------------------------------------------------------------------

(defn parse-args
  "Parse command line arguments.

   Returns map with:
   - :command - Command name (string)
   - :args - Positional arguments after command
   - :options - Parsed options map
   - :errors - Any parsing errors
   - :help? - True if help was requested
   - :deprecation-warnings - Any deprecation warnings from using old options"
  [args]
  ;; Reset deprecation warnings for this parse
  (reset! *deprecation-warnings* [])
  (let [;; First, separate command from rest
        [raw-cmd & rest-args] args
        raw-cmd (when raw-cmd (str/lower-case raw-cmd))
        ;; Resolve alias to target command (may inject additional args)
        {:keys [command args]} (when raw-cmd (resolve-alias raw-cmd rest-args))
        cmd command
        rest-args (or args rest-args)]
    (cond
      ;; No command - bare invocation (not help)
      (nil? raw-cmd)
      {:command nil
       :args []
       :options {}
       :errors nil
       :help? false
       :bare? true}

      ;; Help command
      (= cmd "help")
      {:command "help"
       :args rest-args
       :options {}
       :errors nil
       :help? true}

      ;; Version flag
      (or (= raw-cmd "-v") (= raw-cmd "--version"))
      {:command nil
       :args []
       :options {:version true}
       :errors nil
       :help? false}

      ;; Help flag
      (or (= raw-cmd "-h") (= raw-cmd "--help"))
      {:command nil
       :args []
       :options {:help true}
       :errors nil
       :help? true}

      ;; Unknown command - with typo suggestion (check both commands and aliases)
      (and (not (contains? commands cmd))
           (not (contains? command-aliases raw-cmd)))
      (let [all-names (concat (keys commands) (keys command-aliases))
            suggestion (suggest-command raw-cmd all-names)
            error-msg (if suggestion
                        (str "Unknown command: " raw-cmd "\n\n"
                             "Did you mean: " suggestion "?\n"
                             "  af " suggestion
                             (when (seq rest-args)
                               (str " " (str/join " " rest-args))))
                        (str "Unknown command: " raw-cmd))]
        {:command raw-cmd
         :args rest-args
         :options {}
         :errors [error-msg]
         :help? false
         :suggestion suggestion})

      ;; Valid command - parse options
      :else
      (let [cmd-opts (get-in commands [cmd :options] [])
            all-opts (concat cmd-opts global-options)
            {:keys [options arguments errors summary]} (cli/parse-opts rest-args all-opts)
            requires-id (get-in commands [cmd :requires-id])
            optional-id (get-in commands [cmd :optional-id])
            has-id-arg (or requires-id optional-id)
            id (when has-id-arg (first arguments))
            rest-args (if has-id-arg (rest arguments) arguments)
            ;; Apply AF_NAME (or legacy AF_AGENT) as default for --name if not provided
            options (if (and (nil? (:name options)) (get-default-name))
                      (assoc options :name (get-default-name))
                      options)
            ;; Apply AF_SESSION as default for --session if not provided
            options (if (and (nil? (:session options)) (get-default-session))
                      (assoc options :session (get-default-session))
                      options)
            ;; Auto-infer session if still not provided and agent has exactly one session
            ;; Priority: 1. --session flag, 2. AF_SESSION env, 3. auto-inference
            _ (reset! *session-inference-message* nil)
            options (try-auto-infer-session options)]
        {:command cmd
         :id id
         :args rest-args
         :options options
         :errors (cond-> errors
                   (and requires-id (nil? id) (not (:help options)))
                   (conj (str "Command '" cmd "' requires an ID argument")))
         :help? (:help options)
         :summary summary
         :deprecation-warnings @*deprecation-warnings*
         :session-inference @*session-inference-message*}))))

;; -----------------------------------------------------------------------------
;; Bare Command Output
;; -----------------------------------------------------------------------------

(defn- format-bare-output
  "Generate the bare command output showing project context and next action.
   This is shown when `af` is invoked with no arguments."
  []
  (let [repo-path "."
        initialized? (store/repo-exists? repo-path)]
    (if initialized?
      ;; Project is initialized - show status
      (let [config (store/load-config repo-path)
            project-name (:project-name config "Unnamed Project")
            motes (store/load-all-motes repo-path)
            mote-list (vals motes)
            total (count mote-list)
            verified (count (filter #(= :verified (:status %)) mote-list))
            fixed (count (filter #(= :fixed (:status %)) mote-list))
            proposed (count (filter #(= :proposed (:status %)) mote-list))]
        (str "Alethfeld v" version " - Collaborative Proof Verification\n"
             "\n"
             "Project: " project-name "\n"
             "Motes: " total
             (when (pos? total)
               (str " (" verified " verified, " fixed " need work, " proposed " proposed)"))
             "\n"
             "\n"
             "Your next action:\n"
             "  af ready --name <you>      Get assigned a task with instructions\n"
             "\n"
             "Quick commands:\n"
             "  af status                  View proof progress\n"
             "  af tree 1                  View proof structure from mote 1\n"
             "  af help                    Full command reference\n"
             "\n"
             "Roles: " (str/join ", " util/valid-role-names)))
      ;; Not initialized - suggest init
      (str "Alethfeld v" version " - Collaborative Proof Verification\n"
           "\n"
           "No project found in current directory.\n"
           "\n"
           "Your next action:\n"
           "  af init --name \"My Proof\"   Initialize a new proof project\n"
           "\n"
           "Or navigate to an existing Alethfeld project directory.\n"
           "\n"
           "Roles: " (str/join ", " util/valid-role-names)))))

;; -----------------------------------------------------------------------------
;; Roles Command
;; -----------------------------------------------------------------------------

(def role-descriptions
  "Descriptions of each agent role."
  {"proposer"      "Break claims into sub-claims (decomposition)"
   "advisor"       "Review and approve/reject proposals"
   "prover"        "Add references and refine claim justifications"
   "verifier"      "Vote on whether claims are valid"
   "ref-checker"   "Validate external references and citations"
   "counterexample" "Find flaws, counterexamples, and edge cases"})

(defn- format-roles-output
  "Generate the roles command output showing all roles and descriptions."
  []
  (str "Alethfeld Agent Roles\n"
       "=====================\n"
       "\n"
       (str/join "\n\n"
                 (for [role util/valid-role-names]
                   (str "  " role "\n"
                        "    " (get role-descriptions role "No description"))))
       "\n\n"
       "Get assigned work:\n"
       "  af ready --name <you>      Claim a job matching your capabilities\n"
       "  af jobs                    List available work without claiming"))

;; -----------------------------------------------------------------------------
;; Command Dispatch
;; -----------------------------------------------------------------------------

(def ^:private handlers
  "Registry of command handlers. Populated by register-handler!"
  (atom {}))

(defn register-handler!
  "Register a handler function for a command.

   Arguments:
   - cmd: Command name (string)
   - handler-fn: Function taking (id, options, format) and returning result"
  [cmd handler-fn]
  (swap! handlers assoc cmd handler-fn))

(defn dispatch
  "Dispatch to the appropriate command handler.

   Arguments:
   - parsed: Result from parse-args

   Returns the result of the handler, or handles help/errors."
  [{:keys [command id args options errors help? bare?] :as parsed}]
  (cond
    ;; Errors
    (seq errors)
    {:error true
     :messages errors
     :exit-code :invalid-args}

    ;; Version
    (:version options)
    {:output (str "Alethfeld v" version)
     :exit-code :success}

    ;; Bare invocation - show context and next action
    bare?
    {:output (format-bare-output)
     :exit-code :success}

    ;; Help
    help?
    {:output (cond
               ;; "af help <cmd>" - show help for specific command
               (and (= command "help") (seq args))
               (generate-help (first args))

               ;; "af help" (no args) or "af --help" - show global help
               (or (= command "help") (nil? command))
               (generate-help)

               ;; "af <cmd> --help" - show help for that command
               :else
               (generate-help command))
     :exit-code :success}

    ;; Roles command (handled directly in cli.clj)
    (= command "roles")
    {:output (format-roles-output)
     :exit-code :success}

    ;; No handler registered
    (not (contains? @handlers command))
    {:error true
     :messages [(str "Command '" command "' is not yet implemented")]
     :exit-code :error}

    ;; Dispatch to handler
    :else
    (try
      (let [handler (get @handlers command)
            context {:id id
                     :args args
                     :options options
                     :command command}
            ;; Apply session enforcement middleware if command requires it
            ;; The middleware validates the session BEFORE the handler runs
            wrapped-handler (if (command-requires-session? command)
                              (let [action (get-command-action command options)
                                    validate-only? (command-validate-only? command)]
                                (middleware/wrap-session-enforcement
                                 handler action
                                 :validate-only validate-only?
                                 :repo-path "."))
                              handler)
            result (wrapped-handler context)]
        {:result result
         :exit-code :success})
      (catch clojure.lang.ExceptionInfo e
        {:error true
         :exception e
         :exit-code (err/error-type->exit-code (:type (ex-data e)))}))))

;; -----------------------------------------------------------------------------
;; Main Entry Point
;; -----------------------------------------------------------------------------

(defn run
  "Run the CLI with given arguments.

   Arguments:
   - args: Command line arguments (vector of strings)

   Options:
   - :exit? - Whether to call exit! (default true in production)

   Returns map with :exit-code and :output or :error."
  [args & {:keys [exit?] :or {exit? true}}]
  (let [parsed (parse-args args)
        {:keys [options deprecation-warnings session-inference]} parsed
        fmt (:format options :text)
        verbose (:verbose options false)
        ;; Check if session inference resulted in a multiple-sessions error
        inference-error? (and (map? session-inference) (:error session-inference))
        result (if inference-error?
                 ;; Return error result for multiple sessions
                 {:error true
                  :messages [(format-multiple-sessions-error session-inference)]
                  :exit-code :invalid-args}
                 (dispatch parsed))]
    ;; Print deprecation warnings to stderr
    (when (and exit? (seq deprecation-warnings))
      (doseq [warning deprecation-warnings]
        (binding [*out* *err*]
          (println warning))))
    ;; Print session auto-inference message to stderr (when it's just a message, not an error)
    (when (and exit? (string? session-inference))
      (binding [*out* *err*]
        (println session-inference)))
    (cond
      ;; Error with messages
      (:messages result)
      (do
        (when exit?
          (doseq [msg (:messages result)]
            (binding [*out* *err*]
              (println msg)))
          (when-not (= (:exit-code result) :success)
            (binding [*out* *err*]
              (println)
              (println (generate-help (:command parsed)))))
          (exit! (:exit-code result)))
        result)

      ;; Error with exception
      (:exception result)
      (do
        (when exit?
          (handle-error (:exception result) fmt verbose))
        result)

      ;; Plain output (help, version)
      (:output result)
      (do
        (when exit?
          (println (:output result))
          (exit! :success))
        result)

      ;; Success with result data
      (:result result)
      (do
        (when exit?
          (println (format-output (:result result) fmt))
          (exit! :success))
        result)

      ;; Unexpected
      :else
      (do
        (when exit?
          (exit! :error "Unexpected error"))
        {:error true :exit-code :error}))))

(defn -main
  "CLI entry point for Alethfeld."
  [& args]
  (ensure-handlers!)
  (run (vec args) :exit? true))
