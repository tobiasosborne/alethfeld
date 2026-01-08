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
            [clojure.pprint :as pprint])
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

(def version "0.1.0-SNAPSHOT")

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

(defn format-output
  "Format data according to specified format.

   Arguments:
   - data: The data to format
   - fmt: :edn or :json (default :edn)

   Returns formatted string."
  [data fmt]
  (case fmt
    :json (format-json data)
    :edn (format-edn data)
    (format-edn data)))

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
  "Generate user-friendly error message from exception."
  [ex]
  (let [data (ex-data ex)
        msg (ex-message ex)]
    (case (:type data)
      ;; Repository errors
      :not-initialized
      (str "Error: Not an Alethfeld repository.\n"
           "Run 'af init' to initialize a new repository.")

      :already-initialized
      (str "Error: Repository already initialized.\n"
           "The .alethfeld/ directory already exists.")

      :not-git-repo
      (str "Error: Not a git repository.\n"
           "Run 'git init' first, then 'af init'.")

      ;; Mote errors
      :not-found
      (str "Error: Mote not found: " (:mote-id data) "\n"
           "Run 'af check' to validate repository integrity.")

      :validation-failed
      (str "Error: Validation failed\n"
           (str/join "\n" (map #(str "  - " %) (:errors data))))

      :invalid-status
      (str "Error: Invalid status transition.\n"
           "Current status: " (when (:status data) (name (:status data))) "\n"
           msg)

      ;; Claim errors
      :already-claimed
      (str "Error: Mote " (:mote-id data) " is already claimed by " (:claimed-by data) ".\n"
           "Use 'af unclaim " (:mote-id data) "' first, or use a different mote.")

      ;; Voting errors
      :already-voted
      (str "Error: Agent '" (:agent data) "' has already voted on this mote.\n"
           "Each agent can only vote once.")

      ;; Proposal errors
      :no-proposal
      (str "Error: " msg "\n"
           "Use 'af propose <id> --claim \"...\"' to create a proposal first.")

      :proposal-exists
      (str "Error: A proposal already exists on this mote.\n"
           "Proposal ID: " (:proposal-id data) "\n"
           "Use 'af approve' or 'af reject' to resolve the current proposal first.")

      ;; Git errors
      :git-error
      (str "Error: Git operation failed.\n"
           msg
           (when (:stderr data) (str "\n" (:stderr data))))

      ;; Default
      (str "Error: " msg))))

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
         code (case (:type data)
                :not-found :not-found
                :validation-failed :validation-error
                :invalid-status :error
                :already-voted :conflict
                :already-claimed :conflict
                :no-proposal :error
                :proposal-exists :conflict
                :not-initialized :error
                :already-initialized :error
                :not-git-repo :error
                :git-error :error
                :error)]
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
  [["-f" "--format FORMAT" "Output format (edn or json)"
    :default :edn
    :parse-fn keyword
    :validate [#{:edn :json} "Must be 'edn' or 'json'"]]
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
                       ["-a" "--agent NAME" "Agent name (created-by)"
                        :default "cli-user"]]
             :optional-id true}

   "ready" {:description "Get next job(s) for an agent"
            :usage "af ready [OPTIONS]"
            :options [["-a" "--agent NAME" "Agent name (auto-claims job)"]
                      ["-r" "--role ROLE" "Filter by role"
                       :parse-fn keyword
                       :validate [#{:proposer :advisor :prover :verifier :ref-checker :counterexample}
                                  "Invalid role"]]
                      ["-d" "--difficulty SPEC" "Difficulty filter (N or N-M)"]
                      ["-p" "--priority SPEC" "Priority filter (pN or pN-pM)"]
                      ["-m" "--max N" "Max jobs to return"
                       :default 1
                       :parse-fn #(Integer/parseInt %)
                       :validate [pos? "Must be positive"]]
                      ["-n" "--no-claim" "Don't auto-claim jobs"]]}

   "propose" {:description "Propose decomposition into children"
              :usage "af propose <parent-id> --claim TEXT [--difficulty N] [--claim TEXT ...] --agent NAME"
              :options [["-c" "--claim TEXT" "Claim text (repeatable)"
                         :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                        ["-d" "--difficulty N" "Difficulty for claims (repeatable)"
                         :parse-fn #(Integer/parseInt %)
                         :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                        ["-a" "--agent NAME" "Agent name (required)"
                         :missing "Agent is required"]]
              :requires-id true}

   "approve" {:description "Vote to approve a proposal"
              :usage "af approve <parent-id> --agent NAME [--reason TEXT]"
              :options [["-a" "--agent NAME" "Agent name (required)"
                         :missing "Agent is required"]
                        ["-R" "--reason TEXT" "Reason for approval"]]
              :requires-id true}

   "reject" {:description "Vote to reject a proposal"
             :usage "af reject <parent-id> --agent NAME [--reason TEXT]"
             :options [["-a" "--agent NAME" "Agent name (required)"
                        :missing "Agent is required"]
                       ["-R" "--reason TEXT" "Reason for rejection"]]
             :requires-id true}

   "vote" {:description "Cast verification vote"
           :usage "af vote <id> --for|--against --agent NAME [--reason TEXT]"
           :options [["-a" "--agent NAME" "Agent name (required)"
                      :missing "Agent is required"]
                     [nil "--for" "Vote for (valid)"]
                     [nil "--against" "Vote against (invalid)"]
                     ["-R" "--reason TEXT" "Reason for vote"]]
           :requires-id true}

   "update" {:description "Update mote fields"
             :usage "af update <id> [OPTIONS]"
             :options [["-s" "--status STATUS" "New status"
                        :parse-fn keyword]
                       ["-p" "--priority P" "New priority"
                        :parse-fn keyword]
                       ["-d" "--difficulty N" "New difficulty"
                        :parse-fn #(Integer/parseInt %)]
                       ["-c" "--claim TEXT" "New claim text"]]
             :requires-id true}

   "taint" {:description "Add/remove taint flags"
            :usage "af taint <id> --add TAINT | --remove TAINT"
            :options [[nil "--add TAINT" "Add taint flag"
                       :parse-fn keyword
                       :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]
                      [nil "--remove TAINT" "Remove taint flag"
                       :parse-fn keyword
                       :assoc-fn (fn [m k v] (update m k (fnil conj []) v))]]
            :requires-id true}

   "claim" {:description "Claim mote for work"
            :usage "af claim <id> --agent NAME"
            :options [["-a" "--agent NAME" "Agent name (required)"
                       :missing "Agent is required"]]
            :requires-id true}

   "unclaim" {:description "Release claim on mote"
              :usage "af unclaim <id>"
              :options []
              :requires-id true}

   "add-ref" {:description "Add external reference"
              :usage "af add-ref <id> --ref CITATION [--note TEXT]"
              :options [["-r" "--ref REF" "Citation/reference (required)"
                         :missing "Reference is required"]
                        ["-n" "--note TEXT" "Note about reference"]]
              :requires-id true}

   "add-assumption" {:description "Add internal assumption"
                     :usage "af add-assumption <id> --ref MOTE-ID [--note TEXT]"
                     :options [["-r" "--ref ID" "Referenced mote ID (required)"
                                :missing "Reference mote ID is required"]
                               ["-n" "--note TEXT" "Note about assumption"]]
                     :requires-id true}

   "add-definition" {:description "Add definition"
                     :usage "af add-definition <id> --symbol SYM --meaning TEXT"
                     :options [["-s" "--symbol SYM" "Symbol to define (required)"
                                :missing "Symbol is required"]
                               ["-m" "--meaning TEXT" "Meaning of symbol (required)"
                                :missing "Meaning is required"]]
                     :requires-id true}

   "check" {:description "Validate DAG integrity"
            :usage "af check"
            :options []}

   "log" {:description "Show git history for mote"
          :usage "af log <id> [--limit N]"
          :options [["-l" "--limit N" "Max entries to show"
                     :default 10
                     :parse-fn #(Integer/parseInt %)]]
          :requires-id true}

   "sync" {:description "Pull, commit, push"
           :usage "af sync"
           :options []}

   "help" {:description "Show help"
           :usage "af help [command]"
           :options []}})

;; -----------------------------------------------------------------------------
;; Help Generation
;; -----------------------------------------------------------------------------

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
   - :help? - True if help was requested"
  [args]
  (let [;; First, separate command from rest
        [cmd & rest-args] args
        cmd (when cmd (str/lower-case cmd))]
    (cond
      ;; No command
      (nil? cmd)
      {:command nil
       :args []
       :options {}
       :errors nil
       :help? true}

      ;; Help command
      (= cmd "help")
      {:command "help"
       :args rest-args
       :options {}
       :errors nil
       :help? true}

      ;; Version flag
      (or (= cmd "-v") (= cmd "--version"))
      {:command nil
       :args []
       :options {:version true}
       :errors nil
       :help? false}

      ;; Help flag
      (or (= cmd "-h") (= cmd "--help"))
      {:command nil
       :args []
       :options {:help true}
       :errors nil
       :help? true}

      ;; Unknown command
      (not (contains? commands cmd))
      {:command cmd
       :args rest-args
       :options {}
       :errors [(str "Unknown command: " cmd)]
       :help? false}

      ;; Valid command - parse options
      :else
      (let [cmd-opts (get-in commands [cmd :options] [])
            all-opts (concat cmd-opts global-options)
            {:keys [options arguments errors summary]} (cli/parse-opts rest-args all-opts)
            requires-id (get-in commands [cmd :requires-id])
            optional-id (get-in commands [cmd :optional-id])
            has-id-arg (or requires-id optional-id)
            id (when has-id-arg (first arguments))
            rest-args (if has-id-arg (rest arguments) arguments)]
        {:command cmd
         :id id
         :args rest-args
         :options options
         :errors (cond-> errors
                   (and requires-id (nil? id) (not (:help options)))
                   (conj (str "Command '" cmd "' requires an ID argument")))
         :help? (:help options)
         :summary summary}))))

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
  [{:keys [command id args options errors help?] :as parsed}]
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

    ;; Help
    help?
    {:output (if command
               (generate-help command)
               (generate-help))
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
            result (handler {:id id
                             :args args
                             :options options})]
        {:result result
         :exit-code :success})
      (catch clojure.lang.ExceptionInfo e
        {:error true
         :exception e
         :exit-code (case (:type (ex-data e))
                      :not-found :not-found
                      :validation-failed :validation-error
                      :error)}))))

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
        {:keys [options]} parsed
        fmt (:format options :edn)
        verbose (:verbose options false)
        result (dispatch parsed)]
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
