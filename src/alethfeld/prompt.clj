(ns alethfeld.prompt
  "Prompt templates and rendering for agent roles.

   Templates can be loaded from external files in prompts/ directory:
   - prompts/roles.edn - Role definitions and descriptions
   - prompts/<role>.md - Role-specific prompt templates (proposer.md, etc.)
   - prompts/session-context.md - Session context block template

   Uses mustache-style {{placeholder}} interpolation.
   Falls back to embedded templates if external files are missing."
  (:require [alethfeld.session :as session]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Format Helpers
;; -----------------------------------------------------------------------------

(defn format-assumptions
  "Format a vector of assumptions as readable text.

   Each assumption is either:
   - {:type :internal :ref <mote-id> :note <optional>}
   - {:type :external :ref <citation> :note <optional>}

   Returns a string, or \"(none)\" if empty."
  [assumptions]
  (if (seq assumptions)
    (->> assumptions
         (map (fn [{:keys [type ref note]}]
                (if note
                  (str "- [" (name type) "] " ref ": " note)
                  (str "- [" (name type) "] " ref))))
         (str/join "\n"))
    "(none)"))

(defn format-definitions
  "Format a vector of definitions as readable text.

   Each definition is {:symbol <string> :meaning <string>}.

   Returns a string, or \"(none)\" if empty."
  [definitions]
  (if (seq definitions)
    (->> definitions
         (map (fn [{:keys [symbol meaning]}]
                (str "- " symbol ": " meaning)))
         (str/join "\n"))
    "(none)"))

(defn format-vote-summary
  "Format a vector of votes as a summary string.

   Each vote is {:agent <string> :vote <:for|:against> :reason <optional>}.

   Returns a summary like \"2 for, 1 against\" or \"(no votes)\"."
  [votes]
  (if (seq votes)
    (let [for-count (count (filter #(= :for (:vote %)) votes))
          against-count (count (filter #(= :against (:vote %)) votes))]
      (str for-count " for, " against-count " against"))
    "(no votes)"))

(defn- format-proposal-vote-summary
  "Format proposal votes as a summary string.

   Returns a summary like \"2 approve, 1 reject\" or \"(no votes)\"."
  [votes]
  (if (seq votes)
    (let [approve-count (count (filter #(= :approve (:vote %)) votes))
          reject-count (count (filter #(= :reject (:vote %)) votes))]
      (str approve-count " approve, " reject-count " reject"))
    "(no votes)"))

(defn- format-children
  "Format children list for display.

   Expects a vector of mote maps (resolved children, not just IDs).
   Returns formatted string or \"(none)\"."
  [children]
  (if (seq children)
    (->> children
         (map (fn [{:keys [id claim status]}]
                (str "- " id ": " claim " [" (name status) "]")))
         (str/join "\n"))
    "(none)"))

(defn- format-proposed-children
  "Format proposed children with numbering.

   Expects a vector of mote maps (or strings as fallback for IDs).
   Returns formatted numbered list."
  [children]
  (if (seq children)
    (->> children
         (map-indexed (fn [i child]
                        (if (map? child)
                          ;; Full mote map - show all details
                          (let [{:keys [id claim difficulty]} child]
                            (str (inc i) ". " id ": " claim " (difficulty " difficulty ")"))
                          ;; String ID only - show degraded format
                          (str (inc i) ". " child " (details not loaded)"))))
         (str/join "\n"))
    "(none)"))

(defn- format-external-refs
  "Format only external references from assumptions.
   Returns formatted string or \"(none)\"."
  [assumptions]
  (let [external (filter #(= :external (:type %)) assumptions)]
    (if (seq external)
      (->> external
           (map (fn [{:keys [ref note]}]
                  (if note
                    (str "- " ref ": \"" note "\"")
                    (str "- " ref))))
           (str/join "\n"))
      "(none)")))

;; -----------------------------------------------------------------------------
;; External Template Loading
;; -----------------------------------------------------------------------------

(def ^:private prompts-dir
  "Directory containing external prompt templates.
   Resolved relative to classpath or filesystem."
  "prompts")

(defn- find-prompts-dir
  "Find the prompts directory. Checks:
   1. Current working directory + /prompts
   2. Classpath resource prompts/

   Returns a File or nil if not found."
  []
  (let [cwd-prompts (io/file prompts-dir)]
    (when (.isDirectory cwd-prompts)
      cwd-prompts)))

(defn- load-template-file
  "Load a template file from the prompts directory.

   Arguments:
   - filename: Name of the file (e.g., 'verifier.md')

   Returns the file contents as a string, or nil if not found."
  [filename]
  (when-let [dir (find-prompts-dir)]
    (let [file (io/file dir filename)]
      (when (.exists file)
        (slurp file)))))

(defn- load-roles-edn
  "Load the roles.edn file containing role definitions.

   Returns a map of role -> {:description :long-description :actions}
   or nil if file not found."
  []
  (when-let [content (load-template-file "roles.edn")]
    (try
      (edn/read-string content)
      (catch Exception _ nil))))

(defn- interpolate-template
  "Replace {{placeholder}} patterns in template with values from context.

   Arguments:
   - template: String containing {{key}} placeholders
   - context: Map of keyword -> value

   Returns the interpolated string."
  [template context]
  (reduce-kv
   (fn [s k v]
     (str/replace s (str "{{" (name k) "}}") (str v)))
   template
   context))

;; Cache for loaded templates (reset on each call to support hot-reloading)
(def ^:private external-templates-cache (atom nil))

(defn- load-external-role-template
  "Load an external role template file.

   Arguments:
   - role: Role keyword (e.g., :verifier)

   Returns the template content string, or nil if not found."
  [role]
  (load-template-file (str (name role) ".md")))

(defn- load-session-context-template
  "Load the session context template file.

   Returns the template content string, or nil if not found."
  []
  (load-template-file "session-context.md"))

(defn get-role-definitions
  "Get role definitions from external file or embedded fallback.

   Returns a map of role -> {:description :long-description :actions}."
  []
  (or (load-roles-edn)
      ;; Fallback to embedded definitions
      {:proposer
       {:description "Break claims into sub-claims"
        :long-description "Decompose motes into 2-5 substeps that together prove the claim."
        :actions #{:propose :add-definition :add-assumption :add-ref :done}}
       :advisor
       {:description "Review and approve/reject proposals"
        :long-description "Evaluate proposed decompositions for completeness and mutual exclusivity."
        :actions #{:approve :reject :done}}
       :prover
       {:description "Add references and refine claims"
        :long-description "Add missing assumptions, external references, and definitions."
        :actions #{:propose :add-definition :add-assumption :add-ref :taint-remove :done}}
       :verifier
       {:description "Vote on claim validity"
        :long-description "Validate that substeps logically entail claims. Vote for or against."
        :actions #{:vote :taint-add :done}}
       :ref-checker
       {:description "Validate external references"
        :long-description "Verify external references exist and support claims as stated."
        :actions #{:add-ref :taint-remove :done}}
       :counterexample
       {:description "Find flaws and counterexamples"
        :long-description "Construct counterexamples and find edge cases where claims fail."
        :actions #{:vote :update-status :done}}}))

;; -----------------------------------------------------------------------------
;; Session Context Formatting
;; -----------------------------------------------------------------------------

(def ^:private action->command-name
  "Map action keywords to command names."
  {:propose "propose"
   :add-definition "add-definition"
   :add-assumption "add-assumption"
   :add-ref "add-ref"
   :approve "approve"
   :reject "reject"
   :vote "vote"
   :taint-add "taint --add <tag>"
   :taint-remove "taint --remove <tag>"
   :update-status "update --status <status>"
   :done "done"})

(def ^:private action->description
  "Human-readable descriptions for actions."
  {:propose "create proposals"
   :add-definition "add definitions"
   :add-assumption "add assumptions"
   :add-ref "add references"
   :approve "approve proposals"
   :reject "reject proposals"
   :vote "cast votes"
   :taint-add "add taints"
   :taint-remove "remove taints"
   :update-status "update status"
   :done "end session"})

(defn- format-allowed-commands
  "Format allowed commands for a role with session context.

   Arguments:
   - role: The session role keyword
   - mote-id: The mote ID
   - session-id: The session ID

   Returns a formatted string of allowed commands."
  [role mote-id session-id]
  (let [allowed-actions (session/get-allowed-actions role)
        ;; Exclude :done from the list (shown separately)
        command-actions (disj allowed-actions :done)]
    (if (seq command-actions)
      (->> command-actions
           (map (fn [action]
                  (let [cmd-name (get action->command-name action (name action))]
                    (str "  af " cmd-name " " mote-id " ... --session " session-id))))
           (str/join "\n"))
      "  (none)")))

(defn- format-forbidden-actions
  "Format forbidden actions for a role.

   Arguments:
   - role: The session role keyword

   Returns a formatted string of forbidden actions with which roles can do them."
  [role]
  (let [allowed (session/get-allowed-actions role)
        ;; All possible mutation actions (excluding :done which everyone has)
        all-actions #{:propose :add-definition :add-assumption :add-ref
                      :approve :reject :vote :taint-add :taint-remove :update-status}
        forbidden (set/difference all-actions allowed)]
    (if (seq forbidden)
      (->> forbidden
           (map (fn [action]
                  (let [roles-for-action (session/get-roles-for-action action)
                        role-names (str/join ", " (map name roles-for-action))
                        description (get action->description action (name action))]
                    (str "  - " description " (" role-names " only)"))))
           (str/join "\n"))
      "  (none)")))

(defn- render-session-context
  "Render session context block for a prompt.

   Arguments:
   - session: Session map with :session-id, :mote-id, :role
   - mote-id: The mote ID

   Returns a formatted session context string."
  [session mote-id]
  (let [session-id (:session-id session)
        role (:role session)]
    (str "═══════════════════════════════════════════════════════════════════════════════\n"
         "SESSION CONTEXT\n"
         "═══════════════════════════════════════════════════════════════════════════════\n"
         "\n"
         "SESSION: " session-id "\n"
         "MOTE: " mote-id "\n"
         "ROLE: " (name role) "\n"
         "\n"
         "ALLOWED COMMANDS:\n"
         (format-allowed-commands role mote-id session-id) "\n"
         "\n"
         "FORBIDDEN (your role cannot):\n"
         (format-forbidden-actions role) "\n"
         "\n"
         "When finished: af done --session " session-id "\n"
         "═══════════════════════════════════════════════════════════════════════════════")))

;; -----------------------------------------------------------------------------
;; Prompt Templates (Data-Driven)
;; -----------------------------------------------------------------------------

(def ^:private role-templates
  "Prompt templates for each role.

   Templates use keyword placeholders that get replaced by render-prompt.
   Available placeholders:
   - :mote-id, :claim, :priority, :difficulty, :status
   - :parent-info (formatted parent line)
   - :children (formatted children list)
   - :proposed-children (formatted proposed children with numbers)
   - :assumptions (formatted assumptions)
   - :definitions (formatted definitions)
   - :vote-summary (formatted vote summary)
   - :proposal-vote-summary (formatted proposal vote summary)
   - :external-refs (formatted external references only)
   - :proposed-by (proposal author)"
  {:proposer
   {:header "You are a PROPOSER agent. Your task is to DECOMPOSE this mote into substeps."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "PRIORITY" :key :priority}
     {:label "DIFFICULTY" :key :difficulty}
     {:label "PARENT" :key :parent-info}
     {:label "ASSUMPTIONS" :key :assumptions :block true}]
    :task
    "TASK:
1. Decompose into 2-5 substeps that TOGETHER prove the claim
2. Substeps must be mutually exclusive and collectively exhaustive
3. Each substep must be independently verifiable
4. Assign difficulty (1-5) to each substep"
    :commands
    "COMMAND:
af propose {{mote-id}} \\
  --claim \"<substep 1>\" --difficulty <n> \\
  --claim \"<substep 2>\" --difficulty <n> \\
  ... \\
  --agent <your-name>

When done: af unclaim {{mote-id}}"}

   :advisor
   {:header "You are an ADVISOR agent. Your task is to EVALUATE a proposed decomposition."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "PROPOSED CHILDREN" :key :proposed-children :block true}
     {:label "PROPOSED BY" :key :proposed-by}
     {:label "VOTES" :key :proposal-vote-summary}]
    :task
    "EVALUATE:
1. Do substeps together imply the claim? (completeness)
2. Any gaps or missing cases? (exhaustiveness)
3. Any overlap between substeps? (mutual exclusivity)
4. Appropriate difficulty ratings?"
    :commands
    "COMMANDS:
af approve {{mote-id}} --agent <your-name> --reason \"<why>\"
af reject {{mote-id}} --agent <your-name> --reason \"<flaw>\"

When done: af unclaim {{mote-id}}"}

   :prover
   {:header "You are a PROVER agent. Your task is to REFINE this mote."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "PRIORITY" :key :priority}
     {:label "DIFFICULTY" :key :difficulty}
     {:label "CHILDREN" :key :children :block true :suffix "(none — may need decomposition first)"}
     {:label "ASSUMPTIONS" :key :assumptions :block true}]
    :task
    "TASK:
1. Add missing assumptions (internal refs to other motes)
2. Add external references (citations)
3. Add definitions for symbols used
4. Ensure claim is precisely stated"
    :commands
    "COMMANDS:
af add-assumption {{mote-id}} --ref <mote-id> --note \"<why>\"
af add-ref {{mote-id}} --ref \"<citation>\" --note \"<what it provides>\"
af add-definition {{mote-id}} --symbol \"<sym>\" --meaning \"<meaning>\"
af taint {{mote-id}} --remove needs-refinement
af taint {{mote-id}} --add needs-verification

When done: af unclaim {{mote-id}}"}

   :verifier
   {:header "You are a VERIFIER agent. Your task is to VALIDATE this mote."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "PRIORITY" :key :priority}
     {:label "DIFFICULTY" :key :difficulty}
     {:label "CHILDREN (substeps)" :key :children :block true}
     {:label "ASSUMPTIONS" :key :assumptions :block true}
     {:label "DEFINITIONS" :key :definitions :block true}
     {:label "VOTES SO FAR" :key :vote-summary}]
    :task
    "TASK:
1. Check if substeps logically entail the claim
2. Verify all assumptions are justified
3. Look for gaps, errors, unjustified leaps
4. Cast your vote with reasoning"
    :commands
    "COMMANDS:
af vote {{mote-id}} --for --agent <your-name> --reason \"<why valid>\"
af vote {{mote-id}} --against --agent <your-name> --reason \"<flaw>\"
af taint {{mote-id}} --add needs-counterexample  (if suspicious)
af taint {{mote-id}} --add needs-refinement      (if incomplete)

When done: af unclaim {{mote-id}}"}

   :ref-checker
   {:header "You are a REF-CHECKER agent. Your task is to VALIDATE external references."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "EXTERNAL REFERENCES" :key :external-refs :block true}]
    :task
    "TASK:
1. Verify each reference exists
2. Confirm cited result supports the claim as stated
3. Flag misquotations or misattributions
4. Note preprint vs peer-reviewed status"
    :commands
    "COMMANDS:
af add-ref {{mote-id}} --ref \"<corrected>\" --note \"<update>\"  (to fix)
af taint {{mote-id}} --remove needs-refs                      (when done)

When done: af unclaim {{mote-id}}"}

   :counterexample
   {:header "You are a COUNTEREXAMPLE agent. Your task is to FIND FLAWS."
    :sections
    [{:label "MOTE" :key :mote-id}
     {:label "CLAIM" :key :claim}
     {:label "ASSUMPTIONS" :key :assumptions :block true}
     {:label "DEFINITIONS" :key :definitions :block true}]
    :task
    "TASK:
1. Construct counterexamples
2. Find edge cases where claim fails
3. Check boundary conditions
4. Verify claim isn't vacuously true"
    :commands
    "IF COUNTEREXAMPLE FOUND:
af update {{mote-id}} --status refuted
af vote {{mote-id}} --against --agent <your-name> --reason \"Counterexample: <desc>\"

IF CLAIM SURVIVES:
af taint {{mote-id}} --remove needs-counterexample
af vote {{mote-id}} --for --agent <your-name> --reason \"No counterexample found\"

When done: af unclaim {{mote-id}}"}})

;; -----------------------------------------------------------------------------
;; Context Building
;; -----------------------------------------------------------------------------

(defn- build-context
  "Build the context map for template rendering from a job.

   Job contains:
   - :mote - the target mote
   - :parent - parent mote (or nil)
   - :siblings - sibling motes (vec)

   Also accepts optional resolved-children for proposal children.
   When resolved-children is not provided but the mote has a proposal,
   falls back to showing proposal child IDs (degraded format)."
  [job & {:keys [resolved-children]}]
  (let [mote (:mote job)
        parent (:parent job)
        proposal (:proposal mote)
        ;; For children (verifier view), use resolved or empty
        children (or resolved-children [])
        ;; For proposed-children (advisor view), prefer resolved but fall back to IDs
        proposed-children (if (seq resolved-children)
                            resolved-children
                            (when proposal (:children proposal)))]
    {:mote-id (:id mote)
     :claim (:claim mote)
     :priority (name (:priority mote))
     :difficulty (:difficulty mote)
     :status (name (:status mote))
     :parent-info (if parent
                    (str (:id parent) " — " (:claim parent))
                    "(root)")
     :children (format-children children)
     :proposed-children (format-proposed-children proposed-children)
     :assumptions (format-assumptions (:assumptions mote))
     :definitions (format-definitions (:definitions mote))
     :vote-summary (format-vote-summary (:votes mote))
     :proposal-vote-summary (when proposal
                              (format-proposal-vote-summary (:votes proposal)))
     :external-refs (format-external-refs (:assumptions mote))
     :proposed-by (when proposal (:proposed-by proposal))}))

;; -----------------------------------------------------------------------------
;; Template Rendering
;; -----------------------------------------------------------------------------

(defn- render-section
  "Render a single template section.

   Section format:
   {:label \"LABEL\" :key :context-key :block true/false :suffix \"alt text\"}

   If :block is true, value goes on next line with blank line after."
  [section context]
  (let [{:keys [label key block]} section
        value (get context key)]
    (if block
      (str label ":\n" value)
      (str label ": " value))))

(defn- substitute-mote-id
  "Replace {{mote-id}} placeholders in command text."
  [text mote-id]
  (str/replace text "{{mote-id}}" mote-id))

(defn- render-prompt-from-external
  "Render a prompt using external template file.

   Arguments:
   - role: Role keyword
   - context: Context map with all placeholder values
   - session: Optional session map

   Returns interpolated prompt string, or nil if external template not found."
  [role context session]
  (when-let [template (load-external-role-template role)]
    (let [mote-id (:mote-id context)
          session-id (when session (:session-id session))
          ;; Build full context for interpolation
          full-context (cond-> context
                         session-id (assoc :session-id session-id
                                           :role (name role)
                                           :allowed-commands (format-allowed-commands role mote-id session-id)
                                           :forbidden-actions (format-forbidden-actions role)))
          ;; Interpolate the template
          rendered (interpolate-template template full-context)
          ;; Handle session context and done command
          with-session-cmd (if session
                             (str/replace rendered
                                          #"When done: af unclaim [^\n]+"
                                          (str "When finished: af done --session " session-id))
                             rendered)]
      ;; Add session context header if session provided
      (if session
        (str (render-session-context session mote-id) "\n\n" with-session-cmd)
        with-session-cmd))))

(defn- render-prompt-from-embedded
  "Render a prompt using embedded template.

   Arguments:
   - role: Role keyword
   - context: Context map with all placeholder values
   - session: Optional session map

   Returns rendered prompt string, or nil if role template not found."
  [role context session]
  (when-let [template (get role-templates role)]
    (let [mote-id (:mote-id context)]
      (str
       ;; Session context (if session provided)
       (when session
         (str (render-session-context session mote-id) "\n\n"))
       ;; Header
       (:header template)
       "\n\n"
       ;; Sections
       (->> (:sections template)
            (map #(render-section % context))
            (str/join "\n\n"))
       "\n\n"
       ;; Task
       (:task template)
       "\n\n"
       ;; Commands (with mote-id substitution)
       (let [base-commands (substitute-mote-id (:commands template) mote-id)]
         (if session
           ;; Replace "When done: af unclaim <mote>" with "When finished: af done --session <session>"
           (str/replace base-commands
                        #"When done: af unclaim [^\n]+"
                        (str "When finished: af done --session " (:session-id session)))
           base-commands))))))

(defn render-prompt
  "Render a complete prompt for a job.

   Arguments:
   - job: Job map containing :role, :mote, :parent, :siblings

   Options:
   - :resolved-children - Vector of resolved child motes (for proposals/verification)
   - :session - Session map (when provided, includes session context block)

   When session is provided, the prompt includes:
   - Session context header with SESSION, MOTE, ROLE
   - ALLOWED COMMANDS with --session flag
   - FORBIDDEN actions list
   - 'af done --session <id>' instead of 'af unclaim'

   Templates are loaded from external files in prompts/ directory first,
   with fallback to embedded templates if files are missing.

   Returns the complete prompt string."
  [job & {:keys [resolved-children session]}]
  (let [role (:role job)
        context (build-context job :resolved-children resolved-children)]
    ;; Try external template first, fall back to embedded
    (or (render-prompt-from-external role context session)
        (render-prompt-from-embedded role context session))))
