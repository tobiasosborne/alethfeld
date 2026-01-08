(ns alethfeld.prompt
  "Prompt templates and rendering for agent roles.")

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
         (clojure.string/join "\n"))
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
         (clojure.string/join "\n"))
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
         (clojure.string/join "\n"))
    "(none)"))

(defn- format-proposed-children
  "Format proposed children with numbering.

   Expects a vector of mote maps.
   Returns formatted numbered list."
  [children]
  (if (seq children)
    (->> children
         (map-indexed (fn [i {:keys [id claim difficulty]}]
                        (str (inc i) ". " id ": " claim " (difficulty " difficulty ")")))
         (clojure.string/join "\n"))
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
           (clojure.string/join "\n"))
      "(none)")))

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

   Also accepts optional resolved-children for proposal children."
  [job & {:keys [resolved-children]}]
  (let [mote (:mote job)
        parent (:parent job)
        proposal (:proposal mote)
        children (or resolved-children [])]
    {:mote-id (:id mote)
     :claim (:claim mote)
     :priority (name (:priority mote))
     :difficulty (:difficulty mote)
     :status (name (:status mote))
     :parent-info (if parent
                    (str (:id parent) " — " (:claim parent))
                    "(root)")
     :children (format-children children)
     :proposed-children (format-proposed-children children)
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
  (clojure.string/replace text "{{mote-id}}" mote-id))

(defn render-prompt
  "Render a complete prompt for a job.

   Arguments:
   - job: Job map containing :role, :mote, :parent, :siblings

   Options:
   - :resolved-children - Vector of resolved child motes (for proposals/verification)

   Returns the complete prompt string."
  [job & {:keys [resolved-children]}]
  (let [role (:role job)
        template (get role-templates role)
        context (build-context job :resolved-children resolved-children)
        mote-id (:mote-id context)]
    (when template
      (str
       ;; Header
       (:header template)
       "\n\n"
       ;; Sections
       (->> (:sections template)
            (map #(render-section % context))
            (clojure.string/join "\n\n"))
       "\n\n"
       ;; Task
       (:task template)
       "\n\n"
       ;; Commands (with mote-id substitution)
       (substitute-mote-id (:commands template) mote-id)))))
