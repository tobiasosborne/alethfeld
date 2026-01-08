(ns alethfeld.context.templates
  "Context templates for orchestrator phases.

   This namespace provides functions for loading and interpolating
   markdown templates used by the proof verification orchestrator.

   Templates are stored in resources/templates/ and contain interpolation
   markers like <THEOREM_STATEMENT> that get replaced with actual values.

   Phase templates (from orchestrator protocol v5.2):
   - init           : Initialization phase
   - theorem-audit  : Theorem audit phase
   - strategy       : Strategy formulation phase
   - skeleton       : Skeleton construction phase
   - skeleton-review: Skeleton review phase
   - decomposition  : Decomposition phase
   - expand-verify-loop : Expand-verify loop phase
   - reference-check: Reference checking phase
   - finalization   : Finalization phase
   - complete       : Completion phase
   - escalated      : Escalation phase"
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Constants
;; -----------------------------------------------------------------------------

(def ^:const template-dir "templates")
(def ^:const template-extension ".md")

(def ^:const template-names
  "Set of all available template names."
  #{"init"
    "theorem-audit"
    "strategy"
    "skeleton"
    "skeleton-review"
    "decomposition"
    "expand-verify-loop"
    "reference-check"
    "finalization"
    "complete"
    "escalated"})

;; -----------------------------------------------------------------------------
;; Path Functions
;; -----------------------------------------------------------------------------

(defn template-path
  "Returns the resource path for a template name.

   Example:
     (template-path \"init\") => \"templates/init.md\"
     (template-path \"skeleton-review\") => \"templates/skeleton-review.md\"

   Returns nil if name is nil."
  [name]
  (when name
    (str template-dir "/" name template-extension)))

;; -----------------------------------------------------------------------------
;; Loading Functions
;; -----------------------------------------------------------------------------

(defn load-template
  "Loads a template by name and returns its content as a string.

   Example:
     (load-template \"init\") => \"# Initialization Phase\\n...\"

   Returns nil if:
   - name is nil
   - template file does not exist
   - template cannot be read"
  [name]
  (when name
    (when-let [path (template-path name)]
      (when-let [resource (io/resource path)]
        (slurp resource)))))

(defn list-templates
  "Returns a set of all available template names.

   Example:
     (list-templates) => #{\"init\" \"theorem-audit\" \"strategy\" ...}"
  []
  template-names)

;; -----------------------------------------------------------------------------
;; Interpolation Functions
;; -----------------------------------------------------------------------------

(defn interpolate
  "Replaces interpolation markers in template content with provided values.

   Markers are strings like \"<THEOREM_STATEMENT>\" that get replaced
   with corresponding values from the vars map.

   Args:
     template - String containing the template content
     vars     - Map of marker strings to replacement values

   Example:
     (interpolate \"Theorem: <THEOREM_STATEMENT>\"
                  {\"<THEOREM_STATEMENT>\" \"P implies Q\"})
     => \"Theorem: P implies Q\"

     (interpolate \"Iteration <N> of <LIMIT>\"
                  {\"<N>\" \"5\" \"<LIMIT>\" \"10\"})
     => \"Iteration 5 of 10\"

   Notes:
   - Markers not in vars are left unchanged
   - Multiple occurrences of the same marker are all replaced
   - Returns nil if template is nil
   - Returns template unchanged if vars is nil or empty"
  [template vars]
  (when template
    (if (or (nil? vars) (empty? vars))
      template
      (reduce (fn [content [marker value]]
                (str/replace content marker (str value)))
              template
              vars))))
