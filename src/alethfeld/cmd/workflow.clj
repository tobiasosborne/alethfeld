(ns alethfeld.cmd.workflow
  "Workflow command implementation.

   Displays the Alethfeld proof workflow documentation."
  (:require [alethfeld.cmd.core :as core]
            [clojure.java.io :as io]))

;; -----------------------------------------------------------------------------
;; Workflow Command
;; -----------------------------------------------------------------------------

(defn cmd-workflow
  "Display the Alethfeld proof workflow.

   Returns a map with:
   - :output - The workflow documentation text
   - :next-actions - Suggested next commands"
  [_context]
  (let [workflow-path "prompts/workflow.md"
        workflow-text (try
                        (slurp (io/resource workflow-path))
                        (catch Exception _
                          (slurp workflow-path)))]
    {:output workflow-text
     :next-actions [(core/make-action "af ready --name <agent> --role verifier"
                                      "Start working on verification")
                    (core/ready-action)
                    (core/status-action)]}))
