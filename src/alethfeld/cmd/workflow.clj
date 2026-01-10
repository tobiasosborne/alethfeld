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
        ;; Try classpath first (for jar), then absolute path from CWD
        workflow-text (or (some-> (io/resource workflow-path) slurp)
                          (let [f (io/file workflow-path)]
                            (when (.exists f)
                              (slurp f)))
                          (throw (ex-info "Workflow documentation not found"
                                          {:type :not-found
                                           :path workflow-path
                                           :hint "Run 'af workflow' from your project root directory"})))]
    {:output workflow-text
     :next-actions [(core/make-action "af ready --name <agent> --role verifier"
                                      "Start working on verification")
                    (core/ready-action)
                    (core/status-action)]}))
