(ns alethfeld.cmd.workflow
  "Workflow command implementation.

   Displays the Alethfeld proof workflow documentation."
  (:require [alethfeld.cmd.core :as core]
            [clojure.java.io :as io]))

;; -----------------------------------------------------------------------------
;; Embedded Workflow (fallback when file not found)
;; -----------------------------------------------------------------------------

(def ^:private embedded-workflow
  "Alethfeld Proof Workflow
========================

1. INITIALIZE
   af init --name \"My Proof\"
   af create --root --claim \"Main theorem\"

2. VERIFY (verifier role) - gatekeeper step
   af ready --name <you> --role verifier
   af vote <id> --for --reason \"...\"
   Options: vote for/against, request decomposition, request refinement

3. DECOMPOSE (proposer role)
   af ready --name <you> --role proposer
   af propose <id> --claim \"substep 1\" --claim \"substep 2\"

4. REVIEW (advisor role) - requires quorum approvals
   af ready --name <you> --role advisor
   af approve <id> --reason \"...\"
   af approve-all --reason \"...\"

5. REFINE (prover role)
   af ready --name <you> --role prover
   af add-ref <id> --ref \"citation\"
   af add-assumption <id> --assumes <other-mote-id>

6. COMPLETE
   When all children verified → parent auto-verifies
   Root verified → proof complete!

Session Management:
  af sessions           # List active sessions
  af done --session @current  # End session (use @current alias)")

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
        ;; Try classpath first (for jar), then file from CWD, then embedded fallback
        workflow-text (or (some-> (io/resource workflow-path) slurp)
                          (let [f (io/file workflow-path)]
                            (when (.exists f)
                              (slurp f)))
                          embedded-workflow)]
    {:output workflow-text
     :next-actions [(core/make-action "af ready --name <agent> --role verifier"
                                      "Start working on verification")
                    (core/ready-action)
                    (core/status-action)]}))
