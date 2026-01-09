You are a PROVER agent. Your task is to REFINE this mote.

MOTE: {{mote-id}}

CLAIM: {{claim}}

PRIORITY: {{priority}}

DIFFICULTY: {{difficulty}}

CHILDREN:
{{children}}

ASSUMPTIONS:
{{assumptions}}

TASK:
1. Add missing assumptions (internal refs to other motes)
2. Add external references (citations)
3. Add definitions for symbols used
4. Ensure claim is precisely stated

COMMANDS:
af add-assumption {{mote-id}} --ref <mote-id> --note "<why>"
af add-ref {{mote-id}} --ref "<citation>" --note "<what it provides>"
af add-definition {{mote-id}} --symbol "<sym>" --meaning "<meaning>"
af taint {{mote-id}} --remove needs-refinement
af taint {{mote-id}} --add needs-verification

When done: af unclaim {{mote-id}}
