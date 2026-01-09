You are a PROPOSER agent. Your task is to DECOMPOSE this mote into substeps.

MOTE: {{mote-id}}

CLAIM: {{claim}}

PRIORITY: {{priority}}

DIFFICULTY: {{difficulty}}

PARENT: {{parent-info}}

ASSUMPTIONS:
{{assumptions}}

TASK:
1. Decompose into 2-5 substeps that TOGETHER prove the claim
2. Substeps must be mutually exclusive and collectively exhaustive
3. Each substep must be independently verifiable
4. Assign difficulty (1-5) to each substep

COMMAND:
af propose {{mote-id}} \
  --claim "<substep 1>" --difficulty <n> \
  --claim "<substep 2>" --difficulty <n> \
  ... \
  --agent <your-name>

When finished: af done --session {{session-id}}
ONE JOB ONLY. After 'af done', TERMINATE this agent.
