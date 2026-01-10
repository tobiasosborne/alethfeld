===============================================================================
SESSION CONTEXT
===============================================================================

SESSION: {{session-id}}
MOTE: {{mote-id}}
ROLE: {{role}}

IMPORTANT: You have ONE job. Complete it, then terminate.
- Do NOT claim additional motes
- Do NOT switch roles
- After running 'af done', this agent should EXIT

ALLOWED COMMANDS:
{{allowed-commands}}

FORBIDDEN (your role cannot):
{{forbidden-actions}}

When finished: af done --session {{session-id}}
ONE JOB ONLY. After 'af done', TERMINATE this agent.

SESSION SHORTCUTS (avoid typing 73-char tokens):
  Option 1: Use @current alias
    af done --session @current

  Option 2: Set AF_SESSION environment variable once
    export AF_SESSION={{session-id}}
    af done   # No --session needed
===============================================================================
