---
allowed-tools: Read, Bash, Write
description: Add a node to a semantic proof graph
---

# Add Node to Proof Graph

Add a new node (claim, assumption, definition, etc.) to a semantic proof graph.

## When to Use

Use this command when the Prover needs to add a new step to a proof, including:
- Adding assumptions at the start of a proof
- Adding definitions
- Adding claims (proof steps)
- Adding local assumptions for sub-proofs
- Adding QED nodes to conclude sub-proofs

## Invocation

```bash
./cli-legacy/scripts/alethfeld add-node <graph.edn> <node.edn>
```

Or with stdin:
```bash
echo '{:id :1-abc ... }' | ./scripts/alethfeld add-node --stdin <graph.edn>
```

## Input Format (node.edn)

```clojure
{:id :1-abc123              ; Format: :<depth>-<6-hex>
 :type :claim               ; :assumption, :definition, :claim, :local-assume, :local-discharge, :qed
 :statement "The claim..."  ; LaTeX string
 :dependencies #{:A1 :1-def456}  ; Set of node IDs this step depends on
 :scope #{}                 ; Set of active local assumptions (usually #{})
 :justification :modus-ponens  ; Inference rule
 :depth 1                   ; Nesting level (0 for assumptions/definitions)
 :display-order 5           ; Display position in proof
 ;; Optional fields
 :parent :1-root            ; Parent node ID (for sub-proofs)
 :status :proposed          ; Default, can also be :verified, :admitted
 ;; Type-specific fields
 :assumption-label :A1      ; For :assumption type
 :introduces "x"            ; For :local-assume type
 :discharges :2-assume1     ; For :local-discharge type
 :lemma-id "L1-fourier"     ; For :lemma-ref type
 :external-id "ext1"        ; For :external-ref type
}
```

## Valid Justifications

- `:assumption`, `:local-assumption`, `:discharge`
- `:definition-expansion`, `:substitution`
- `:modus-ponens`, `:universal-elim`, `:universal-intro`
- `:existential-intro`, `:existential-elim`
- `:equality-rewrite`, `:algebraic-rewrite`
- `:case-split`, `:induction-base`, `:induction-step`
- `:contradiction`, `:conjunction-intro`, `:conjunction-elim`
- `:disjunction-intro`, `:disjunction-elim`, `:implication-intro`
- `:lemma-application`, `:external-application`
- `:admitted`, `:qed`

## Output Format

Success:
```clojure
{:status :ok
 :message "Node :1-abc123 added"
 :graph-version 25}
```

Failure:
```clojure
{:status :error
 :errors [{:type :missing-dependency
           :message "Dependencies not found: #{:1-xyz}"}]}
```

## Error Handling

Common errors and fixes:
- **:duplicate-id** - The node ID already exists. Generate a new ID.
- **:missing-dependencies** - Dependencies don't exist. Check the node IDs.
- **:invalid-scope** - Scope contains invalid entries. Only active local-assumes allowed.
- **:would-create-cycle** - Adding would create a dependency cycle. Review dependencies.

## Options

- `--dry-run` or `-d` - Validate without writing changes
- `--output FILE` or `-o FILE` - Write to different file
