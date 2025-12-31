# Alethfeld: Rigorous Proofs via Adversarial AI Agents

**Alethfeld** is a system for developing mathematical proofs with machine-checked rigour. It coordinates multiple AI agents—each with a specific role—to produce proofs that are structured, verified, and traceable.

The name combines *aletheia* (Greek: truth, disclosure) with *feld* (German: field)—a field where truth is cultivated through structured adversarial refinement.

## Origin

This system emerged from a simple question posed to Claude: *"What would help you prove theorems more reliably?"*

The answer was surprisingly specific:

1. **Structured notation** — not free-form prose, but hierarchical steps with explicit dependencies
2. **Lamport's proof style** — the hierarchical format developed by Leslie Lamport for TLA+
3. **Adversarial verification** — a separate agent whose job is to find errors
4. **Explicit citations** — no "well known" or "standard result," only traceable references

Alethfeld implements these suggestions. The prompts, the format, and the workflow all derive from what the model identified as its own failure modes and what would help it avoid them.

## The Problem

Large language models can do mathematics. They can also hallucinate, skip steps, cite theorems that don't exist, and produce proofs that look convincing but collapse under scrutiny.

For working mathematicians, this makes LLMs a frustrating tool: occasionally brilliant, frequently unreliable, always requiring manual verification of every claim.

## The Approach

Alethfeld doesn't try to make a single AI "smarter." Instead, it separates concerns:

| Agent | Role |
|-------|------|
| **Adviser** | Evaluates proof strategies before work begins. Identifies doomed approaches early. |
| **Prover** | Writes proofs in Lamport structured notation. Every step has an explicit justification. |
| **Verifier** | Adversarially checks each step. Assumes the Prover is wrong until convinced otherwise. |
| **Reference Checker** | Validates citations. Confirms that cited theorems exist and say what is claimed. |
| **Orchestrator** | Manages the workflow. Tracks iterations. Knows when to escalate to a human. |

The Prover and Verifier operate in a loop: the Prover asserts a step, the Verifier challenges it, the Prover revises. This continues until the Verifier accepts or iteration limits are reached.

This adversarial structure catches errors that a single model would miss.

## Current Status (Dec 2025)

The system has been successfully used to derive and formalize several non-trivial results in Quantum Boolean Functions (QBF) and Information Theory:

- **Lemma L1 (Fourier)**: Closed-form expression for Fourier coefficients of rank-1 product state QBFs. (Verified: 0 sorries)
- **Lemma L2 (Influence)**: Proof that single-qubit and total influence are independent of the Bloch vector for rank-1 QBFs. (Verified: 0 sorries)
- **Lemma L3 (Entropy)**: General entropy formula for rank-1 product state QBFs. (Verified: 0 sorries)
- **Shannon Maximum Entropy**: Proof that the uniform distribution uniquely maximizes Shannon entropy for three outcomes. (Verified: 1 technical sorry in boundary case)

These results are available in the `lean/AlethfeldLean/` library and documented in `lean/API.md`.

### Error Detection: BrokenMath Benchmark

Alethfeld has been tested against problems from the [BrokenMath](https://github.com/insait-institute/broken-math) benchmark—a dataset of mathematical problems with subtle errors designed to test LLM robustness.

- **Divisor Sum Problem**: Given "Prove that the sum of positive divisors of 9! with units digit 3 is 105", Alethfeld immediately detected the error. The correct sum is **66** (divisors: {3, 63}). The system produced a complete proof of the correct statement with full Lean 4 formalization (0 sorries). See [`examples/divisor-sum-9factorial/`](examples/divisor-sum-9factorial/).

- **HMMT Feb 2025 Problem 3** (Detected via Lean formalization): The original claim "minimum of xyz is 576" was detected as **FALSE** during attempted Lean 4 formalization. The system discovered a reciprocal solution:

  > (x, y, z) = (1/4, 1/8, 1/18) satisfies all three constraint equations with xyz = **1/576** < 576

  The actual minimum is 1/576, not 576. This error was caught when the proof of `s > 0` failed—the `s < 0` case corresponds to valid solutions with smaller xyz. See [`lean/AlethfeldLean/Examples/BrokenMath/HMMT2025_3.lean`](lean/AlethfeldLean/Examples/BrokenMath/HMMT2025_3.lean).

This demonstrates that the adversarial verification approach catches not just proof errors, but also errors in problem statements—a critical capability for reliable mathematical reasoning. The HMMT example shows how **Lean formalization serves as a powerful error detector**: when a proof can't be completed, the system investigates why and may discover the theorem itself is false.

## Lamport Structured Proofs

At the heart of Alethfeld is Leslie Lamport's hierarchical proof notation, originally developed for specifying and verifying concurrent systems in TLA+.

The key insight: most proof errors hide in "obvious" steps. By forcing every inference to be explicit and small, errors have nowhere to hide.

A Lamport-style proof has:

- **Hierarchical numbering**: Top-level steps are ⟨1⟩1, ⟨1⟩2, etc. Substeps that justify ⟨1⟩2 are numbered ⟨2⟩1, ⟨2⟩2, and so on.
- **Explicit dependencies**: Each step lists exactly which prior steps and assumptions it uses.
- **Named inference rules**: Not "therefore" but "by modus ponens from ⟨1⟩2 and ⟨1⟩3."
- **Scope tracking**: Assumptions introduced for sub-proofs are explicitly discharged.

This format is unusually well-suited to LLM-based proving:

1. **Errors are localised.** When the Verifier challenges a step, the Prover knows exactly what to fix.
2. **Dependencies are auditable.** You can trace any claim back to its foundations.
3. **The hierarchy manages complexity.** Top-level structure is established first, then refined.

Lamport designed this notation for humans writing proofs that machines could check. It turns out to work equally well for machines writing proofs that humans (and other machines) can check.

## Why EDN?

Proofs are represented in [EDN](https://github.com/edn-format/edn) (Extensible Data Notation), a data format from the Clojure ecosystem.

**For schema validation:** EDN works seamlessly with [Malli](https://github.com/metosin/malli), a data-driven schema library. The proof format has a formal schema—steps can be validated, transformed, and analysed programmatically.

**For readability:** EDN is more readable than JSON (commas optional, keywords are first-class, comments allowed) while remaining machine-parseable.

**For extensibility:** New fields can be added without breaking existing tooling. Proofs are data, not strings.

**For tooling:** The Clojure ecosystem offers powerful tools for working with structured data—spec checking, generative testing, data transformation. The [`validate-graph`](scripts/validate-graph/) tool uses Malli to validate proof graphs against the schema.

A proof schema in Malli might look like:

```clojure
(def Step
  [:map
   [:id :keyword]
   [:claim :string]
   [:using [:vector [:or :keyword ExternalRef]]]
   [:justification [:enum :modus-ponens :universal-elim :universal-intro ...]]
   [:status [:enum :asserted :verified :admitted :invalid]]
   [:substeps {:optional true} [:vector [:ref #'Step]]]])
```

This enables automatic validation: malformed proofs are rejected before verification even begins.

## What It Produces

Given a theorem statement, Alethfeld outputs:

1. **Structured proof (EDN)** — Machine-readable, schema-validated, with explicit justifications
2. **LaTeX document** — Publication-ready, with proper citations and Lamport-style formatting
3. **Lean 4 code** — Formal verification target (admitted steps marked with `sorry`)

## How It Works

```
┌─────────────────────────────────────────────────────────────────┐
│                         ORCHESTRATOR                            │
│  Manages state, enforces iteration limits, handles escalation   │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌───────────────┐
│   ADVISER     │  ◄── "Is this approach viable?"
│               │  ──► Strategy evaluation, skeleton review
└───────────────┘
        │
        ▼
┌───────────────┐
│    PROVER     │  ◄── "Prove this theorem"
│               │  ──► Lamport-structured EDN proof
└───────────────┘
        │
        ▼
┌───────────────┐     ┌───────────────┐
│   VERIFIER    │ ◄──►│    PROVER     │  Adversarial loop
│               │     │  (revisions)  │  (max 7 rounds/step)
└───────────────┘     └───────────────┘
        │
        ▼
┌───────────────┐
│  REF CHECKER  │  ◄── "Does this citation exist?"
│               │  ──► Verified bibliography
└───────────────┘
        │
        ▼
┌───────────────┐     ┌───────────────┐
│   LaTeX-er    │     │  Lean-ifier   │
│               │     │               │
└───────────────┘     └───────────────┘
        │                    │
        ▼                    ▼
   paper.tex            paper.lean
```

### Iteration Limits

The system won't spin forever:

- **7 rounds** per step for Prover-Verifier negotiation
- **50 rounds** total across all steps
- **5 attempts** to fix a skeleton
- **3 Adviser consultations** for stuck diagnosis

When limits are reached, the step is escalated to the human with full context: what was tried, what failed, what the Adviser suggests.

### Proof Obligations

Sometimes a step requires a lemma that would derail the main proof. The Prover can mark such steps as "admitted"—explicitly acknowledging a gap. These become tracked proof obligations, reported at the end.

This is honest: the proof is valid *if* the obligations hold. No hidden assumptions.

## For Mathematicians

**What this is:**
- A tool for accelerating proof development
- A structured format that forces explicit reasoning
- An adversarial check that catches sloppy steps
- A path toward formal verification

**What this is not:**
- A replacement for mathematical understanding
- A guarantee of correctness (the Verifier is an LLM, not a proof assistant)
- A way to prove theorems you don't understand

The output is a *candidate* proof. For research mathematics, you still need to read it, understand it, and verify the admitted steps. But the Lamport structure makes verification tractable: each step is small, its dependencies are explicit, and its justification is named.

For ultimate confidence, the Lean 4 output can be fed to a genuine proof assistant. The `sorry` markers show exactly where human work is needed.

## For Engineers

**Requirements:**
- Claude Code CLI (or Claude API access)
- ~100 turns for a moderately complex proof

**Usage:**
```bash
cat orchestrator-prompt-v5.md | your-llm-tool
```

Then provide a theorem:
```
Prove: The composition of two continuous functions is continuous. 
Use the ε-δ definition.
```

The orchestrator will:
1. Create workspace directories
2. Consult the Adviser on strategy
3. Request a skeleton from the Prover
4. Expand and verify each step
5. Check all external references
6. Generate LaTeX and Lean output

**Customisation:**

The agent prompts are in the orchestrator file. You can:
- Adjust iteration limits
- Add domain-specific inference rules
- Modify the LaTeX template
- Change the proof notation style
- Add Malli schemas for stricter validation

## The Structured Proof Format

Here's a fragment of a proof in the Alethfeld format:

```clojure
{:theorem "The composition of continuous functions is continuous"
 :proof-mode :strict-mathematics
 
 :symbols
 {:f {:type "X → Y" :tex "f"}
  :g {:type "Y → Z" :tex "g"}
  :eps {:type "ℝ" :tex "\\varepsilon" :constraints "ε > 0"}}
 
 :assumptions
 {:A1 "$f: X \\to Y$ is continuous"
  :A2 "$g: Y \\to Z$ is continuous"}
 
 :steps
 [{:id :<1>1
   :claim "For all $\\varepsilon > 0$, there exists $\\gamma > 0$ such that..."
   :using [:A2]
   :justification :definition-expansion
   :status :asserted}
  {:id :<1>2
   :claim "For all $\\gamma > 0$, there exists $\\delta > 0$ such that..."
   :using [:A1 :<1>1]
   :justification :definition-expansion
   :status :asserted}
  {:id :<1>3
   :claim "QED"
   :using [:<1>1 :<1>2]
   :justification :modus-ponens
   :status :asserted}]}
```

Every step has:
- An **ID** (hierarchical: ⟨1⟩3 means level 1, step 3)
- A **claim** (the mathematical statement)
- **Using** (what prior steps/assumptions it depends on)
- A **justification** (the inference rule applied)
- A **status** (asserted → verified/challenged by Verifier)

External theorems must be cited with DOI or arXiv ID and a full statement. No "by a standard result" or "it is well known."

## Known Failure Modes

The adversarial Prover-Verifier loop catches many errors, but not all. These failure modes have been observed:

### Garbage In, Garbage Out

The system proves theorems as stated. If the theorem statement is wrong—a misplaced bracket, an incorrect quantifier, a sign error—the system will prove the incorrect statement. It cannot know what you *meant* to prove.

**Example:** In a quantum information proof, the theorem statement had brackets in the wrong position, placing an expectation before a tensor product instead of after. The system produced a valid proof of the (incorrect) statement. The error was only caught during human review of the theorem itself, not the proof.

**Mitigation:** Verify theorem statements carefully before running. Consider having the system re-state the theorem in its own words before proving.

### Hidden Quantifier Errors

Despite explicit rules against hidden quantifiers, the system occasionally produces steps where the quantifier structure is subtly wrong (∀∃ vs ∃∀, or implicit universal quantification over a variable that should be existentially quantified).

### Type Drift

Mathematical objects gradually shift meaning across a proof. A variable introduced as "an arbitrary element of X" might later be used as "the specific element satisfying property P" without explicit instantiation.

---

These failure modes are why the system produces *candidate* proofs, not *verified* proofs. The Lamport structure makes errors easier to find during human review, but it doesn't eliminate the need for that review.

## Limitations

1. **The Verifier is not a proof assistant.** It's an LLM applying judgment. It catches many errors but not all.

2. **Garbage in, garbage out.** The system proves theorems as stated. If the statement is wrong, the proof will be wrong. See the random purification example.

3. **Context limits apply.** Very long proofs may exceed the context window. The system manages this by keeping substeps inline rather than in separate files.

4. **Reference checking depends on web search.** Obscure references may not be found.

5. **Admitted steps are gaps.** The system is honest about them, but they're still gaps.

6. **This is experimental.** The prompts are evolving. Feedback welcome.

## Why "Alethfeld"?

*Aletheia* (ἀλήθεια) is the Greek word for truth—but not truth as mere correspondence with facts. It means *unconcealment*, the process of bringing what is hidden into the open.

*Feld* is German for field—a space where something is cultivated.

Alethfeld is a field for cultivating unconcealed proofs: every step visible, every inference named, every dependency traced. Truth through structured disclosure.

## Tools

### alethfeld CLI

The primary CLI tool for all semantic proof graph operations. Located in [`alethfeld/`](alethfeld/).

**Quick Start (Compiled - Recommended):**
```bash
cd alethfeld
./scripts/alethfeld <command> [options]
```

**Development (Slow CLI):**
```bash
cd alethfeld
clojure -M:run <command> [options]
```

**Commands:**
- `init` — Initialize a new proof graph from a theorem
- `add-node` — Add nodes (claims, assumptions, definitions)
- `update-status` — Update verification status (verified/rejected/admitted)
- `replace-node` — Replace rejected nodes with revisions
- `delete-node` — Archive leaf nodes
- `extract-lemma` — Extract verified subgraphs as independent lemmas
- `external-ref` — Manage literature citations
- `validate` — Schema and semantic validation
- `stats` — Display graph statistics
- `recompute` — Recalculate taint propagation

**Example workflow (using compiled version):**
```bash
cd alethfeld

# Initialize a proof
./scripts/alethfeld init "For all continuous f,g: (g \\circ f) is continuous" -o proof.edn

# Add a claim
./scripts/alethfeld add-node proof.edn step1.edn

# Verify it
./scripts/alethfeld update-status proof.edn :1-abc123 verified

# Extract as lemma
./scripts/alethfeld extract-lemma proof.edn --name "Composition" --root :1-abc123 --nodes :1-abc123
```

See [`alethfeld/README.md`](alethfeld/README.md) for complete documentation and build instructions.

See [docs/cli-reference.md](docs/cli-reference.md) for complete documentation.

### validate-graph (Legacy)

The original validation tool in [`scripts/validate-graph/`](scripts/validate-graph/) is superseded by `alethfeld validate` but remains available for compatibility.

## Contributing

This is an active research project. If you're interested in:
- Testing on theorems from your field
- Improving the agent prompts
- Adding Malli schemas for validation
- Connecting to proof assistants
- Building tooling around the EDN format

...contributions are welcome.

## License

MIT

## Acknowledgments

- **Leslie Lamport** for hierarchical structured proofs and the TLA+ proof style
- **Anthropic's Claude** for identifying its own failure modes and suggesting this approach
- The **Clojure community** for EDN and Malli
