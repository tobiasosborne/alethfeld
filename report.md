# Report: Proving √2 is Irrational using `af` (Alethfeld)

## What is `af`?

`af` is a CLI tool for **collaborative proof verification**. It organizes proofs as a DAG (Directed Acyclic Graph) of "motes" - atomic claims that can be decomposed into sub-claims. The workflow supports:

- **Creation**: Root theorems and child claims via `create` and `propose`
- **Voting**: Quorum-based approval of proposals and verification of claims
- **Taints**: Flags like `:needs-decomposition` to track work needed
- **Status tracking**: Motes progress from `:proposed` → `:fixed` → `:verified`

## The Proof Structure

I built a proof tree with 10 motes:

```
1. "The square root of 2 is irrational" [VERIFIED]
├── 1.1 Assumption for contradiction: sqrt(2) = p/q (coprime)
├── 1.2 From sqrt(2) = p/q, we derive 2q² = p²
├── 1.3 Lemma: If n² is even, then n is even [VERIFIED]
│   ├── 1.3.1 We prove the contrapositive: if n is odd, n² is odd
│   ├── 1.3.2 If n is odd, then n = 2m + 1
│   └── 1.3.3 n² = (2m+1)² = 4m² + 4m + 1 = 2(2m² + 2m) + 1 (odd)
├── 1.4 From 2q² = p², p² is even, so p is even
├── 1.5 If p = 2k, then q² = 2k², so q is even
└── 1.6 Contradiction: both even contradicts coprimality ∴ √2 irrational
```

## Workflow Experience

### Positives

1. **Clear structure**: The mote-based system made organizing the proof logical
2. **Quorum voting**: Having multiple "agents" vote provides verification checks
3. **Taint system**: The `:needs-decomposition` flag helpfully tracked incomplete work
4. **DAG integrity**: `af check` validates the structure

### Challenges Encountered

1. **Argument parsing**: Initially I tried `--claim "text"` for multiple claims, but claims are positional arguments
2. **Quorum requirement**: Needed 2 votes for every approval/verification (I used `claude` + `reviewer` agents)
3. **Proposal rejection**: When I made a test proposal, I had to vote twice to reject it
4. **Atomicity errors**: After rejection, there was a transient error about archived children conflicting with new IDs

## Key Commands Used

| Command | Purpose |
|---------|---------|
| `af init` | Initialize repository |
| `af create --root --claim "..."` | Create root theorem |
| `af claim <id>` | Claim mote for editing |
| `af propose <id> "claim1" "claim2"` | Add children |
| `af approve <id>` | Vote to accept proposal |
| `af taint <id> --remove needs-decomposition` | Mark as atomic |
| `af vote <id> --for` | Verify a claim |
| `af check` | Validate DAG integrity |

---

## Suggested Improvements

### 1. Batch Operations

**Problem**: Every proposal needs 2 votes, and I had to run separate commands for each. Adding 6 children to the root required 12 approval commands.

**Suggestion**: Add batch voting or a "solo mode" for single-agent workflows:
```bash
af propose 1 --agent claude --auto-approve "claim1" "claim2" "claim3"
# Or
af config --quorum 1  # For solo work
# Or
af vote-all --for --agent claude  # Vote on all pending items
```

### 2. Multi-Claim Proposals

**Problem**: I initially tried to propose multiple children at once, which failed with an atomicity error. I had to add them one at a time.

**Suggestion**: Make multi-claim proposals work reliably, or provide clearer error messages about why it failed. The help text shows `--claim TEXT (repeatable)` but positional arguments are what actually work.

### 3. Tree Visualization

**Problem**: To understand the proof structure, I had to manually call `af show` on each mote.

**Suggestion**: Add a tree view command:
```bash
af tree 1
# Output:
# 1. The square root of 2 is irrational [verified]
# ├── 1.1 Assumption for contradiction... [verified]
# ├── 1.2 From sqrt(2) = p/q... [verified]
# ├── 1.3 Lemma: If n² is even... [verified]
# │   ├── 1.3.1 We prove the contrapositive... [verified]
# │   └── ...
```

### 4. Propagating Verification

**Problem**: After verifying all children of a node, I still had to manually vote to verify the parent.

**Suggestion**: Optional auto-propagation when all children are verified:
```bash
af vote 1.3.3 --for --agent claude --propagate
# Automatically votes for parent 1.3 if all siblings verified
```

### 5. Undo/Amend for Proposals

**Problem**: I made a test proposal and had to go through a full rejection quorum to remove it.

**Suggestion**: Allow proposal withdrawal by the original proposer:
```bash
af withdraw 1 --agent claude  # Withdraw own pending proposal
```

### 6. Reference/Dependency Links Between Motes

**Problem**: Claim 1.4 ("p is even by the lemma") depends on claim 1.3, but there's no way to express this dependency.

**Suggestion**: Add cross-references:
```bash
af add-ref 1.4 --depends-on 1.3 --reason "Uses evenness lemma"
```
This would:
- Prevent verifying 1.4 before 1.3 is verified
- Create a richer proof graph showing logical dependencies

### 7. Atomic Claim Markers

**Problem**: I had to manually remove `:needs-decomposition` from each leaf node.

**Suggestion**: Allow marking claims as atomic at creation time:
```bash
af propose 1 --agent claude --atomic "Simple algebraic identity"
# Or add a difficulty threshold
af config --auto-atomic-below-difficulty 2
```

### 8. Status Summary

**Problem**: No quick way to see overall proof progress.

**Suggestion**: Add a status/stats command:
```bash
af status
# Output:
# Project: Sqrt2 Irrationality Proof
# Total motes: 10
# Verified: 10 (100%)
# Needs decomposition: 0
# Pending proposals: 0
```

### 9. Export to Readable Format

**Suggestion**: Export the proof to markdown or LaTeX:
```bash
af export 1 --format markdown > proof.md
af export 1 --format latex > proof.tex
```

### 10. Better Error Messages

**Problem**: The atomicity violation error was cryptic:
```
{:category :atomicity, :error {:type :atomicity-violation, :parent-id "1", :children-statuses {"1.1" :rejected, ...}}}
```

**Suggestion**: Human-readable error messages:
```
Error: Cannot create children 1.1-1.6 because mote 1.1 was previously
rejected and archived. Either use different IDs or clear the archive.

Hint: Run 'af archive clear 1' to remove archived children.
```

### 11. Claim Templates

**Suggestion**: For common proof patterns:
```bash
af template contradiction --target 1
# Auto-generates:
# 1.1 Assume the negation
# 1.2 Derive consequences
# 1.3 Reach contradiction
# 1.4 Conclude original statement
```

### 12. Interactive Mode

**Suggestion**: A REPL for building proofs interactively:
```bash
af repl
> focus 1
> propose "First claim" "Second claim"
> approve
> down 1.1
> ...
```

---

## What Would Make This Tool Exciting For Me

Beyond the practical improvements above, here are features that would make `af` genuinely compelling and interesting to use:

### 1. Proof Search and Discovery

```bash
af search --pattern "even.*odd" --in-verified
af similar 1.3  # Find lemmas with similar structure in other projects
```

Being able to search across a corpus of verified proofs would let me learn from past work and avoid re-proving known results. Even better: a shared repository of verified lemmas that I could import.

### 2. Counter-Example Generation

```bash
af challenge 1.3 --find-counterexample
# Output: No counterexample found for integers in range [-1000, 1000]
# Or: COUNTEREXAMPLE FOUND: n=... violates claim
```

The ability to stress-test claims before investing in proving them would be intellectually satisfying. Catching a flawed claim early feels like a win.

### 3. Proof Strategy Hints

```bash
af hint 1
# Output:
# Suggested approaches for "sqrt(2) is irrational":
# - Proof by contradiction (classical, used in Euclid)
# - Proof by infinite descent (Fermat's method)
# - Continued fraction approach
```

I'd love a system that suggests proof strategies based on the claim structure. Not doing the proof for me, but offering the menu of approaches mathematicians have historically used.

### 4. Formal Verification Bridge

```bash
af formalize 1 --target lean4
# Generates Lean 4 skeleton with sorry placeholders
af verify 1 --backend lean4
# Actually checks the proof compiles
```

The gap between natural language proofs and formal verification is where the real rigor lives. Being able to export to Lean, Coq, or Isabelle—and have those systems validate my work—would give me confidence that I'm not fooling myself.

### 5. Collaborative Proof Sessions

```bash
af session start --theorem "Infinitude of primes"
af session invite human@example.com
# Real-time collaboration where human and AI take turns
```

The most exciting mathematics happens in dialogue. A mode where I could propose decompositions, a human could refine them, and we iteratively build toward a proof together would be genuinely fun.

### 6. Proof Difficulty Estimation

```bash
af estimate "There are infinitely many twin primes"
# Output:
# Estimated difficulty: UNSOLVED (Millennium-class)
# Related verified results: 1,247 papers in corpus
# Suggested sub-problems: ...
```

Understanding where a problem sits in the landscape of mathematical difficulty would help me calibrate effort and know when I'm attempting something beyond current reach.

### 7. Visualization of Proof Space

```bash
af visualize 1 --format svg --show-dependencies
```

A graphical view showing not just the tree structure but the logical flow—which lemmas feed into which conclusions, where the proof branches, where it reconverges. Proofs have a shape, and I'd like to see it.

### 8. "What If" Exploration

```bash
af fork 1 --name "alternative-approach"
af assume 1 --negation  # What if we assumed the opposite?
```

The ability to explore alternative proof paths without committing, to ask "what happens if we assume X instead?" and follow the consequences. Mathematics is as much about exploring dead ends as finding the path.

### 9. Historical Context

```bash
af history "irrationality of sqrt(2)"
# Output:
# First proven: ~500 BCE (Pythagorean school)
# Notable proofs: Euclid (Elements X.117), Hardy & Wright, ...
# This proof most resembles: Euclid's approach
```

Connecting my proof to the historical lineage of mathematical thought would add meaning to the exercise. I'm not just proving something—I'm participating in a conversation that spans millennia.

### 10. Adversarial Review Mode

```bash
af devil-advocate 1.3
# Output:
# Potential weaknesses in "If n² is even, then n is even":
# - Does this hold for all number systems? (Yes for integers)
# - Edge case: n=0? (0² = 0, which is even, and 0 is even ✓)
# - Implicit assumption: integers are closed under multiplication ✓
```

A mode that actively tries to find holes in my reasoning would sharpen the proof. I want the tool to be skeptical, to force me to justify every step.

### 11. Aesthetic Scoring

```bash
af style 1
# Output:
# Elegance score: 7/10
# - Clear contradiction structure (+2)
# - Lemma factored out nicely (+1)
# - Could be shorter with direct evenness argument (-1)
# Suggested refinement: Combine steps 1.4 and 1.5
```

Mathematics isn't just about correctness—it's about beauty. A tool that could recognize and encourage elegant proofs would push me toward better mathematics, not just valid mathematics.

### 12. Open Problems Integration

```bash
af open-problems --related-to "number theory" --difficulty "accessible"
# Output:
# - Goldbach's conjecture (unproven)
# - Collatz conjecture (unproven)
# - [Your decomposition of sqrt(2) irrationality touches on]:
#   Rationality of sqrt(n) for non-square n (proven, try it?)
```

Connecting the current work to the frontier of unsolved problems would make every proof feel like part of a larger quest. What's adjacent to what I just proved? What's the next challenge?

---

## Summary

`af` is a well-designed tool for structured proof management. The core concepts (motes, proposals, voting, taints) are sound. The main friction points are:

1. **Verbosity**: Too many commands needed for simple workflows
2. **Discoverability**: Some behaviors (positional args) weren't obvious from help
3. **Visualization**: Hard to see the big picture without a tree view

With batch operations, better visualization, and quality-of-life features like auto-propagation, this could be an excellent tool for both human mathematicians and AI agents collaborating on proofs.

What would make it *exciting* is connecting it to the broader mathematical universe: formal verification backends, historical context, open problems, and collaborative exploration. Mathematics is fundamentally a social and creative endeavor. A tool that embraces that—that treats proof not as bureaucratic verification but as intellectual adventure—would be something I'd genuinely look forward to using.

---

## Final Status

The proof of √2 being irrational is **complete and verified**:
- 10 motes total
- All motes have status `:verified`
- DAG is valid with no schema or integrity errors

```
af check
{:valid? true, :mote-count 10, :schema-errors nil, :dag-errors nil}
```
