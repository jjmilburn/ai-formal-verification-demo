# The Verification Loop: How LLMs and Proof Checkers Are a Perfect Match

*A practical guide to AI-assisted formal verification, with runnable demos.*

---

## The Thesis

Martin Kleppmann recently [predicted](https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html) that AI will make formal verification go mainstream. His argument is elegant:

> "Rather than having humans review AI-generated code, I'd much rather have the AI prove to me that the code it has generated is correct."

Three forces are converging:

1. **Cost reduction**: LLMs can draft proofs, cutting verification cost from "23 lines of proof per line of code" (seL4) to something tractable
2. **Necessity**: We're generating code faster than we can review it—51% of GPT-3.5 generated C programs had vulnerabilities
3. **Synergy**: Proof checkers reject hallucinations. The LLM can retry until it gets a valid proof.

This isn't speculation. [Lean Copilot](https://arxiv.org/abs/2404.12534) automates 74% of proof steps. [Harmonic AI](https://harmonic.fun/) raised $120M building on this premise. The [FM-ALPACA paper](https://arxiv.org/abs/2501.16207) (ACL'25) benchmarked LLMs on formal verification across five languages.

This repository demonstrates the core pattern with runnable examples.

---

## The Verification Loop

The key insight: **LLM hallucinations don't matter if you have a checker**.

```
┌─────────────────────────────────────────────┐
│  1. LLM generates code/proof/spec           │
│         ↓                                   │
│  2. Verifier checks it                      │
│         ↓                                   │
│  3a. Valid → Verified (see caveats below)   │
│  3b. Invalid → Feed error back to LLM       │
│         ↓                                   │
│  4. LLM fixes based on error                │
│         ↓                                   │
│  (repeat until valid or max attempts)       │
└─────────────────────────────────────────────┘
```

This works because:
- Verifiers give **precise feedback** (not vague "looks wrong")
- LLMs are good at fixing code given specific errors
- The final result has formal guarantees—but what's guaranteed depends on the tool (see "Three Ways to Verify" below)

---

## Three Ways to Verify

We demonstrate the loop across three tools, each with different strengths **and different levels of assurance**:

| Tool | What It Verifies | Level of Assurance |
|------|------------------|-------------------|
| **Dafny** | Actual executable code | **Implementation** — the code you run is proven correct |
| **Lean4** | Mathematical theorems | **Theorems** — proves math facts, not code correctness |
| **TLA+** | Abstract specifications | **Design only** — proves the spec is correct, not any implementation |

**Important distinction**: Dafny verification is the most "complete"—it proves *the implementation itself* is correct. TLA+ only proves your *design* is correct; you could still introduce bugs when implementing that design in Python or Java. This is a meaningful gap.

### Dafny: Annotating Imperative Code

Dafny lets you write normal-looking code with pre/postconditions and loop invariants:

```dafny
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures index >= 0 ==> a[index] == key
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  // ... implementation with loop invariants
}
```

The LLM task: given unannotated code, add the annotations to make it verify.

**Why it works**: Dafny errors are specific ("loop invariant not maintained at line 12"), giving the LLM clear guidance.

### Lean4: Theorem Proving

Lean4 proves theorems using tactics:

```lean
theorem add_comm : ∀ a b : Nat, a + b = b + a := by
  intro a b
  omega
```

The LLM task: fill in the `sorry` placeholder with valid tactics.

**Why it works**: The type checker tells you exactly which goal remains unsolved.

### TLA+: Model Checking Specifications

TLA+ describes systems as state machines, then exhaustively checks properties:

```tla+
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")
```

The LLM task: generate a spec from natural language, fix it when TLC finds counterexamples.

**Why it works**: Counterexamples are concrete execution traces—the LLM can see exactly what went wrong.

**Caveat**: TLA+ verifies your *design*, not your *implementation*. When TLC says "no errors found," it means the abstract specification satisfies your properties. You still need to correctly implement that design in a real programming language—and that translation is where bugs often hide. TLA+ won't catch them.

---

## Grounding: The FM-ALPACA Paper

This project reproduces methods from ["From Informal to Formal"](https://arxiv.org/abs/2501.16207) (ACL'25):

**What they did**:
- Created 18k instruction-response pairs across Coq, Lean4, Dafny, ACSL, and TLA+
- Benchmarked 10 LLMs on six verification tasks
- Fine-tuned 7-8B models to match much larger models

**Key findings**:
- Fine-tuning on formal data improves general reasoning (not just verification)
- "Proof Generation" tasks (what we do here) have highest success rates
- External context significantly helps—don't ask the LLM to work from nothing

Our demos use Claude without fine-tuning, showing this works with off-the-shelf models.

---

## What This Means for You

### If you're an ML practitioner:

- This is a new application of LLMs with **objective success metrics**
- Verification feedback loops could train better reasoning models
- The FM-ALPACA fine-tuned models are [on HuggingFace](https://huggingface.co/fm-universe)

### If you work on safety-critical systems:

- AI-generated code is coming whether you like it or not
- Formal verification can provide strong safety guarantees—but only for what's actually verified (Dafny verifies implementations; TLA+ only verifies designs)
- Tools like [dafny-annotator](https://dafny.org/blog/2025/06/21/dafny-annotator/) make implementation verification practical today

### If you're formal-methods-curious:

- The LLM handles the tedious parts (writing invariants, finding tactics)
- You still need to write good specifications—that's the hard part
- But the barrier to entry just dropped dramatically

---

## Try It Yourself

### Quick Start

```bash
git clone https://github.com/yourusername/ai-formal-verification-demo
cd ai-formal-verification-demo
./setup.sh
jupyter notebook notebooks/
```

### What's Inside

```
notebooks/
├── 01-intro-to-verification.ipynb   # Background and setup
├── 02-dafny-demo.ipynb              # LLM adds Dafny annotations
├── 03-lean4-demo.ipynb              # LLM generates Lean proofs
├── 04-tlaplus-demo.ipynb            # LLM generates TLA+ specs
└── 05-comparison.ipynb              # Side-by-side evaluation

examples/
├── dafny/                           # Binary search, max array
├── lean/                            # Simple theorems
└── tlaplus/                         # Mutual exclusion, counters
```

### Dependencies

- Python 3.10+
- [Dafny](https://github.com/dafny-lang/dafny) (installed via setup.sh)
- [Lean4](https://leanprover.github.io/lean4/doc/) via elan
- [TLA+ tools](https://github.com/tlaplus/tlaplus)
- Claude API (uses Claude Code authentication)

---

## The Honest Caveats

**Specifications are still hard**. Kleppmann notes:

> "The specification remains the critical step. Writing a specification still requires careful expertise and thought."

The LLM helps you verify that code matches a spec—it doesn't write the spec for you.

**Design ≠ Implementation**. This is crucial: TLA+ and Lean verify *designs* and *theorems*, not running code. The seL4 microkernel required a separate proof that the C code faithfully implements the spec—that's a massive undertaking not covered here. Only Dafny in this repo verifies actual executable code.

**This isn't magic**. Some problems need multiple iterations. Complex invariants may stump the LLM. The tools have learning curves.

**But the economics changed**. What took "half a person-day per line" might now take a few API calls. That's a real improvement—just be clear-eyed about what you're actually proving.

---

## Further Reading

### Papers
- [FM-ALPACA: From Informal to Formal](https://arxiv.org/abs/2501.16207) - The benchmark paper
- [Lean Copilot](https://arxiv.org/abs/2404.12534) - LLM-assisted Lean proving
- [APOLLO](https://arxiv.org/abs/2505.05758) - State-of-the-art Lean automation
- [dafny-annotator](https://arxiv.org/html/2411.15143v1) - AI-assisted Dafny verification

### Blog Posts
- [AI will make formal verification go mainstream](https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html) - Kleppmann's prediction
- [Genefication](https://www.mydistributed.systems/2025/01/genefication.html) - Practical TLA+ workflow

### Tools & Resources
- [LeanDojo](https://leandojo.org/) - Lean + LLM integration
- [Harmonic AI](https://harmonic.fun/) - Startup building on Lean4
- [FM-ALPACA models](https://huggingface.co/fm-universe) - Fine-tuned models on HuggingFace

---

## License

MIT. Use this code however you want.

---

*Written for [unalarming.com](https://unalarming.com) — making academic findings practical for engineers.*
