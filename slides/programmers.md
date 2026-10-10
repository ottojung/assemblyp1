---
theme: default
title: "AssemblyP1 for Programmers"
info: |
  Genome assembly, maximum likelihood, and how a multi-agent research
  system produced kernel-checked results.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# Would you trust an AI-discovered proof?

### Genome assembly, maximum likelihood, and the machine that checked the answer

<div class="pt-8 opacity-70">
AssemblyP1 · for programmers and research engineers
</div>

<div class="pt-10 text-sm opacity-60">
Two stories in ~20 minutes: a real mathematical result, and the engineering that checked it.
</div>

<HomeLink label="Choose another audience" />

<!--
Welcome. This talk is for programmers who have never used an AI agent, so the second half starts from zero: what an agent actually is, and how a team of them found, falsified, and kernel-checked a mathematical result. The first half is the result itself: a genome-assembly mystery with a concrete, surprising answer. Everything shown is either computed exactly or checked by a proof kernel — and the talk is honest about the difference between those two things.
-->

---
layout: default
---

# Roadmap

<div class="grid grid-cols-2 gap-10 pt-8">
<div>

### The science

1. A genome-assembly mystery
2. Two different questions
3. A counterexample, exactly computed
4. Right arithmetic, wrong definition
5. A definition weaker than the paper's

</div>
<div>

### The machine

6. What an agent is
7. One orchestrator, many workers
8. What Lean is
9. Why the checker can be trusted
10. What was verified — and the caveat

</div>
</div>

<div class="pt-8 opacity-70">
The two halves meet at one point: the mathematical claims are exactly the ones the machine is built to falsify.
</div>

---
layout: default
---

# The genome assembly mystery

Sequencing reads a circular genome in short, overlapping pieces.

```text
source:  A C G T T A C G A T
reads:   ACGTT   TTACG   ACGAT
```

<div class="pt-6 text-lg">
The <b>assembly problem</b>: infer the circular source from the fragments alone.
</div>

<div class="pt-4 text-sm opacity-70">
This is the computational core of every genome project — from bacterial genomes to the Human Genome Project.
</div>

<!--
Set the stage. The genome is a circular string over the alphabet A, C, G, T. A sequencer does not read it end to end; it produces many short reads of a fixed length L, each starting at a uniformly random position, read off the circle. The only data we ever get is the multiset of read strings — a type and a count for each distinct length-L window. The idealizations (circular, equal length, error-free, uniform starts) are deliberate: they make the information question crisp. They are not a claim about messy real data.
-->

---
layout: default
---

# Two different questions

<div class="grid grid-cols-2 gap-10 pt-6">
<div>

### Reconstruction

Can a candidate genome explain **every observed read**?

Structural: *which assemblies can spell the reads?*

</div>
<div>

### Maximum likelihood

Which candidate best explains the **observed read counts**?

$$
\arg\max_{W}\ \Pr(\text{reads} \mid W)
$$

Optimization: *which candidate scores highest on this sample?*

</div>
</div>

<div class="pt-8 text-lg text-amber-600">
A genome can be structurally consistent with the reads — and still not be the most likely explanation of their frequencies.
</div>

<!--
This distinction — structure versus frequency — is the central insight of the project. A 2016 paper (Shomorony, Kim, Courtade & Tse) gave conditions under which the reads contain enough structural information to reconstruct the genome, and left open whether those same conditions guarantee that the maximum-likelihood genome is the true genome. AssemblyP1 is what happens when you make that question precise and then check the answer in a proof kernel.
-->

---
layout: default
---

# The historical counterexample

The 2016 question, answered the hard way: with a concrete witness.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

truth `S = AAATAT` (length 6)

decoy `D = AAAAAT` (length 6)

reads of length `L = 3` (a read and its reverse complement are one class)

</div>
<div>

$$
\frac{\mathrm{Lik}(D)}{\mathrm{Lik}(S)} = 3
$$

the wrong genome is **exactly 3× as likely**

</div>
</div>

<div class="pt-6 text-lg">
Not a floating-point estimate: an exact rational, proved in Lean.
</div>

<!--
This is the project's historical witness, the first same-length counterexample. Both strings have length 6; reads have length 3; the molecule model identifies a read with its reverse complement, so ATA and TAT are the same molecule class. Sampled starts (0, 0, 1, 3, 5) on the truth give observed counts {AAA: 2, AAT: 1, ATA: 1, TAA: 1}. Under the exact read distribution, the decoy AAAAAT scores exactly 3 times the truth AAATAT; under the fixed-N binomial sampling model the ratio is 5. Both are kernel-checked in AssemblyP1/SameLengthSection62Counterexample.lean. The mechanism: the decoy produces the over-sampled read AAA from three start positions on its circle, so an unlucky sample that happens to contain extra AAA reads rewards the decoy. The sign of the reversal depends on the sampling model, not just on the two genomes — that is the point of the example.
-->

---
layout: default
---

# Right arithmetic, wrong definition

A predicate transcribing the paper's "bridged" condition was written **endpoint-wise** instead of as a **strict straddling** condition.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**What the code computed**

Every ratio was exact. The arithmetic was correct.

</div>
<div>

**What went wrong**

The definition was not the paper's. The kernel happily checked a theorem about the wrong thing.

</div>
</div>

<div class="pt-6 text-lg text-amber-600">
The bug manufactured a machine-checked "counterexample" — and a whole research branch chased the artifact.
</div>

<!--
This is the episode that justifies the talk's opening question. The paper's bridging condition says a repeat copy is bridged when a read extends past it on both sides — a strict straddling condition. The first formalization transcribed it endpoint-wise, which is weaker. With the wrong predicate, a "counterexample" appeared: a kernel-checked theorem, exact arithmetic, wrong definitions. It took an independent audit to notice that the phantom escape hypothesis was an artifact. The fix was a corrected predicate — bridgesCopy_length : BridgesCopy → e + 2 ≤ L — after which the phantom counterexample is refuted. Lesson: formalizing source semantics is research, not clerical work. A transcription bug can manufacture a theorem that is true but irrelevant. The definition is part of the claim.
-->

---
layout: default
---

# What an agent is

An agent is not a robot that "reasons". It is a **loop**:

```text
   ┌──────────┐  next action   ┌──────────┐
   │   LLM    │ ─────────────▶ │  tools   │
   │ proposes │                │ act      │
   └──────────┘                └────┬─────┘
        ▲                          │
        │        result            ▼
        └──────────────────── observe
```

<div class="grid grid-cols-3 gap-6 pt-6 text-sm">
<div>

**read** files, search code

</div>
<div>

**write** code, edit text

</div>
<div>

**shell** build, test, git

</div>
</div>

<div class="pt-6 text-lg">
No magic: a language model with a filesystem and a shell, iterating until the work is done.
</div>

<!--
For anyone who has not used an AI agent: there is no reasoning engine in the box. There is a language model that proposes a next action, a set of tools that can read and write files and run shell commands, and a loop that feeds the tool results back to the model. The model never touches your repository directly — it emits tool calls, the harness executes them, and the results come back as text. Everything the system can do, you can do by hand; the difference is speed and stamina. The interesting engineering question is not "how does it think" but "how do you keep a loop like this from going wrong" — which is the next two slides.
-->

---
layout: default
---

# One orchestrator, many workers

```text
      ┌───────────────────────────────────┐
      │  Board: issues · reviews · queue  │
      └─────────────────┬─────────────────┘
                        │ dispatch independent fronts
       ┌────────────────┼────────────────┐
       ▼                ▼                ▼
  ┌─────────┐     ┌─────────┐      ┌─────────┐
  │ Worker A│     │ Worker B│      │ Worker C│
  │ own     │     │ own     │      │ own     │
  │ branch  │     │ branch  │      │ branch  │
  └────┬────┘     └────┬────┘      └────┬────┘
       └────────────────┼────────────────┘
                        ▼
      ┌───────────────────────────────────┐
      │  Review → CI → merge             │
      └─────────────────┬─────────────────┘
                        ▼
              Proof checker (Lean)
```

<div class="pt-6 text-lg">
Parallelize exploration. <b>Serialize reconciliation.</b>
</div>

<!--
The coordination surface is a durable board — issues, comments, reviews — backed by content-addressed storage, so a fresh invocation can reconstruct the whole research graph from it rather than from chat history. The orchestrator decomposes broad questions into narrow research packets and dispatches independent fronts to workers. Every write-capable worker gets its own branch and worktree; no two writers share a branch. The expensive, serial part is reconciliation: merging partial results proposition by proposition, checking quantifiers, hypotheses, model versions, and tie semantics rather than trusting prose summaries. A worker's own summary is not independent verification of its result. The board, the branches, and the reviews are the memory; the agents are stateless.
-->

---
layout: default
---

# A definition weaker than the paper's

A late audit found the formal **coverage predicate** was weaker than the source's actual condition.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**What we formalized**

Coverage counted only the **sampled placements** of each observed read.

</div>
<div>

**What the paper says**

Coverage quantifies over **any matching occurrence** of an observed read string.

</div>
</div>

<div class="pt-6 text-lg">
The fix was <b>additive</b>: new predicates, new endpoints — and every original theorem preserved.
</div>

<!--
This is the second definitions-are-part-of-the-claim episode, and the constructive version. The paper's coverage condition asks whether every position of the genome is covered by some occurrence of some observed read string — any matching occurrence, not only the placements that happened to be sampled. The first formalization counted only sampled placements, which is strictly weaker. Rather than silently strengthening the old theorems, the project added the stronger historical predicates and theorem endpoints alongside the old ones, and kept both models first-class. An independent Python audit certifies the new witnesses. The lesson is the same as the bridging bug, from the other side: never delete a valid theorem to make a stronger-sounding claim. A weaker theorem you keep is a result; a stronger theorem you fake is a liability.
-->

---
layout: default
---

# What Lean is

**Propositions are types. Proofs are programs.**

```lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
```

<div class="grid grid-cols-3 gap-6 pt-6 text-sm">
<div>

`p ∧ q → q ∧ p` — the proposition, a **type**

</div>
<div>

`fun h => ⟨h.2, h.1⟩` — the proof, a **program**

</div>
<div>

the kernel checks the program has the type

</div>
</div>

<div class="pt-6 text-lg">
A proof you can run is a proof you can <b>check</b> — mechanically, every time.
</div>

<!--
Lean is a proof assistant built on the Curry-Howard correspondence: a proposition is a type, and a proof of it is a program (a term) of that type. The snippet proves that conjunction commutes. The proposition p ∧ q → q ∧ p is the type; the term fun h => ⟨h.2, h.1⟩ is the proof — given a proof h of p ∧ q, build a proof of q ∧ p from its two components, swapped. There is no appeal to intuition: the kernel type-checks the term against the type, and type checking is a small, mechanical procedure. This is why the project states its theorems in Lean: not because the machine found them, but because the machine can check them.
-->

---
layout: default
---

# Why the small kernel is trustworthy

Every proof term is checked by a **tiny kernel** — the only code that must be trusted.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Why to trust it**

- one small checker, not a large proof search
- every theorem replayed through it in CI
- axioms audited: only `propext`, `Classical.choice`, `Quot.sound`

</div>
<div>

**Where trust ends**

- axioms are **assumed**, not proved
- the kernel checks the **formal statement** — not whether the definitions match the biology

</div>
</div>

<div class="pt-6 text-lg text-amber-600">
A green CI job is not a proof. The kernel is the proof boundary — the model is still yours.
</div>

<!--
The trust argument is deliberately narrow. Lean's kernel is small enough to audit by eye, and it does exactly one thing: check that each proof term has the type its theorem claims. CI replays the entire library through the kernel and audits the axioms every theorem depends on — the project permits only the three standard axioms (propext, Classical.choice, Quot.sound) and no sorry, admit, or native_decide. But the kernel's guarantee is conditional: it certifies that the formal statement follows from the axioms. It cannot certify that the formal definitions match the paper's biology, or that the model matches real sequencing. That obligation — model fidelity — stays with the humans and the source audits. Trust the kernel for the proof. Audit the axioms. Own the model.
-->

---
layout: default
---

# What was verified — and the caveat

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Negative results**

- `AAATAT → AAAAAT`: exact ratio **3**
- `ATATACAC → ATACACAC`: exact ratio **3/2**
- `AAATT → AAAATT`: exact ratio **15625/11664**

the wrong genome wins — exactly

</div>
<div>

**Positive results**

- **Rigidity**: the truth's spectrum is the unique circulation — no strict same-length counterexample, for any `G`, `L`, alphabet
- **Population uniqueness**: the truth is always a maximizer; equality forces same length and rotation

</div>
</div>

<div class="pt-6 text-lg">
<b>Caveat:</b> at full overlap (consecutive windows share <code>L − 1</code> symbols), the optimum can be <b>disconnected</b> — the verified statements are about specific model readings, not all of sequencing.
</div>

<!--
Both directions are kernel-checked, and the boundary is explicit. Negative: three families of finite counterexamples where a wrong genome out-scores the truth — the historical AAATAT witness at exact ratio 3, the per-occurrence strengthening at 3/2, and the variable-length reversal at 15625/11664, with the amplification mechanism checked at M = 1, 2. Positive: rigidity says that under the right structural hypothesis the truth's read spectrum is the unique positive integer circulation of total G on the support graph, so no strict same-length counterexample exists at all; and the population theorem says that in the exact read distribution the truth is always a maximizer, with equality only at the same length up to cyclic rotation. The caveat matters: at full overlap, where consecutive windows of a circular molecule overlap in exactly L − 1 symbols, a genuine optimum of the flow optimizer need not be positive-support connected — the AAATAT witness again, at ratio 1280/243. The verified map is precise about where each statement holds. That precision is the result, not a limitation of it.
-->

---
layout: end
---

# Trust the check, not the claim.

<div class="pt-6 text-lg opacity-90">
Definitions are part of the claim. Verify your verifier.<br/>
Preserve failed routes. The kernel is the proof boundary — the model is yours.
</div>

<div class="pt-8 opacity-70">
A real math result, a real kernel check, and an honest account of the machine that produced them.
</div>

<HomeLink label="Choose another audience" />

<!--
Land the three ideas. First: definitions are part of the claim — two separate episodes (the bridging predicate, the coverage predicate) were caught only because the project treated formalization as research and audited its own predicates against the source. Second: verify your verifier — a broken predicate can manufacture or hide a result, so the pipeline is designed to falsify, and review re-executes rather than inherits. Third: the kernel is the proof boundary, not the whole truth — it certifies the formal statement from audited axioms, and model fidelity remains a human, documented obligation. If you remember one sentence: trust the check, not the claim.
-->

---
layout: default
---

# Where to look

<div class="text-sm">

**The endpoint theorem**

`AssemblyP1/Issue94Complete.lean` — `population_unique_ML`

**The finite witnesses**

`AssemblyP1/SameLengthSection62Counterexample.lean` · `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` · `AssemblyP1/OrientedVariableLengthSe62.lean`

**Rigidity**

`AssemblyP1/OrientedRigidity.lean`

**The engineering**

`.github/workflows/ci.yml` · `docs/research-orchestration.md`

</div>

<div class="pt-8 text-2xl">
Questions?
</div>

<!--
Pointers for afterwards. The endpoint theorem is population_unique_ML in AssemblyP1/Issue94Complete.lean: for an oriented circular truth that is primitive and P2 at read length L, every primitive P2 candidate of any length scores at most the truth in the population log-likelihood, with equality only at the same length up to cyclic rotation. The finite witnesses live in the three counterexample modules; rigidity lives in OrientedRigidity.lean. The engineering story — board, orchestration, CI, review — is documented under docs/research-orchestration.md and the CI workflow. Everything on these slides reproduces: the exact scripts are in scripts/, the Lean modules build with lake build, and the decks build with npm run build in this directory.
-->
