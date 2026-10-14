---
theme: default
title: "AssemblyP1 for Programmers"
info: |
  Genome assembly, maximum likelihood, and a research investigation.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# The Most Likely Genome

### Genome assembly, probability, and mathematical verification

**AssemblyP1** · A research investigation

<HomeLink label="Choose another audience" />

<!--
This is not an algorithm lecture or a progress report about software agents.
Begin with the scientific problem and develop the research question naturally.
-->

---

# How can we reconstruct a genome?

A genome is a very long string of DNA letters.

Sequencing does not hand us that string. It gives us **many short fragments**, called *reads*, sampled from different positions.

For example, a circular genome `ACGTA` has these length-3 fragments:

```text
ACG   CGT   GTA   TAA   AAC
```

**We know the fragments, but not where each one came from.**

The assembly problem is to infer the original sequence.

<!--
The circular toy model removes distracting end effects.
We assume error-free oriented reads; real sequencing is more complicated.
-->

---

# What makes assembly difficult?

DNA contains **repeated substrings**.

```text
... G [ ACGA ] T ...
... C [ ACGA ] A ...
```

A short read containing only `ACGA` cannot tell us which copy was sampled.

A longer read containing the **flanking context** can distinguish them.

This is why read length, overlap, and *bridging repeats* matter.

<!--
Bridging means the read extends beyond a particular repeat copy on both sides.
The takeaway is information content, not graph implementation.
-->


---

# Assembly begins with overlaps

These reads came in an unknown order. But adjacent reads can agree on their last and first two letters:

```text
ACG → CGT → GTA → TAA → AAC
  ↑                       ↓
  └───────────←───────────┘
```

Following those overlaps spells the circular genome `ACGTA`.

**Assembly turns local matches into a global sequence.**

<!--
Point to ACG -> CGT: the CG suffix matches the CG prefix.
The circular cycle reuses each of the five length-3 windows once.
Explain in words; no graph theory prerequisites. Repeated DNA can make one
read consistent with several neighbors — the next slides show why that matters.
-->

---

# Every genome predicts a distribution

In our idealized model, each read begins at a **uniformly random position** on the circular genome.

If `AAATT` is the genome, just one of its five positions yields the length-3 read `AAA`.

If `AAAATT` is the genome, two of its six positions yield `AAA`.

$$
P_G(w)=\frac{\text{starts yielding }w}{G}
\qquad
P(\texttt{AAA}\mid\texttt{AAATT})=\tfrac15
\quad
P(\texttt{AAA}\mid\texttt{AAAATT})=\tfrac26
$$

**The two candidates predict different sampling frequencies.**

<!--
Independent, error-free, oriented fixed-length reads. The exact MB09 molecule
and approximation models are separate later branches of the research; this is
the simplest generative illustration.
-->

---

# Reads → a probability for each genome

Six length-3 reads, independently sampled from the true genome `AAATT`:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

Multiply each read's probability:

$$
P(R\mid S)=(1/5)^6=\tfrac1{15625}
\qquad
P(R\mid D)=(2/6)^2(1/6)^4=\tfrac1{11664}
$$

The **wrong genome** scores about **34% higher** for this sample.

**MAP** — choose the candidate with the largest posterior probability. With **equal priors**, MAP is maximum likelihood. MAP minimizes the *average* error over samples: **optimal on average, not infallible**.

<!--
Likelihood ratio (D/S) = 15625/11664 ≈ 1.3396; count the windows explicitly.
With equal priors, Bayes gives the competitor posterior 15625/(15625+11664)
≈ 57.3% — still the decision that minimizes conditional error given just this
model and these reads; the truth is known only because we built the experiment.
Optimality is for prior-averaged 0-1 recovery risk, given the same model, prior
and candidate universe — not a pointwise guarantee for every true genome and
finite sample. The finite decision theorem (randomization cannot beat MAP;
extra observations cannot hurt under consistent marginals) is kernel-checked
in AssemblyP1/FiniteBayesDecision.lean.
-->

---

# The question I chose to investigate

In 2016, Shomorony, Kim, Courtade, and Tse introduced **Not-So-Greedy**. Instead of committing to each largest-looking overlap — which can collapse repeats — it builds a sparse network of plausible read connections, then reconstructs a sequence.

Their theorem guarantees recovery of the true circular genome under precise **coverage and repeat-bridging** conditions. They ended their paper with an open question:

$$
\text{NSG's success conditions}
\quad\stackrel{?}{\Longrightarrow}\quad
S\in\operatorname*{arg\,max}_D P(R\mid D)
$$

**Do the algorithm's success conditions also make the truth a maximum-likelihood genome?**

<!--
Shomorony et al., "Information-optimal genome assembly via sparse read-overlap
graphs", Bioinformatics 2016, https://doi.org/10.1093/bioinformatics/btw450
Theorem 1 and supplementary conditions. The antecedent is the *algorithm's*
success conditions, not merely an abstract claim that reads contain information.
The symbols are schematic; actual candidate predicates and read conventions
vary across paper interpretations.
-->

---

# A strict finite counterexample

The 2016 question, answered the hard way: with a concrete witness.

truth `S = AAATAT` (length 6) · decoy `D = AAAAAT` (length 6) · reads of length `L = 3`, a read identified with its reverse complement

$$
\frac{\mathrm{Lik}(D)}{\mathrm{Lik}(S)} = 3
$$

Under the source's **same-length molecule model**, with **bridging conditions holding**, the wrong genome is **exactly 3× as likely** — an exact rational, **proved in Lean**, not a floating-point estimate.

Whole **families** of finite counterexamples follow — not one unlucky dataset.

<!--
The project's historical witness, the first same-length counterexample. Sampled
starts (0, 0, 1, 3, 5) on the truth give observed counts {AAA: 2, AAT: 1,
ATA: 1, TAA: 1}; under the exact read distribution the decoy AAAAAT scores
exactly 3× the truth AAATAT (fixed-N binomial sampling: ratio 5). Both are
kernel-checked in AssemblyP1/SameLengthSection62Counterexample.lean.
Strengthenings: per-occurrence model ratio 3/2
(PerOccurrenceSameLengthCounterexample.lean); variable-length reversal ratio
15625/11664 (OrientedVariableLengthSe62). Mechanism: the decoy produces the
over-sampled read AAA from three start positions on its circle, so an unlucky
sample containing extra AAA reads rewards the decoy.
-->

---

# Strong positive theorems

- **Rigidity**: under structural hypotheses, the truth's spectrum is the unique circulation — no strict same-length counterexample, for any `G`, `L`, alphabet
- **Population uniqueness**: for a truth with mild non-repetition structure (primitive, P2), every admissible candidate scores at most the truth — equality forces same length and rotation
- **Plus**: MAP decision optimality and population Gibbs theorems — a growing portfolio, every result kernel-checked

**Caveat:** at full overlap the optimum can be disconnected — each verified statement is about a specific model reading, not all of sequencing.

<!--
Rigidity: AssemblyP1/OrientedRigidity.lean — under the right structural
hypothesis the truth's read spectrum is the unique positive integer
circulation of total G on the support graph. Population:
Issue94Complete.population_unique_ML (AssemblyP1/Issue94Complete.lean) assumes
the truth is primitive and P2 at read length L and quantifies over the
admissible candidate class (AdmClass, PopulationUniqueness.lean); the Gibbs
layer (PopulationGibbs.lean) proves always-maximality and equality of
distributions — rotation uniqueness is exactly what the primitive and P2
hypotheses buy. MAP optimality: FiniteBayesDecision.lean. Full-overlap
caveat: Section62FullOverlapDisconnected.lean — at full overlap a genuine
optimum need not be positive-support connected (the AAATAT witness again, at
ratio 1280/243). The verified map is precise about where each statement holds;
that precision is the result, not a limitation of it.
-->

---

# Agents were present from day one

On September 17, I began AssemblyP1 with **two things already in place**: a real open question from the genome-assembly literature, and a research method — cooperating AI agents, durable work, adaptive orchestration, Lean as the verification boundary.

An **agent** is not a robot that reasons. It is a loop:

```text
   ┌──────────┐  next action   ┌──────────┐
   │   LLM    │ ─────────────▶ │  tools   │
   │ proposes │                │ act      │
   └──────────┘                └────┬─────┘
        ▲                          │
        │        result            ▼
        └──────────────────── observe
```

The system wasn't added after the mathematics became complicated — I designed the project from the outset to conduct mathematical research by directing it.

<!--
Primary evidence: docs/intent-records/project.md, intent records dated
2026/09/17. The initial repository commits already seed Lean, agent
instructions, research orchestration and durable intent records. This was the
methodology at founding, not a post-hoc workaround. The model never touches
the repository directly — it emits tool calls, the harness executes them, and
the results come back as text. Everything the system can do, you can do by
hand; the difference is speed and stamina.
-->

---

# The central work: choosing directions

The important decision was repeatedly **what to investigate next** — counterexamples, positive theorems, why the failures happen. Each result changed the next question.

```text
   ┌───────────────────────────────┐
   │  Board: issues · reviews      │
   └──────────────┬────────────────┘
                  ↓
   Orchestrator dispatches independent fronts
                  ↓
   ┌────────┬────────┬────────┐
   │Worker A│Worker B│Worker C│  isolated branches
   └────────┴────────┴────────┘
                  ↓
        Review → CI → merge
                  ↓
          Lean kernel check
```

**Parallelize exploration. Serialize reconciliation.**

<!--
The coordination surface is a durable board — issues, comments, reviews — so a
fresh invocation can reconstruct the whole research graph from it rather than
from chat history. The orchestrator decomposes broad questions into narrow
research packets; every write-capable worker gets its own branch and worktree.
The expensive, serial part is reconciliation: merging partial results
proposition by proposition, checking quantifiers, hypotheses, model versions
and tie semantics rather than trusting prose summaries. A worker's own summary
is not independent verification of its result. The board, the branches, and the
reviews are the memory; the agents are stateless.
-->

---

# Two incomparable definitions of coverage

A late audit found the formal **coverage predicate** did not match the source's actual condition.

**Old model** — sampled starts cover every genomic **base**; adjacent reads need not overlap.

**Historical model** — for every interval of length `L−1`, an **observed read string** must match at a start in that interval, possibly at a position never sampled.

**Neither coverage predicate implies the other.** Earlier, a bridging predicate was transcribed endpoint-wise instead of as strict straddling — exact arithmetic, wrong definition, and a phantom "counterexample" that took an independent audit to expose.

The fix was **additive**: separate source-literal endpoints, old results preserved.

<!--
Predicate definitions: AssemblyP1/HistoricalCovers.lean and
SourceFaithfulIs.lean; kernel-checked incomparability regressions in
HistoricalCoverageSameLengthWitnesses.lean. The historical model saturates
matching repeat occurrences — weaker in that dimension — but requires a read
START witness, which the old base-coverage model does not. The bridging bug:
the paper's condition is strict straddling; the first formalization was
endpoint-wise, manufacturing a machine-checked phantom counterexample until an
independent audit exposed it. Lesson: a weaker theorem you keep is a result; a
stronger theorem you fake is a liability.
-->

---

# What Lean is — and why the kernel can be trusted

**Propositions are types. Proofs are programs.**

```lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
```

A tiny **kernel** checks every proof term — the only code that must be trusted. CI replays all theorems through it and audits the axioms: Lean's three standard ones, `propext`, `Classical.choice`, `Quot_sound`.

**Where trust ends:** axioms are assumed, not proved; the kernel checks the *formal statement* — not whether the definitions match the biology.

<!--
Curry-Howard correspondence: the proposition p ∧ q → q ∧ p is the type; the
term fun h => ⟨h.2, h.1⟩ is the proof — given a proof h of p ∧ q, build a
proof of q ∧ p from its two components, swapped. The kernel type-checks the
term against the type; type checking is a small, mechanical procedure. The
project permits only the three standard axioms and no sorry/admit. Model
fidelity stays with the humans and the source audits: trust the kernel for
the proof, audit the axioms, own the model.
-->

---

# Trust the check, not the claim.

We started with a question from 2016: **do Not-So-Greedy's reconstruction conditions also make the true genome a maximum-likelihood genome?**

**We settled the concrete source-supported finite versions** — strict counterexamples at exact ratios, strong positive theorems, both kernel-checked — through human-directed, parallel AI exploration with Lean as the proof boundary.

<HomeLink label="Choose another audience" />

<!--
Definitions are part of the claim — two separate episodes (the bridging
predicate, the coverage predicate) were caught only because the project
treated formalization as research and audited its own predicates against the
source. Verify your verifier: a broken predicate can manufacture or hide a
result, so the pipeline is designed to falsify, and review re-executes rather
than inherits. The kernel is the proof boundary, not the whole truth — it
certifies the formal statement from audited axioms, and model fidelity remains
a human, documented obligation. The initial 2016 finite question is settled
across determinate source-supported interpretations; general characterization
and sample-complexity directions remain distinct new research questions.
-->
