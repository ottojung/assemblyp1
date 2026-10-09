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

# When Reconstructible Does Not Mean Most Likely

### Genome assembly, maximum likelihood, and a multi-agent research system

<div class="pt-8 opacity-70">
AssemblyP1 · for programmers and research engineers
</div>

<div class="pt-10 text-sm opacity-60">
Two stories: a real mathematical result, and the engineering that checked it.
</div>

<HomeLink label="Choose another audience" />

<!--
Two audiences share this site. This deck is the programmers' path: the math
result *plus* the orchestration, Lean, CI and review story. The biologists'
path tells the same science for a domain audience.
-->

---
layout: default
---

# Two different questions

<div class="grid grid-cols-2 gap-10 pt-6">
<div>

### Reconstruction

Can we recover the source string from overlapping pieces?

```text
source:  A C G T T A C G A T
reads:   ACGTT   TTACG   ACGAT
```

Structural: *which assemblies can spell the observed reads?*

</div>
<div>

### Maximum likelihood

Which candidate genome best explains the **observed read counts**?

$$
\arg\max_{W}\ \Pr(\text{reads} \mid W)
$$

Optimization: *which candidate scores highest on this sample?*

</div>
</div>

<div class="pt-8 text-lg">
A 2016 paper asked whether good <b>reconstruction</b> conditions guarantee that the
<b>maximum-likelihood</b> genome is the true genome. This deck is about what happens when
you make that question precise — and then check the answer in a kernel.
</div>

---
layout: default
---

# Roadmap

<div class="grid grid-cols-2 gap-10 pt-8">
<div>

### The science

1. A circular genome and its reads
2. The overlap-support graph
3. Repeat ambiguity and bridging
4. Rigidity: when the spectrum is forced
5. A finite likelihood reversal
6. Population ML and uniqueness

</div>
<div>

### The engineering

1. A research graph, not a task list
2. Board + orchestrator + workers
3. Job transport and isolated branches
4. Search → exact arithmetic → Lean
5. Independent review and CI
6. Errors, refutations, and lessons

</div>
</div>

<div class="pt-8 opacity-70">
The two halves are connected: the mathematical claims are exactly the ones the
engineering pipeline is built to falsify, compute, and finally kernel-check.
</div>

---
layout: section
---

# Part I · The science

A circular genome, short reads, and the gap between spelling and scoring.

---
layout: default
---

# The model in one slide

- The genome is a **circular** string `S` of length `G` over an alphabet (DNA: `A C G T`).
- Sequencing draws `N` **error-free reads** of a fixed length `L`.
- Each read starts at a uniformly random position and is read off `S` cyclically.
- Reads are the only data we get.

<div class="pt-6 text-lg">
The observable object is the <b>multiset of read strings</b> — a type and a count for each
distinct length-<code>L</code> window. Everything downstream is a statement about what that
multiset can and cannot reveal.
</div>

<div class="pt-6 text-sm opacity-70">
Idealizations are deliberate: circular, equal read length, error-free, uniform starts.
They make the information question crisp; they are not a claim about messy real data.
</div>

---
layout: default
---

# Reads become a graph

Each read of length `L` is an edge from its `(L-1)`-prefix to its `(L-1)`-suffix.
Shared pieces merge. A walk spells a candidate genome.

```text
   AC ──ACG──▶ CG ──CGT──▶ GT ──GTT──▶ TT ──TTA──▶ TA ──TAC──▶ AC
        └──────────── the walk AC→CG→GT→TT→TA→AC spells ACGTTACGTA ────────────┘
```

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Vertices** are distinct `(L-1)`-mers. **Edges** are distinct `L`-mers.

The **multiplicity** `A(w)` of edge `w` is how many times the read type `w` was observed.

</div>
<div>

Two different things live here:

- **support** — *which* read types exist (structure)
- **multiplicity** — *how many* copies were seen (frequencies)

</div>
</div>

---
layout: default
---

# Repeats are structural ambiguity

```text
    ... A [ C G C G ] T ...
    ... G [ C G C G ] C ...
```

A read entirely inside the repeated block cannot tell which copy it came from.
The overlap graph gets a **fork**: a vertex with two ways in and two ways out.

<div class="pt-6 text-lg text-amber-600">
This is ambiguity in the data, not a bug in any one assembler.
The information to separate the copies may simply not be present.
</div>

---
layout: default
---

# Bridging conditions

The 2016 paper rules out the worst repeat configurations. Two clauses matter here:

<div class="pt-4">

1. **Triple repeats** must be short relative to the read length.
2. **Interleaved repeat pairs** must be short in at least one member.

</div>

A repeat copy is **bridged** when a read extends past it on both sides.

<div class="pt-6 text-lg">
If these conditions hold, the paper's construction recovers the true circular sequence
<b>up to cyclic shift</b>. That is a statement about <i>structure</i>.
</div>

<div class="pt-6 text-sm opacity-70">
A precise formal predicate for "the source's coverage condition" is a research object in
its own right; a subtle version of it becomes an important episode later in this deck.
</div>

---
layout: default
---

# The support graph and rigidity

Take the truth `S`. Build the graph whose

- **vertices** are the distinct `(L-1)`-windows of `S`,
- **edges** are the distinct `L`-windows `w` in the read support,
- **edge multiplicity** is the observed count `A(w)`.

<div class="pt-4 text-lg">
If no `(L-1)`-window occurs too often, then the truth's spectrum is the
<b>unique positive integer circulation of total G</b> on that graph.
</div>

<div class="pt-4">
Kernel-checked core: <code>AssemblyP1.OrientedRigidity.unique_positive_circulation</code> and
the word-level adapter <code>rigidity_same_spectrum</code>. The cap hypothesis is exactly what
the paper's bridging condition supplies.
</div>

<div class="pt-4 text-sm opacity-70">
A "circulation" is a flow that conserves at every vertex. Positivity plus a throughput cap
leaves no room for a second solution.
</div>

---
layout: default
---

# What rigidity buys you

If the spectrum is forced, then any same-length candidate that can spell the reads has
**exactly the truth's spectrum**. Every likelihood ratio is exactly `1`.

<div class="pt-6 text-2xl text-center">
no strict same-length counterexample — for any G, L, alphabet
</div>

<div class="pt-6">
So where do counterexamples come from? Two places:

- **change the model** (candidate length, strand convention, coverage predicate), or
- **finite sampling** (the observed counts are an unlucky draw).

</div>

<div class="pt-6 text-sm opacity-70">
Kernel-checked corollary surface: <code>paper/sections/04-finite-results.tex</code>,
<code>cor:same-length-zero</code>.
</div>

---
layout: default
---

# An explicit finite likelihood reversal

Oriented reads, `L = 3`, and a candidate of a **different length**.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

truth `S = AAATT` (length 5)

decoy `D = AAAATT` (length 6)

Sample all true starts, then observe **one extra** `AAA`.

</div>
<div>

Candidate-intrinsic exact ratio:

$$
\frac{\mathrm{Lik}(D)}{\mathrm{Lik}(S)} = \frac{15625}{11664} > 1
$$

**the decoy wins**

</div>
</div>

<div class="pt-6 text-lg text-amber-600">
The sign depends on the sampling model, not just the two genomes.
</div>

---
layout: default
---

# The sign can flip

Same two strings, two objectives.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Full-start sample** (`n = 5`, no skew)

$$
\frac{\mathrm{Lik}(D)}{\mathrm{Lik}(S)} = \frac{3125}{3888} < 1
$$

truth wins

</div>
<div>

**Fixed-`N` binomial** (`N = 5`)

$$
\frac{81}{64} > 1
$$

decoy wins

</div>
</div>

<div class="pt-6">
The ratio amplifies as more copies of the repeat are observed:
exact ratio `(3125/3888)·(5/3)^M`, binomial `(81/128)·2^M`.
</div>

<div class="pt-4 text-sm opacity-70">
Kernel-checked instances at `M = 1, 2`:
<code>AssemblyP1/OrientedVariableLengthSe62.lean</code>.
A finite witness is a statement about the model, not about real sequencing.
</div>

---
layout: default
---

# Same-length counterexamples exist too

Rigidity needs the *right* structural hypothesis. Weaken the model and same-length
counterexamples appear.

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Molecule / reverse-complement model**

`S = AAATAT` → `D = AAAAAT`, `L = 3`

exact ratio `3`, fixed-`N` binomial ratio `5`

</div>
<div>

**Per-occurrence strengthening**

`S = ATATACAC` → `D = ATACACAC`, `L = 3`

exact ratio `3/2`, binomial ratio `9/5`

</div>
</div>

<div class="pt-6 text-sm">
Kernel-checked: <code>SameLengthSection62Counterexample.lean</code>,
<code>PerOccurrenceSameLengthCounterexample.lean</code>.
Both competitors carry genuine §6.2 flow certificates — this is a model question, not a bug.
</div>

---
layout: default
---

# So the answer depends on the model

The project catalogued the plausible readings of the 2016 sentence as a matrix.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Eleven negative rows**

nine kernel-checked witnesses, two exact-arithmetic reproductions.

</div>
<div>

**Four positive rows**

including a kernel-checked same-length maximizer and rotation-uniqueness result.

</div>
</div>

<div class="pt-6 text-lg">
No single determinate, source-supported reading of the finite question remains open.
But "which reading is <i>the</i> one" is a source question, and we treat it as one.
</div>

<div class="pt-4 text-sm opacity-70">
Register: <code>docs/source-notes/interpretation-matrix-217.md</code>.
The matrix is qualification material — not the headline.
</div>

---
layout: default
---

# Population ML removes the sampling accident

Replace one finite draw by its exact read **distribution**.

<div class="pt-6">
For a candidate `W`, let `p_W(w)` be the probability that a uniformly placed length-`L`
read equals `w`. The population log-likelihood is
`Σ_w x(w) log p_W(w)`.
</div>

<div class="pt-6 text-xl text-center">
the truth is always a maximizer (Gibbs / KL)
</div>

<div class="pt-6">
That inequality is generic statistics. The real question is <b>uniqueness</b>:
which other candidates tie the truth exactly?
</div>

---
layout: default
---

# Uniqueness is the hard combinatorics

Two hypotheses do the work.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

### Primitive

`S` is **not** a whole-genome repetition `U·U·…·U`.

A periodic genome is inherently ambiguous up to its period.

</div>
<div>

### P2 / Ukkonen-admissible

No long triple repeat and no long interleaved repeat pair at read length `L`.

This is the paper's structural condition, read at the right threshold.

</div>
</div>

<div class="pt-6 text-sm">
Definitions: <code>IsPrimitive</code> (<code>PopulationReduction.lean</code>),
<code>P2</code> (<code>P2.lean</code>), rotation equivalence
<code>RotEquiv</code>. The alignment `P2 → Ukkonen` is itself kernel-checked
(<code>P2.imp_Ukkonen</code>).
</div>

---
layout: default
---

# The kernel-checked population theorem

<div class="text-sm">

**`AssemblyP1.Issue94Complete.population_unique_ML`**

For an oriented circular truth `S`, with `0 < G`, `1 < L`, `S` primitive and `P2` at
read length `L`, and for **every** candidate length `K > 0` and **every** primitive `P2`
candidate `W`:

1. `PopLogLik(W) ≤ PopLogLik(S)`;
2. equality forces `K = G` and `W` a cyclic rotation of `S`.

</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**No external premise.**

The complete-spectrum step that used to be imported from
Bresler–Bresler–Tse is discharged **internally**.

</div>
<div>

**Axioms only**

`propext`, `Classical.choice`, `Quot.sound`.

No `sorry`, no `admit`, no `native_decide`.

</div>
</div>

---
layout: default
---

# What the theorem does *not* say

<div class="pt-4 text-lg">

- It is about the **oriented** model. Molecule / doubled-strand readings are separate rows.
- It is a **population** statement, not a guarantee for finite noisy reads.
- It does **not** decide which historical reading of the 2016 sentence is intended.
- A kernel check certifies the formal statement. Matching it to biology is a separate obligation.

</div>

<div class="pt-8 text-xl text-center text-amber-600">
A green CI job is not a proof. The kernel checking the theorem is the proof boundary —
and even that does not certify the modeling choices.
</div>

---
layout: section
---

# Part II · The engineering

How a multi-agent research system found, falsified, checked, and integrated these results.

---
layout: default
---

# The problem shape

This was not a task list. It was a **research graph**.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

### Genuinely parallel

- distinct proof routes for one lemma
- independent counterexample searches
- source/model audits
- independent re-derivation of a ratio

</div>
<div>

### Genuinely sequential

- reconciling partial results proposition-by-proposition
- a single endpoint theorem that imports many fronts
- merge conflicts in one aggregator file
- final review and integration

</div>
</div>

<div class="pt-6 text-lg">
Scheduling independent fronts is cheap. <b>Reconciliation</b> is the expensive,
serial part — and it is where correctness actually comes from.
</div>

---
layout: default
---

# Architecture at a glance

```text
        ┌─────────────────────────────────────────────────────────┐
        │  Durable board: issues, comments, reviews, queue, feed  │
        └───────────────┬─────────────────────────────────────────┘
                        │ read state / post verdicts
                        ▼
        ┌─────────────────────────────────────────────────────────┐
        │  Orchestrator: decompose into research packets,          │
        │  dispatch independent fronts, reconcile, review, merge   │
        └───────────────┬─────────────────────────────────────────┘
                        │ enqueue jobs
                        ▼
   ┌──────────────┐   ┌──────────────┐   ┌──────────────┐
   │  Worker A     │   │  Worker B     │   │  Worker C     │
   │  branch/wt    │   │  branch/wt    │   │  branch/wt    │
   └──────┬───────┘   └──────┬───────┘   └──────┬───────┘
          │ push             │ push             │ push
          ▼                  ▼                  ▼
   ┌─────────────────────────────────────────────────────────┐
   │  Git + CI: PR review, lake build, kernel replay, audit   │
   └───────────────┬─────────────────────────────────────────┘
                   ▼
        Lean + Mathlib kernel  ← the proof-acceptance boundary
```

---
layout: default
---

# The durable coordination surface

**Antonina** is a signed coordination board, backed by content-addressed storage.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

- **issues** with a priority queue
- **comments** as append-only evidence
- **reviews** bound to one exact commit
- an activity **feed**
- **resources** (host + path) and execution **targets**

</div>
<div>

Every mutation is a signed operation in a hash-linked log.

The board is the recovery surface: a fresh invocation can reconstruct the whole
research graph from it, not from chat history.

</div>
</div>

<div class="pt-6 text-sm opacity-70">
A `request-changes` review blocks closing until an approval names a commit that no
`request-changes` named. Review is a durable object, not a comment thread.
</div>

---
layout: default
---

# The orchestrator: topology, not load

The scheduler reasons about the **logical work graph**, not about machines.

<div class="pt-4 text-lg">
Dispatch every independent front that has positive marginal value.
The only valid reasons to hold back are topological: an unfinished predecessor,
a duplicate live owner, or unavoidable sequential overlap.
</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Good reasons to parallelize**

- two incompatible proof routes
- an independent audit of a claimed result
- a bounded search that could kill a route early

</div>
<div>

**Bad reasons**

- "the host looks busy"
- RAM/CPU estimates as scheduling policy
- a fixed agent count treated as a quota

</div>
</div>

---
layout: default
---

# Research packets

Work is delegated as **narrow packets**, not vague assignments. Each packet states:

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

- objective
- permitted definitions and context
- explicit **non-goals**
- required evidence
- deliverable and stop conditions
- handoff format

</div>
<div>

<div class="pt-4 text-lg">
Workers attack the packet. They do not redefine it to make it easy.
</div>

<div class="pt-6 text-sm opacity-70">
One project kept a steady-state pool of five independent AssemblyP1 fronts —
a saturation target, not a quota, and never a reason to invent low-value work.
</div>

</div>
</div>

---
layout: default
---

# Execution: jobs, leases, no replay

Long-running work (Lean builds, searches) is dispatched as **jobs** to remote hosts
through a queue.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

- a job is `pending → running → succeeded | failed`
- claiming uses a lease with a heartbeat
- a **stale lease is marked failed, never re-executed**
- jobs are routed by an explicit server identity

</div>
<div>

<div class="text-lg">
"No re-execution" is a safety property: a job may have already pushed a commit or
deployed something. Replaying it would duplicate side effects.
</div>

<div class="pt-4 text-sm opacity-70">
The job protocol is versioned and fails closed: a worker only serves the version it
understands, and lower-version pending work is not silently run.
</div>

</div>
</div>

---
layout: default
---

# Worker isolation

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

Every write-capable worker gets:

- its own **branch** (`agent/board-NNN-topic`)
- its own **worktree** / directory
- its own agent session

No two writers share a branch. Integration targets `main` directly.

</div>
<div>

The orchestrator reviews the diff independently and may merge once the claims are
verified at the level they claim.

<div class="pt-6 text-sm opacity-70">
A worker's own summary is not independent verification of its result. Agreement
among agents does not promote a claim to a stronger evidence class.
</div>

</div>
</div>

---
layout: default
---

# The research loop is a build pipeline

```text
 source fact ──▶ formal model ──▶ bounded search ──▶ candidate result
      ▲                                                    │
      │                                                    ▼
      └──────────── reconcile ◀── independent audit ◀── exact arithmetic
                                   │
                                   ▼
                         kernel-checked theorem
```

<div class="pt-6 text-lg">
Each arrow is a place a claim can <b>die</b>. That is the point: the pipeline is
designed to falsify, not to confirm.
</div>

---
layout: default
---

# Evidence classes are not interchangeable

<div class="pt-2">

| Class | What it gives you |
| --- | --- |
| **Source fact** | a cited primary source with a recoverable location |
| **Modeling decision** | a deliberate, documented interpretation |
| **Conjecture** | believed useful; not proved |
| **Computational evidence** | a bounded search with explicit scope |
| **Mathematical proof** | a general implication from stated assumptions |
| **Kernel-checked result** | a Lean theorem with no `sorry`/`admit`/new axiom |

</div>

<div class="pt-6 text-amber-600">
Never promote a result because several workers agree, because it ranks highly, or
because it survived many failed attempts to falsify it.
</div>

---
layout: default
---

# Case study A · search → exact arithmetic → Lean

The finite reversal `S = AAATT`, `D = AAAATT`.

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**1. Bounded search** found the strings and the qualitative reversal.

Evidence, not proof — the search scope is finite.

</div>
<div>

**2. Exact-rational script** re-derived every ratio with `Fraction`, removing
floating-point doubt for that finite instance.

</div>
</div>

<div class="pt-6 text-lg">
<b>3. Lean</b> then kernel-checked the formal statement and the arithmetic:
<code>exact_ratio1 : exactLik obs1 dD 6 / exactLik obs1 dS 5 = 15625 / 11664</code>.
</div>

<div class="pt-4 text-sm opacity-70">
File: <code>AssemblyP1/OrientedVariableLengthSe62.lean</code>. The exact script and the
Lean proof are independent: they could disagree, and that is the point.
</div>

---
layout: default
---

# Case study B · internalize the external theorem

The population theorem used to rest on an **external** complete-spectrum result
(Bresler–Bresler–Tse).

<div class="pt-4 text-lg">
A long research front rebuilt that step from scratch — a concrete component
antiderivative construction — and discharged it inside the kernel.
</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Before**

`population_unique_ML_up_to_rotation` carried an explicit
`EulerianianCycleObstruction` premise (the BBT input).

</div>
<div>

**After**

`population_unique_ML` has no external premise. The predecessor is kept for the
audit trail and superseded.

</div>
</div>

<div class="pt-4 text-sm opacity-70">
Endpoint: <code>AssemblyP1/Issue94Complete.lean</code>. This is the payoff of parallel
proof exploration: several routes to one lemma, then a kernel-checked winner.
</div>

---
layout: default
---

# Case study C · a false lemma, caught

One front registered a module that turned the build red.

<div class="pt-4">
The claimed lemma was

```text
window E i = window S i        -- FALSE
```

and it was **refuted** by a kernel-checked probe at `G = 4`, `L = 3`, `S = 0101`.
The true relation shifts by `G - k`, not `k`.
</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Lesson 1**

A red build is a gift. A *green* build around a false intermediate lemma is the
dangerous case.

</div>
<div>

**Lesson 2**

The fix was not mechanical: the statement had to change, so the module was
**quarantined** and re-authored, not patched.

</div>
</div>

<div class="pt-4 text-sm opacity-70">
Commits <code>4fe3606</code> (red) → <code>a91a01e</code> (repaired, green).
</div>

---
layout: default
---

# Case study D · a source-semantics bug

A predicate transcribing the paper's "bridged" condition was written endpoint-wise
instead of as a strict straddling condition.

<div class="pt-4 text-lg">
It produced a kernel-checked "counterexample" and a phantom escape hypothesis — a
whole research branch chasing an artifact.
</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**The fix**

The corrected predicate yields
`bridgesCopy_length : BridgesCopy → e + 2 ≤ L`, and the phantom counterexample is
refuted.

</div>
<div>

**The lesson**

Formalizing source semantics is research, not clerical work. A transcription bug can
manufacture a theorem that is true but irrelevant.

</div>
</div>

<div class="pt-4 text-sm opacity-70">
Commit <code>12aa0ee</code>: "#88: fix the bridging source semantics; the wraparound
regime was an artifact".
</div>

---
layout: default
---

# Case study E · verify your verifier

A search script reported hundreds of counterexamples to a decomposition step.

<div class="pt-4">
The predicate `hasParallelEdges` was written against the wrong data shape, so it was
**identically false**. The "counterexamples" were an evaluator bug.
</div>

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Corrected result**

zero such counterexamples at the tested bound.

</div>
<div>

**What survived**

A genuine, different refutation of the *stated* split — found by kernel-checked
enumeration, not by the broken script.

</div>
</div>

<div class="pt-4 text-sm opacity-70">
Commits <code>e0233af</code>, and the corrected obligation
<code>edgeTypeUnique_iff_uniqueEulerianCycle</code>.
</div>

---
layout: default
---

# Independent review

Review is not "does the diff look reasonable". It checks:

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

- **predicate drift** — is the definition byte-identical to the reviewed one?
- **re-execution, not inheritance** — rebuild and replay the kernel, don't trust a
  cached green
- **non-vacuous checks** — a control module must fail
- **axiom audit** — only the permitted axioms

</div>
<div>

<div class="text-lg">
One integration run rebuilt the library, kernel-replayed it, re-audited axioms, and
re-ran the arithmetic script — and used a deliberately nonexistent module to prove
the replay was not vacuous.
</div>

</div>
</div>

---
layout: default
---

# CI: the kernel boundary

<div class="text-sm">

The build job does three distinct things:

</div>

<div class="pt-4">

1. `lake build --wfail` — compile with warnings as errors.
2. `lake env leanchecker AssemblyP1` — **replay the entire library through the Lean kernel**.
3. `axiom-audit --allow propext,Classical.choice,Quot.sound --modules-from AssemblyP1` —
   audit every theorem module, including standalone files the aggregator would miss.

</div>

<div class="pt-6 text-lg text-amber-600">
CI does not prove the math is interesting, or that the definitions match biology.
It proves the kernel accepted the formal statements, and that no disallowed axiom or
`sorry` crept in.
</div>

<div class="pt-4 text-sm opacity-70">
<code>.github/workflows/ci.yml</code>. Mathlib and compiled-object caches are keyed on the
toolchain and manifest, and persisted independently so a failed proof build does not
throw away the expensive dependency download.
</div>

---
layout: default
---

# What concurrency actually bought

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Parallel paid off**

- incompatible proof routes explored at once
- independent re-derivation of every ratio
- source/model audits alongside formalization
- bounded searches that killed routes early

</div>
<div>

**Serial was unavoidable**

- reconciliation, proposition by proposition
- one aggregator file importing many fronts
- the final endpoint theorem
- merge conflicts resolved by keeping both sides

</div>
</div>

<div class="pt-6 text-lg">
We do not claim a speedup number. The honest claim is narrower: independent fronts
could be explored without blocking each other, and the serial integration step is
where correctness was actually decided.
</div>

---
layout: default
---

# Case study F · a late source-fidelity turn

Late in the project, a front found that the formal coverage predicate was **weaker**
than the paper's actual condition: the source quantifies over any matching occurrence
of an observed read string, not only the sampled placements.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**The change was additive**

New historical predicates and theorem endpoints were added. Every original theorem,
including witnesses that fail the stronger coverage, was **preserved**.

</div>
<div>

**Two models, both first-class**

The interpretation matrix documents both. An independent Python audit and kernel
lemmas certify the new witnesses; the old model remains available.

</div>
</div>

<div class="pt-4 text-sm opacity-70">
Board #247; audit PR #128 (commits <code>39e3df0</code>, <code>f2c50c7</code>).
Never delete a valid theorem to make a stronger-sounding claim.
</div>

---
layout: default
---

# Lessons for engineers

<div class="pt-2">

1. **Separate evidence classes.** Search, exact computation, proof, and kernel check are
   four different things. Keep them labelled.
2. **Parallelize exploration; serialize reconciliation.** Agreement is not verification.
3. **Verify your verifier.** A broken predicate can manufacture or hide a result.
4. **Never replay side-effecting jobs.** Stale leases fail closed.
5. **Make review durable.** Bind verdicts to exact commits.
6. **CI is a boundary, not a proof.** The kernel is the proof boundary; modeling is still yours.
7. **Preserve failed routes.** A refuted lemma is a result — it saves the next agent.

</div>

---
layout: default
---

# What remains open

<div class="pt-4 text-lg">

- **Source fidelity.** Which historical reading of the 2016 sentence is intended
  remains partly unresolved; the project keeps the readings explicit.
- **Finite vs population.** The kernel-checked uniqueness theorem is a population
  result. Finite-read guarantees are not claimed.
- **Formal correspondence.** Matching the formal predicates to the biology is an
  ongoing, documented obligation.

</div>

<div class="pt-8 text-xl text-center">
The interesting result is not a single yes/no. It is a precise <b>map</b> of where the
reconstruction→likelihood implication holds, where it fails, and why.
</div>

---
layout: default
---

# Where to look

<div class="text-sm">

**The theorem**

`AssemblyP1/Issue94Complete.lean` — `population_unique_ML`

**The finite witnesses**

`AssemblyP1/OrientedVariableLengthSe62.lean`,
`AssemblyP1/SameLengthSection62Counterexample.lean`,
`AssemblyP1/PerOccurrenceSameLengthCounterexample.lean`

**Rigidity**

`AssemblyP1/OrientedRigidity.lean`

**The map**

`docs/source-notes/interpretation-matrix-217.md`, `docs/open-problem.md`,
`paper/main.tex`

**The engineering**

`docs/research-orchestration.md`, `docs/skills/`, `.github/workflows/ci.yml`

</div>

---
layout: end
---

# Questions?

<div class="pt-6 opacity-80">
A real math result, a real kernel check, and an honest account of the machine that
produced them.
</div>

<HomeLink label="Choose another audience" />

---
layout: default
---

# Backup · the model is deliberately idealized

- The genome is a **circular** string over `A/C/G/T`.
- Every read has the same length `L`, starts at a uniformly random position.
- Reads are **error-free**, as in the source's model.
- Cyclic rotation represents the same oriented genome.

<div class="pt-6 text-sm opacity-70">
These assumptions make the information question crisp. They are not a claim that real
sequencing data look this clean.
</div>

---
layout: default
---

# Backup · primary sources

<div class="text-sm">

**Medvedev & Brudno (2009).** "Maximum Likelihood Genome Assembly."
*Journal of Computational Biology* 16(8), 1101–1116. `doi:10.1089/cmb.2009.0047`

**Bresler, Bresler & Tse (2013).** "Optimal assembly for high throughput shotgun
sequencing." *BMC Bioinformatics* 14(Suppl 5):S18. `doi:10.1186/1471-2105-14-S5-S18`

**Shomorony, Kim, Courtade & Tse (2016).** "Information-optimal genome assembly via
sparse read-overlap graphs." *Bioinformatics* 32(17), i494–i502.
`doi:10.1093/bioinformatics/btw450`

</div>

---
layout: default
---

# Backup · exactly what the kernel checks

<div class="text-sm">

`AssemblyP1.Issue94Complete.population_unique_ML`

```
∀ K > 0, ∀ W : Fin K → α,
  AdmClass L K W → PopLogLik(W) ≤ PopLogLik(S)  ∧
  (PopLogLik(W) = PopLogLik(S) → ∃ h : G = K, RotEquiv h W S)
```

where `AdmClass L K W := IsPrimitive W ∧ P2 K L W`.

Hypotheses: `0 < G`, `1 < L`, `IsPrimitive S`, `P2 G L S`.

Audited axioms: `propext`, `Classical.choice`, `Quot.sound`.

</div>

<div class="pt-4 text-sm opacity-70">
The predecessor `population_unique_ML_up_to_rotation` is retained for the audit trail;
it still carries the external complete-spectrum premise that the new endpoint discharges.
</div>
