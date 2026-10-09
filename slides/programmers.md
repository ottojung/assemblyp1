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

<HomeLink label="Choose another audience" />

---
layout: default
---

# The puzzle in one picture

A circular genome is sequenced as many short, error-free reads.

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Reconstruction**

Can we recover the source string from overlapping pieces?

```
source:  A C G T T A C G A T
reads:   ACGTT   TTACG   ACGAT
```

</div>
<div>

**Maximum likelihood**

Which candidate genome best explains the *observed read counts*?

$$
\arg\max_{W}\ \Pr(\text{reads} \mid W)
$$

</div>
</div>

<div class="pt-6 text-lg">
The 2016 open question asked whether <b>structural repeat-bridging conditions</b> are enough to guarantee that the maximum-likelihood genome is the true genome.
</div>

---
layout: default
---

# Assemblers organize reads as a de Bruijn graph

Each read is an edge between its length-$(L-1)$ prefix and suffix; shared pieces merge.

```text
        ACG            CGC            GCG
   AC --------> CG --------> GC --------> CG
                 \                        /
             CGT  \                      /  GCG (the repeat)
                   v                    v
                  GT ------> TA ------> AC
```

The walk `AC → CG → GC → CG → GT → TA → AC` spells `ACGCGT` with `L = 3`.

<div class="pt-4 text-amber-600">
The repeat <code>CGCG</code> turns node <code>CG</code> into a fork: two entries, two exits.
The graph alone cannot say which entry pairs with which exit.
</div>

---
layout: default
---

# Repeats are structural ambiguity

<div class="text-xl pt-6">

`...A `**`CGCG`**` T...`
`...G `**`CGCG`**` C...`

</div>

A read entirely inside the repeated block cannot tell which copy it came from.

<div class="pt-8 text-amber-600 text-lg">
This is structural ambiguity in the data, not a flaw in any one algorithm.
</div>

Bridging conditions were designed to rule out exactly the repeat configurations that make assembly ill-posed.

---
layout: default
---

# The 2016 question connected two ideas

<div class="text-2xl text-center pt-10">

structurally enough information to reconstruct

<div class="text-4xl py-4">⇓ ?</div>

maximum likelihood chooses the true genome

</div>

<div class="pt-8 text-base opacity-80">
Shomorony, Kim, Courtade & Tse (2016) explicitly left this implication open,
pointing to the Medvedev–Brudno maximum-likelihood formulation.
</div>

---
layout: default
---

# Maximum likelihood is a different test

Reads are sampled from uniformly random start positions.

A candidate genome predicts a probability for every read string. Observed multiplicities then give a likelihood score.

<div class="pt-6 text-lg text-amber-600">
"Can spell every observed read" and "assigns the highest probability to this sample" are different questions.
</div>

---
layout: default
---

# The historical wording hides several ML problems

<div class="text-lg">

- Are read strings **oriented**, or collapsed with their reverse complements?
- Must candidates have the **true genome length**?
- Which Medvedev–Brudno **likelihood / candidate** formulation is intended?
- Does "is the true sequence" mean *a* maximizer, or the *unique* maximizer up to rotation?

</div>

<div class="pt-8 text-amber-600">
AssemblyP1 split these choices instead of silently picking one.
</div>

---
layout: default
---

# Finite data gives both answers

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

### Positive

Oriented reads + same-length candidates + the structural condition force the complete read spectrum.

The truth is then uniquely determined **up to circular rotation**.

</div>
<div>

### Negative

Allow variable candidate length, change strand semantics, or pick another source-derived formulation, and **explicit finite counterexamples appear**.

</div>
</div>

<div class="pt-8 text-amber-600">
There is no single yes/no answer until the model is pinned down.
</div>

---
layout: default
---

# An explicit finite likelihood reversal

Oriented, variable-length comparison with `L = 3`:

- truth `S = AAATT`
- decoy `D = AAAATT`

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Candidate-intrinsic exact ratio**

$$
\frac{15625}{11664} > 1
$$

the decoy wins

</div>
<div>

**Full-start sample (`n = 5`)**

$$
\frac{3125}{3888} < 1
$$

the truth wins

</div>
</div>

<div class="pt-6 opacity-80">
The sign of the comparison depends on the sampling model, not just the genomes.
A reverse-complement molecule witness `AAATAT → AAAAAT` gives exact ratio `3` and fixed-`N` binomial ratio `5`.
</div>

---
layout: default
---

# Why the same-length success is slightly suspicious

<div class="text-2xl pt-8">
The assembler is being told the true target length.
</div>

That removes a degree of freedom from every competing genome.

So the project asked whether **candidate-checkable structural conditions** could replace privileged knowledge of the answer.

---
layout: default
---

# Intrinsic structural checks still do not cure finite sampling

Even when a candidate passes strong repeat and read-length checks,

<div class="text-2xl pt-6 text-amber-600">
a finite random sample can accidentally favor the wrong frequency profile.
</div>

This isolates a second obstruction: **sampling noise**, distinct from repeat ambiguity.

---
layout: default
---

# Population ML removes the sampling accident

Replace one finite draw by its exact read distribution.

<div class="pt-4 text-lg">
The expected log-likelihood is maximized exactly when the candidate predicts the same normalized read spectrum as the truth (Gibbs / KL).
</div>

<div class="pt-6 text-amber-600 text-lg">
Statistics is now clean; uniqueness becomes a combinatorial identifiability question.
</div>

---
layout: default
---

# Strongest current repaired result

For oriented circular genomes that are

- **primitive** (not a whole-genome repetition), and
- **P2 / Ukkonen-admissible** at the read length,

population maximum likelihood uniquely recovers the true genome up to rotation.

<div class="pt-6 text-base">
This theorem is kernel-checked end to end:
<code>AssemblyP1.Issue94Complete.population_unique_ML</code> proves, for <b>any-length</b> admissible candidates, both optimality and rotation uniqueness — with no external theorem assumed.
</div>

---
layout: section
---

# From mathematics to engineering

How a multi-agent research system found, checked, and integrated these results.

---
layout: default
---

# Grounded architecture

<div class="grid grid-cols-2 gap-6 pt-2 text-sm">
<div>

**Durable coordination**

- **Antonina board** — canonical task, review, and feedback surface
- **OpenClaw orchestrator** — topology- and independence-driven scheduling
- **Workers** — one research branch / proof per front

</div>
<div>

**Execution & integration**

- **Job protocol** dispatching work through a queue to remote execution hosts
- **GitHub worktrees**, SSH pushes, signed commits, PR review and CI
- **Lean + Mathlib kernel** as the proof-acceptance boundary

</div>
</div>

<div class="pt-6 opacity-80 text-sm">
Observed and desired behavior are kept separate: ideas that were not deployed are not attributed to running production.
</div>

---
layout: default
---

# The research loop looked like engineering

<div class="text-xl text-center pt-6">

source reading → formal model → bounded search

→ counterexample / proof → audit → reconciliation → synthesis

</div>

<div class="pt-8 text-base">
GitHub issues tracked research questions. Parallel workers attacked independent uncertainties. Failed arguments were preserved when they changed what should be tried next.
</div>

---
layout: default
---

# Case study: discovery then verification

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

### Search

Scripts exhaust small genomes and samples to discover surprising candidates and likelihood inequalities.

Bounded search is **evidence**, not proof.

</div>
<div>

### Verification

Exact-rational scripts remove floating-point doubt for a finite calculation.

Lean then kernel-checks the formal statement and proof term.

</div>
</div>

<div class="pt-6 text-amber-600">
Testing suggests · exact arithmetic verifies a calculation · proof establishes a theorem · the kernel checks a formal proof.
</div>

---
layout: default
---

# Evidence levels are intentionally different

| Level | What it gives |
| --- | --- |
| Bounded search | examples and patterns; not a proof |
| Exact script | a finite calculation without floating-point doubt |
| Mathematical proof | a general implication from stated assumptions |
| Lean proof | a formal statement and proof term checked by the kernel |

<div class="pt-6">
The repaired population theorem is kernel-checked end to end.
The finite same-length candidate-rotation result is kernel-checked when both truth and competitor carry genuine §6.2 certificates.
</div>

---
layout: default
---

# Exactly what Lean checks

<div class="text-sm">

**Population theorem — checked, no external premise.**

`AssemblyP1.Issue94Complete.population_unique_ML`: oriented circular truth, `0 < G`, `1 < L`, truth primitive and P2 at read length `L`; for **every** candidate length `K > 0` and **every** primitive P2 candidate `W`:

1. its population log-likelihood is ≤ the truth's;
2. any tie forces `K = G` and `W` a cyclic rotation of the truth.

**Finite same-length candidate rotation — checked, conditional.**

`SameLength62Uniqueness.unique_62_maximizer_up_to_rotation`: under full-information feasibility and genuine §6.2 truth and competitor certificates, every candidate rotates the truth.

</div>

---
layout: default
---

# What changed our understanding

- Repeat bridging addresses **structural identifiability**.
- Maximum likelihood also depends on the **candidate model and finite frequencies**.
- Some finite formulations fail; a strict same-length oriented formulation succeeds.
- Removing privileged true-length knowledge exposes **finite-sampling failures**.
- Population ML cleanly separates **statistical noise** from **spectrum identifiability**.

<div class="pt-6 text-amber-600">
The interesting result is the map of where the implication works, where it fails, and why.
</div>

---
layout: default
---

# Current frontier

The original 2016 sentence remains source-ambiguous enough that AssemblyP1 does not pretend one modern formulation is uniquely "the" historical conjecture.

The project now has precise finite positive/negative results and a clean, kernel-checked repaired population theorem.

Remaining work: source fidelity, separately formalizing the complete-spectrum theorem the finite argument still assumes, and publication-quality exposition.

---
layout: end
---

# Questions?

<div class="pt-6 opacity-80">
Two audience-specific decks share one GitHub Pages site.
</div>

<HomeLink label="Choose another audience" />

---
layout: default
---

# Backup: the model is deliberately idealized

- The genome is a **circular** string over A/C/G/T.
- Every read has the same length `L` and starts at a uniformly random position.
- Reads are **error-free**, as in the model of the 2016 question.
- Circular rotation represents the same oriented genome.

<div class="pt-6 text-sm opacity-80">
These assumptions make the information-theoretic question crisp; they are not a claim that real sequencing data look this clean.
</div>

---
layout: default
---

# Backup: primary sources

<div class="text-sm">

**Medvedev & Brudno (2009).** "Maximum Likelihood Genome Assembly." *Journal of Computational Biology* 16(8), 1101–1116. `doi:10.1089/cmb.2009.0047`

**Bresler, Bresler & Tse (2013).** "Optimal assembly for high throughput shotgun sequencing." *BMC Bioinformatics* 14(Suppl 5):S18. `doi:10.1186/1471-2105-14-S5-S18`

**Shomorony, Kim, Courtade & Tse (2016).** "Information-optimal genome assembly via sparse read-overlap graphs." *Bioinformatics* 32(17), i494–i502. `doi:10.1093/bioinformatics/btw450`

</div>
