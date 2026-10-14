---
theme: default
title: "The Most Likely Genome"
info: |
  Genome assembly, probability, and mathematical verification.
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

# Reconstruction from overlaps: a worked traversal

Adjacent reads agree on their last and first two letters:

```text
ACG → CGT → GTA → TAA → AAC
  ↑                       ↓
  └───────────←───────────┘
```

Following those overlaps spells the circular genome `ACGTA`.

**This is a de Bruijn graph:** each 3-mer is an edge from its 2-letter prefix to its 2-letter suffix, and an Eulerian traversal uses each edge once.

<!--
Point to ACG -> CGT: the CG suffix matches the CG prefix. In the de Bruijn
graph, ACG is an edge AC -> CG, CGT is CG -> GT, and so on; the cycle
AC -> CG -> GT -> TA -> AA -> AC uses each of the five edges once and spells
ACGTA. A circular genome has n rotation spellings with identical windows, so
reconstruction is always "up to rotation". This teaching graph is NOT the
read-overlap graph of the 2016 algorithm on the next slides.
-->

---

# The 2016 algorithm uses a different graph

Shomorony, Kim, Courtade, and Tse (2016) build a **read-overlap graph**:

- **vertices are observed reads** — not short k-mers;
- edges are suffix–prefix overlaps between reads;
- Not-So-Greedy keeps the greedy successor **plus the first genuinely disagreeing extension**;
- it **prunes spurious and transitive edges** and adjusts **edge multiplicities** to make the graph Eulerian.

Under coverage and repeat-bridging conditions, that multigraph has a **unique Eulerian cycle**, and it spells the true circular genome.

<!--
Cite Shomorony et al., "Information-optimal genome assembly via sparse
read-overlap graphs", Bioinformatics 2016, DOI 10.1093/bioinformatics/btw450,
Theorem 1 and its supplementary conditions. The construction takes O(NL) time
for N reads of length L. This graph is DISTINCT from the de Bruijn teaching
graph on the earlier slide: here vertices are observed reads, not (L-1)-mers.
Present the ideas, not the full internal construction. This slide restores the
actual graph construction and reconstruction that an earlier draft had removed.
-->

---

# The 2016 open question

The paper closes with a question that sits between reconstruction and statistics:

$$
\text{Not-So-Greedy's success conditions}
\quad\stackrel{?}{\Longrightarrow}\quad
S\in\operatorname*{arg\,max}_D P(R\mid D)
$$

**Do the conditions that make reconstruction succeed also make the truth a maximum-likelihood genome?**

<!--
Paraphrase of the 2016 Discussion, which points back to Medvedev and Brudno
2009. The symbols are schematic: the candidate predicates, the read-type
convention, and the objective (exact multinomial, fixed-N product binomial, or
the Section 6.2 flow) vary across readings and are exactly what the research
pins down. This is the ENTRANCE to the statistical thread, not the paper's main
result.
-->

---

# Every genome predicts a distribution

In this model each read begins at a **uniformly random start**. So each genome assigns every read type a probability:

$$
P_G(w)=\frac{\text{starts yielding }w}{G}
\qquad
P(\texttt{AAA}\mid\texttt{AAATT})=\tfrac15
\quad
P(\texttt{AAA}\mid\texttt{AAAATT})=\tfrac26
$$

**Likelihood** $P(R\mid G)$ is not the **posterior** $P(G\mid R)$ — the posterior also needs a candidate set and a prior.

**Uniform over start positions is not uniform over read strings.**

<!--
Uniformity is over the |G| start positions, not over the <= 4^L read types: the
number of starts yielding a type varies by genome, so the induced probabilities
differ. Distinguish (i) the sampling process, (ii) the likelihood P(R|G), and
(iii) the posterior P(G|R), which needs a candidate universe and a prior; there
is no uniform distribution over an unrestricted infinite genome universe.
Circular rotations induce identical spectra, so they are observationally
equivalent candidates.
-->

---

# Why ML is worth studying: the Bayes entrance

With a **finite candidate set**, a **uniform prior**, and **zero-one loss**:

> Maximum likelihood maximizes the **prior-averaged** probability of returning the truth, among **all** deterministic and randomized rules that use the same reads.

The proof is one line: for each observed sample, choose the largest posterior; averaging preserves the inequality; randomization is a convex combination and cannot beat the best point.

**Kernel-checked** in `AssemblyP1/FiniteBayesDecision.lean`.

**Limits:** prior-averaged, not per-truth; not for arbitrary loss; ties are broken consistently.

<!--
This is the ENTRANCE and rationale, not the paper's overarching result. Standard
decision theory (Berger 1985, Section 2.4). Kernel endpoints: chooseMAP_optimal,
chooseMAP_optimal_randomized, finite_iid_MAP_optimal, and the monotonicity
result chooseMAP_success_monotone_under_refinement. "More observations cannot
hurt" is about PRIOR-AVERAGED success, never about a fixed true genome. The
guarantee applies to the exact read distribution, not automatically to a
surrogate objective. Keep the hierarchy: Bayes-optimal ML motivates the
question; it is not an ML-supremacy claim.
-->

---

# Positive structural result: rigidity and uniqueness

Under the source's structural hypotheses — bridging, oriented reads, equal candidate length, truth among the candidates:

> the truth's length-$L$ spectrum is the **unique positive integer circulation** of its window-support graph. Every same-length oriented competitor ties the truth, and with the complete-spectrum step each such competitor is a **cyclic rotation** of the truth.

**No strict same-length counterexample exists** — for any genome length, read length, or alphabet.

<!--
Kernel endpoints: OrientedRigidity.unique_positive_circulation;
SameLength62Maximizer (informationFeasible_62_maximizer);
SameLength62Uniqueness.unique_62_maximizer_up_to_rotation (the unconditional
rotation endpoint); OrientedFinal.oriented_same_length_spectrum_rigidity and
OrientedFinal.rotation_uniqueness_of_bbt (the latter consumes the unproved
external BBT premise, so it is conditional). State the qualifiers honestly:
dropping truth candidacy is false at equal length (AABB -> ABAB); dropping equal
length restores strict counterexamples. The general Graver-basis criterion
(GraverRigidity.rigid_iff_forall_graver_not_feasible) is a separate iff for
integer-flow supports, not this theorem.
-->

---

# A finite aside: even the truth can lose

Finite samples fluctuate. A competitor can assign the observed read counts higher probability even when reconstruction is feasible:

$$
\frac{\mathrm{Lik}(D)}{\mathrm{Lik}(S)}=3
\qquad
S=\texttt{AAATAT},\quad D=\texttt{AAAAAT}
$$

**An optimal estimator is not an infallible estimator.** More reads improve the *average*; success for a *particular* true genome need not be monotone in $n$.

<!--
Kernel endpoint:
SameLengthSection62Counterexample.samelength_se62_bidirected_flow_counterexample
(exact ratio 3; the source's fixed-N binomial ratio is 5), under the source's
same-length molecule model with bridging holding. Whole families follow
(HistoricalCoverageSameLengthWitnesses, OrientedVariableLengthSe62). This is a
short aside: the full AAATT/AAAATT teaching calculation is in backup B1.
Mechanism: the competitor reallocates multiplicity toward an over-represented
observed read type. Do NOT present this as the first result or as "ML is
invalid" — the prior-averaged optimality of the previous slide is untouched.
-->

---

# Population level: identifiability

Replace the finite sample by the **exact read distribution**:

- the truth always **maximizes** expected log-likelihood — a Gibbs/KL identity;
- **uniqueness** is the deep part: for primitive, P2-admissible genomes the maximizer is unique **up to rotation**.

For a finite identifiable family, independent reads make empirical frequencies converge (strong law), so ML is eventually correct almost surely and $P(\text{correct at } n)\to 1$.

**"Infinite reads" is a limit — not an infinite product of probabilities.**

<!--
Kernel endpoints: PopulationGibbs.popLogLik_le_self' (maximality; support holes
give -infinity) and PopulationGibbs.popTie_iff (equality iff equal read
distributions); Issue94Complete.population_unique_ML (uniqueness up to rotation,
no external premise, under primitive + P2 + the admissible class + L >= 2). The
convergence statement is standard statistics (strong law; ML consistency under
identifiability, e.g. Lehmann & Casella 1998) and is NOT kernel-checked.
Distinguish population uniqueness from finite-sample guarantees. The open
sample-complexity question ("how many reads for 99%?") is backup B3.
-->

---

# Agents were present from day one

On September 17 the project began with **two things already in place**: a real open question from the genome-assembly literature, and a research method — cooperating AI agents, durable work, adaptive orchestration, and Lean as the verification boundary.

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
Founding narrative: docs/intent-records/project.md, intent records dated
2026/09/17; the initial commits already seed Lean, agent instructions,
orchestration, and durable intent records. The board is the memory; agents are
stateless. The orchestrator decomposes broad questions into narrow packets; every
write-capable worker gets its own branch and worktree. The expensive, serial
part is reconciliation — merging partial results proposition by proposition,
checking quantifiers, hypotheses, model versions, and tie semantics rather than
trusting prose summaries. A worker's own summary is not independent verification.
-->

---

# What Lean is — and why the kernel can be trusted

**Propositions are types. Proofs are programs.**

```lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
```

A tiny **kernel** checks every proof term — the only code that must be trusted. CI replays every theorem through it and audits the axioms: only Lean's three standard ones are allowed.

**Where trust ends:** axioms are assumed, not proved; the kernel checks the *formal statement* — not whether the definitions match the biology.

<!--
Curry-Howard correspondence: the proposition p ∧ q → q ∧ p is the type; the term
fun h => ⟨h.2, h.1⟩ is the proof. The kernel type-checks the term against the
type; type checking is small and mechanical. The project permits only propext,
Classical.choice, and Quot.sound, and no sorry/admit. Model fidelity stays with
the humans and the source audits. Two predicate episodes (the bridging predicate
and the coverage predicate) were caught only because formalization is treated as
research and audited against the source; see backup B2.
-->

---

# Trust the check, not the claim.

We started with a question from 2016: **do Not-So-Greedy's reconstruction conditions also make the true genome a maximum-likelihood genome?**

**Bayes-optimal ML is the entrance**, not the headline. The contribution is the **assembly-specific classification**: positive rigidity, negative finite witnesses, and population identifiability — all kernel-checked.

<HomeLink label="Choose another audience" />

<!--
One-sentence takeaway: under a specified equal-prior model ML maximizes average
correctness, yet can still be wrong on a particular sample; what AssemblyP1 adds
is the assembly-specific classification of when the truth wins, ties, or loses
under exact, binomial, and flow objectives, plus population uniqueness under
primitive P2. General characterization and sample complexity remain open.
Definitions are part of the claim: verify your verifier.
-->

---
layout: end
---

# Backup B1: the complete finite reversal calculation

Six length-3 reads sampled from the truth `AAATT`:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

$$
P(R\mid S)=\left(\tfrac15\right)^6=\tfrac1{15625}
\qquad
P(R\mid D)=\left(\tfrac26\right)^2\left(\tfrac16\right)^4=\tfrac1{11664}
$$

The decoy `AAAATT` scores about **34% higher** for this sample.

**An optimal estimator is not an infallible estimator.**

<!--
This is a restricted two-candidate teaching illustration with variable-length
candidates; it is NOT a source-faithful counterexample to a 2016/MB09 candidate
class. Use only if the audience asks "can the truth actually lose?". The
source-faithful same-length witness is on the main "finite aside" slide. With
equal priors the decoy posterior is 15625/(15625+11664) ~ 57.3%; the ML/MAP rule
still minimizes prior-averaged error.
-->

---

# Backup B2: two incomparable definitions of coverage

A late audit found the formal **coverage predicate** did not match the source's actual condition.

**Old model** — every genomic base lies inside a read placed at a sampled start.

**Historical model** — every length-$(L-1)$ window must contain a match of an observed read string, even where no read was sampled.

**Neither definition implies the other.**

The fix was **additive**; old results were preserved.

<!--
Kernel regressions: AssemblyP1/HistoricalCovers.lean and
HistoricalCoverageSameLengthWitnesses.lean. The historical model saturates
matching repeat occurrences but requires a read START witness the old model does
not, so the two predicates are incomparable. A second bug in the bridging
predicate was pure arithmetic on the wrong definition and manufactured a phantom
"counterexample" that only independent audit caught. Lesson: a weaker theorem you
keep is a result; a stronger theorem you fake is a liability.
-->

---

# Backup B3: how many reads for 99% recovery?

The limit theorem gives **convergence**, not a finite sample size.

**Sample complexity is an open quantitative problem** in this precise model.

A scoped, external illustration: for a finite distinguishable family,

$$
\Pr_\theta[\text{a wrong genome beats the truth}]
\;\le\; \sum_{\eta\neq\theta}\rho(\theta,\eta)^n,
$$

where $\rho$ is the Hellinger affinity. This is per-truth, and not proved here.

<!--
No sample-complexity theorem exists in this model. The Hellinger/union bound is
standard (e.g. Tsybakov 2009, Theorem 2.4) and is labelled EXTERNAL — not
kernel-checked. Never imply that the limit theorem itself supplies a finite n.
The bound is per fixed truth, not a uniform guarantee, and needs the family to
be finite and distinguishable.
-->

---

# Backup B4: primary sources

- Medvedev & Brudno (2009), *Maximum Likelihood Genome Assembly*.
- Shomorony, Kim, Courtade & Tse (2016), *Information-optimal genome assembly via sparse read-overlap graphs*.
- Bresler, Bresler & Tse (2013), *Optimal assembly for high throughput shotgun sequencing*.
- Berger (1985), *Statistical Decision Theory and Bayesian Analysis*.
- Cover & Thomas (2006), *Elements of Information Theory*.
- Tsybakov (2009), *Introduction to Nonparametric Estimation*.

**[Research repository](https://github.com/ottojung/assemblyp1)**
