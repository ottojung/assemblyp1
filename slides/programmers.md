---
theme: default
title: "The Most Likely Genome"
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

# An important result already existed

Shomorony and colleagues (2016) showed that, under precise **coverage and repeat-bridging conditions**, the observed reads contain enough information to reconstruct the true circular genome.

They also gave an algorithm that succeeds under those conditions.

That is a remarkable **reconstruction guarantee**.

But it leaves a different question open: *how should a candidate genome be scored?*

<!--
Source: Shomorony, Kim, Courtade & Tse, Bioinformatics 2016.
Do not teach the implementation of Not-So-Greedy here.
The reconstruction result and likelihood result concern different questions.
-->

---

# Why use likelihood at all?

Read collection is **random sampling**.

Every proposed genome therefore predicts not just *which reads are possible*, but **how frequently** each read should appear.

Two genomes might explain every read we saw, yet predict very different frequencies.

**Maximum likelihood uses those frequencies as evidence.**

Instead of asking for the shortest compatible sequence, it asks:

> Which candidate would most likely have produced this particular sample?

<!--
Medvedev & Brudno (2009) proposed maximum likelihood as an alternative
to maximum parsimony. Likelihood is a scoring objective, not a method
for searching all possible genome sequences.
-->

---

# A simple probabilistic model

Pick a start position **uniformly at random** on a candidate circular genome.

Take the next $L$ letters as a read. Repeat independently.

For each read type:

$$
P(\text{read}\mid\text{genome})
=\frac{\text{number of matching start positions}}{\text{genome length}}
$$

For a sample of independent reads, **multiply their probabilities**.

This is the basic appeal: a statistical score derived from the experiment.

It measures **how likely the reads are given a genome**, not how likely the genome itself is.

<!--
A fixed-length, oriented, error-free, independent uniform-start model.
This slide introduces the simplest candidate-intrinsic likelihood,
not every objective in the historical literature.
-->

---

# The research question

The 2016 paper asked whether **bridging conditions**, which guarantee reconstruction, also guarantee that the **true genome maximizes likelihood**.

It sounds plausible:

- The reads contain enough information to find the true sequence.
- Likelihood is a principled way to score possible sequences.

**Does the first fact imply the second?**

That is the question I set out to investigate.

<!--
Historical source: Shomorony et al. (2016), Discussion; likelihood is
linked to Medvedev & Brudno (2009).
Avoid silently changing 'is a maximizer' to 'is the unique maximizer'.
-->

---

# First, what exactly is the claim?

The answer depends on choices that sound minor but change the mathematics:

- **Likelihood:** which probability model and approximation?
- **Candidates:** any genome, or only certain compatible assemblies?
- **Observations:** oriented reads or double-stranded molecules?
- **Guarantee:** is the truth *a* maximizer, or the *only* one?

There is also a difference between **observed read strings** and their hidden starting positions.

**I made these distinctions explicit before treating any proof as a resolution.**

<!--
The source is not a single universally specified mathematical objective.
Historical read-string coverage must not be silently replaced by the
project's sampled-placement variant. Keep both interpretations audited.
-->

---

# A small example of the difficulty

Suppose the actual circular genome is:

**Truth:** `AAATT` (length 5)

Consider another candidate:

**Competitor:** `AAAATT` (length 6)

And suppose we observed six length-3 reads:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

Both genomes can generate every one of these reads.

**Which genome makes this particular sample more likely?**

<!--
This is a minimal illustration of finite-sample reweighting in an
unrestricted variable-length candidate model. It is not, by itself,
a source-faithful counterexample to every 2016/2009 interpretation.
-->

---

# Look at the predicted frequencies

| Read type | Truth `AAATT` | Competitor `AAAATT` |
|:---|---:|---:|
| `AAA` | $1/5$ | $2/6$ |
| `AAT` | $1/5$ | $1/6$ |
| `ATT` | $1/5$ | $1/6$ |
| `TTA` | $1/5$ | $1/6$ |
| `TAA` | $1/5$ | $1/6$ |

**The extra A creates two matching start positions**, instead of one.

And `AAA` is exactly the read that appeared twice in our sample.

---

# The surprising calculation

Likelihood means multiplying the six read probabilities.

$$
P(R\mid S)=(1/5)^6=\frac{1}{15625}
$$

$$
P(R\mid D)=(2/6)^2(1/6)^4=\frac{1}{11664}
$$

Therefore:

$$
\frac{P(R\mid D)}{P(R\mid S)}
=\frac{15625}{11664}\approx1.34
$$

**The wrong genome gets the higher score.**

The score is simple; the implications are not.

---

# What have we actually learned?

We have exhibited a **finite-sample failure**: a candidate that was not the source can assign greater probability to the reads that happened to be sampled.

But this example does **not** settle every version of the original question.

In particular, allowing a different genome length changes the candidate universe.

**A good counterexample must satisfy the exact hypotheses of the statement it claims to refute.**

That was one of my central requirements throughout the research.

---

# The finite results have a boundary

The investigation produced both **positive and negative** results.

**Under specific same-length, oriented, bridging and candidate-admissibility assumptions:** the true genome is a likelihood maximizer; the relevant candidates cannot strictly outperform it.

**Under broader candidate models or other read conventions:** strict finite counterexamples exist, including witnesses checked against the historical read-string conditions.

Neither answer can be generalized by silently dropping its assumptions.

<!--
The positive result uses genuine Section 6.2 candidates, oriented reads,
same length, and the project's read-placement information-feasibility.
Historically faithful molecule witnesses exist for separate conventions.
Exact details and proofs belong in the whitepaper.
-->

---

# How I directed the investigation

I did not treat producing a proof as the research goal.

I kept making decisions about **which claim was worth proving**:

- Return to the original papers when definitions or citations looked questionable.
- Separate plausible readings instead of treating them as interchangeable.
- Pursue both concrete counterexamples and restricted positive theorems.
- Reject a result if its assumptions did not match the intended question.
- Keep unresolved cases explicitly open rather than claiming completion.

**The task was to steer the research toward a correct answer, not merely a finished proof.**

<!--
First-person research coordination is deliberate. Focus on the user's
intellectual decisions, issue prioritization, source scrutiny and acceptance
criteria, not agent scheduling, tool logistics or model endpoints.
-->

---

# What counted as convincing evidence?

For every substantial claim, I required a chain of checks:

1. **Source fidelity:** are we answering the question actually written?
2. **Exact examples:** do the counts and probabilities really work?
3. **Formal statement:** does the theorem say precisely what we claim?
4. **Lean verification:** is the proof accepted by the kernel?
5. **Independent review and CI:** can the result be checked again?

A green build alone is not enough if the theorem proves the wrong thing.

<!--
The user directed independent reviewers and insisted on direct target
formalizations, exact-head CI, and not merging failing branches.
-->

---

# Why the distinction matters

This work taught me to separate three questions:

- **Reconstruction:** do the reads determine the genome?
- **Finite-sample likelihood:** does this actual sample score the truth highest?
- **Identifiability:** can two different genomes have the same read distribution?

They are related, but not equivalent.

**The interesting work is finding the conditions under which one conclusion really follows from another.**

<!--
Population ML is deliberately not introduced as though it were the
original finite-sample question. The backup slide explains it as a
separate response to sampling fluctuations, if asked.
-->

---

# What we can say in the end

A natural statistical scoring rule is **not automatically** a reconstruction guarantee.

Finite-sample fluctuations can favor a wrong candidate.

But strong structural assumptions can produce positive guarantees for a carefully specified candidate class.

Most importantly, these are **mathematical claims with boundaries** — and the research was about making those boundaries explicit, proving the results, and checking their fidelity.

---

layout: end
---

# The Most Likely Genome

**[Paper, Lean proofs, and evidence](https://github.com/ottojung/assemblyp1)**

<HomeLink label="Choose another audience" />

---

# Optional extension: remove sampling noise

*This is a different question, not the finite conjecture.*

Suppose instead of a finite sample we know the **exact read-frequency distribution** of the true genome.

Now Gibbs' inequality gives:

$$
\ell_S(S)-\ell_S(D)=D_{\mathrm{KL}}(p_S\|p_D)\ge0
$$

So the truth **always maximizes population likelihood**.

Why study this? It removes finite-sampling fluctuations and isolates the remaining problem: **can two genomes induce the same distribution?**

<!--
This is the population follow-up formulated by the project, not a
restatement of the source's finite-sample conjecture. Its maximality
is generic; uniqueness under primitive P2 needs a separate theorem.
-->

---

# Optional extension: maximum is not unique

Two different circular genomes may have the **same** distribution of short reads.

For example:

```text
AAACAC
AACAAC
```

Both have two occurrences each of `AA`, `AC`, and `CA`.

Then their population likelihoods **tie**, even with unlimited data at that read length.

Our separate population theorem proves uniqueness **up to rotation** inside a primitive, P2-admissible, oriented class — not among all genomes.
