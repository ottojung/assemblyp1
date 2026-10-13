---
theme: default
title: "AssemblyP1 for Programmers"
info: |
  A simple maximum-likelihood rule, surprising finite-sample behavior,
  and machine-checked results about short-read genome assembly.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# Could the wrong genome be more likely?

### A surprisingly simple idea with surprisingly deep consequences

**AssemblyP1** · For programmers

<HomeLink label="Choose another audience" />

<!--
Open with the question, not with an assembly algorithm.
Everything on the next few slides can be checked by hand.
-->

---

# We see fragments, not the genome

Suppose the true genome is the circular string **AAATT**.

A sequencer takes a short read from a randomly chosen start position. For reads of length 3:

| Start | Read |
|---:|:---|
| 1 | `AAA` |
| 2 | `AAT` |
| 3 | `ATT` |
| 4 | `TTA` |
| 5 | `TAA` |

**We observe a sample of reads, not their starting positions.**

<!--
The last two reads wrap around the circular genome. We assume
error-free, oriented reads and independent uniform start positions.
-->

---

# Two different questions

**Reconstruction:** Can overlapping fragments tell us which circular genome produced them?

**Maximum likelihood:** Which proposed genome makes the **particular reads we saw** most probable?

Reconstruction exploits clues such as overlaps and repeats.

**Likelihood also uses how often each read appeared.**

<!--
Shomorony et al. (2016) prove reconstruction under structural
coverage and bridging hypotheses. No algorithm internals are needed here.
-->

---

# Maximum likelihood in one sentence

Pretend each candidate genome is a machine that generates random reads.

1. Give the machine a proposed genome.
2. Ask how likely it is to emit our observed reads.
3. Prefer the candidate assigning them the highest probability.

$$
\widehat D=\operatorname*{arg\,max}_D P(\text{reads}\mid D)
$$

**That's the scoring rule.** Searching all genomes can still be hard.

<!--
The likelihood P(reads | D) is not the posterior probability P(D | reads).
We compare candidate scores for fixed data.
-->

---

# A genome is a loaded die

**Truth:** `AAATT` — five equally likely start positions.

**Decoy:** `AAAATT` — six equally likely start positions.

Count how often each read can be produced:

| Read | Under $S$ | Under $D$ |
|:---|---:|---:|
| `AAA` | $1/5$ | $2/6$ |
| `AAT` | $1/5$ | $1/6$ |
| `ATT` | $1/5$ | $1/6$ |
| `TTA` | $1/5$ | $1/6$ |
| `TAA` | $1/5$ | $1/6$ |

**The extra A creates two starts producing AAA instead of one** — probabilities $2/6$ versus $1/5$.

---

# What did we actually observe?

Imagine six independently sampled reads:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

- `AAA` appeared **twice**.
- Each of the other four types appeared once.

This sample is entirely possible under the true genome `AAATT`.

But it contains **more AAA than the true distribution predicts on average**.

<!--
The read order is immaterial. A multinomial coefficient common to
both candidate scores cancels in their likelihood ratio.
-->

---

# Six reads. Just multiply.

Every read contributes one probability factor.

For the **true genome**:

$$
P(R\mid S)=(1/5)^6
$$

For the **decoy**:

$$
P(R\mid D)=(2/6)^2(1/6)^4
$$

That is the entire likelihood calculation for these two candidates.

---

# Surprise: the wrong genome wins

$$
\frac{P(R\mid D)}{P(R\mid S)}
=\frac{15625}{11664}\approx 1.34
$$

The decoy makes our six reads about **34% more probable**.

Why? It gives more weight to the twice-observed `AAA`.

**Maximum likelihood rewards agreement with the sample, not direct knowledge of the truth.**

*The exact finite ratio is verified in Lean.*

---

# One duplicate changes the winner

If we observe each of the five read types **once**:

```text
AAA   AAT   ATT   TTA   TAA
```

the truth wins:

$$
\frac{P(R_5\mid D)}{P(R_5\mid S)}=\frac{3125}{3888}<1
$$

Duplicate one `AAA`, and the decoy wins:

$$
\frac{P(R_6\mid D)}{P(R_6\mid S)}=\frac{15625}{11664}>1
$$

**The rule did not change. The observed frequencies did.**

<!--
Five-read ratio computed exactly. The six-read finite witness has a
kernel-checked certificate. No claim that typical samples behave this way.
-->

---

# Why this simple idea is powerful

For **any** proposed genome, likelihood gives a precise answer:

> How well does this candidate predict the frequencies of the reads we saw?

We can compare candidates without specifying how to construct them.

But there are two distinct challenges:

- **Scoring** a genome is conceptually simple.
- **Finding** the best-scoring genome can be difficult.

And the best finite-sample score does not always identify the true generator.

---

# What if sampling luck disappears?

Imagine having enough reads to know the **exact true read frequencies**.

For `AAATT`, each of the five length-3 read types then has frequency $1/5$.

Different candidates predict different distributions.

**Which distribution gives the highest average log-likelihood?**

The answer is general: **the true distribution itself**.

---

# A one-line population theorem

Let $p_S(w)$ be the true probability of read $w$ and $p_D(w)$ a candidate's probability.

$$
\ell_S(D)=\sum_w p_S(w)\log p_D(w)
$$

Then:

$$
\ell_S(S)-\ell_S(D)
=D_{\mathrm{KL}}(p_S\|p_D)\geq 0
$$

**The truth is always a population-likelihood maximizer** over any candidate class containing it.

For this *maximality* statement, **no bridging or repeat condition is needed**.

<!--
This is Gibbs' inequality: predicting a wrong frequency distribution
cannot improve expected log-score. Zero-probability predictions have
minus-infinity expected log-score when the true event has positive weight.
-->

---

# But the maximum can be tied

Consider these different circular genomes:

```text
AAACAC
AACAAC
```

Their complete length-2 read counts are identical:

| Read | `AA` | `AC` | `CA` |
|:---|---:|---:|---:|
| Count for either genome | 2 | 2 | 2 |

Even with unlimited length-2 reads, the two genomes are indistinguishable.

**The right probabilities can identify a distribution without identifying one unique genome.**

---

# When does the truth become unique?

AssemblyP1 proves population uniqueness within a structured class:

- **Primitive** circular genomes: not repetitions of a shorter genome.
- **P2-admissible** genomes: certain troublesome repeat arrangements are absent at the chosen read length.
- **Oriented** reads, with circular rotations considered equivalent.

Within that class, the true genome is the **unique population maximum up to rotation**.

**Probability supplies maximality. Structure supplies uniqueness.**

<!--
Both the truth and admissible candidates are restricted to the primitive P2
class; this does not assert uniqueness for arbitrary genomes.
-->

---

# A positive result for finite reads, too

Finite sampling is not always hopeless.

Under **stronger structural hypotheses** — including suitable bridging, an admissible true genome, and same-length oriented competitors — the overlap constraints force the possible read spectrum.

In that precise setting, our rigidity theorem gives a **positive finite maximum-likelihood guarantee**.

It does **not** automatically extend to arbitrary lengths or observation conventions.

---

# What did we actually verify?

Lean mechanically checked mathematical claims including:

- The **exact finite likelihood reversal** from our example.
- **Structural rigidity** under explicit read-bridging assumptions.
- **Population uniqueness** for the primitive P2 class.

Independent agents helped explore examples and proofs. The lasting results are **precise, re-checkable theorems**.

---

# One little rule, three discoveries

**Multiply the probabilities a candidate assigns to the reads.**

That gives us:

1. A wrong genome can score higher on a finite sample.
2. The truth always maximizes the exact-population score.
3. Whether it is the **only** maximizer depends on the structure of repeats.

**Simple probability meets deep combinatorics.**

---

layout: end
---

# Thank you

**[The paper, proofs, and presentations](https://github.com/ottojung/assemblyp1)**

<HomeLink label="Choose another audience" />
