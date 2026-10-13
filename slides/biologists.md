---
theme: default
title: "AssemblyP1 for Biologists"
info: |
  Why the most likely genome can differ from the true genome,
  and what short-read frequencies can really tell us.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# Which genome is most likely?

### A simple probability puzzle from short-read sequencing

**AssemblyP1** · For biologists and genomicists

<HomeLink label="Choose another audience" />

<!--
Start with likelihood, not the intricacies of an overlap algorithm.
The core example uses only five possible read types.
-->

---

# A sequencer takes a sample

Consider a small **circular genome**, `AAATT`.

If we read three bases at a time, the possible read types are:

| Start position | Read |
|---:|:---|
| 1 | `AAA` |
| 2 | `AAT` |
| 3 | `ATT` |
| 4 | `TTA` |
| 5 | `TAA` |

We do not observe the starting positions — only reads drawn from them.

*Assume error-free reads, with each start position equally likely.*

---

# Overlaps help. Repeats confuse.

Reads sharing a long overlap can be placed beside one another.

But a repeated sequence may occur in more than one place:

```text
...G [ ACGA ] T...
...C [ ACGA ] A...
```

A short read entirely inside `ACGA` cannot identify the copy it came from.

**That is missing information, not a failure of computation.**

---

# Longer context can resolve a repeat

A read that spans **both ends of a repeat copy** captures the sequence on either side.

```text
...G [ ACGA ] T...
   G [ ACGA ] T
```

The flanking bases distinguish this occurrence from another copy.

Under precise coverage and bridging conditions, a reconstruction algorithm can recover the true circular genome.

*Shomorony et al. (2016) prove such a guarantee.*

<!--
Do not teach Not-So-Greedy implementation in this talk.
The key takeaway is that there is a structural reconstruction result.
-->

---

# But the paper left another question

If the reads already contain enough information to reconstruct the genome...

**...must the true genome also be the most likely explanation of those reads?**

Those are not identical questions.

- Reconstruction asks **which arrangements fit**.
- Maximum likelihood asks **which arrangement best predicts the observed frequencies**.

---

# Maximum likelihood is simple

Imagine testing a proposed genome by repeating the sequencing experiment in your head.

1. How many start positions produce each read type?
2. How probable are the reads we actually saw?
3. Which candidate assigns the **highest probability** to the sample?

**Nothing more complicated than a set of probabilities and a product.**

<!--
This is likelihood P(data | genome), not posterior probability P(genome | data).
Searching over all candidate genomes is a separate problem.
-->

---

# Two genomes make different predictions

| Candidate | Genome | Length |
|:---|:---|---:|
| Truth $S$ | `AAATT` | 5 |
| Decoy $D$ | `AAAATT` | 6 |

With uniformly random starts:

| Read type | Under $S$ | Under $D$ |
|:---|---:|---:|
| `AAA` | $1/5$ | $2/6$ |
| `AAT` | $1/5$ | $1/6$ |
| `ATT` | $1/5$ | $1/6$ |
| `TTA` | $1/5$ | $1/6$ |
| `TAA` | $1/5$ | $1/6$ |

**The extra A makes an AAA read more probable under the decoy.**

---

# Now look at the observed sample

Suppose six reads came from the true genome:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

- `AAA` happened twice.
- Each other read type happened once.

This is a completely possible random sample from `AAATT`.

**But the random sample over-represents AAA.**

---

# The likelihood is just multiplication

Under the true genome, every observed read has probability $1/5$:

$$
P(R\mid S)=(1/5)^6
$$

Under the decoy, `AAA` has probability $2/6$ and the other reads have probability $1/6$:

$$
P(R\mid D)=(2/6)^2(1/6)^4
$$

We have multiplied **six ordinary sampling probabilities**.

---

# Surprise: the decoy wins

$$
\frac{P(R\mid D)}{P(R\mid S)}
=\frac{15625}{11664}\approx1.34
$$

The wrong genome gives this sample **about 34% more probability**.

It benefits from the extra `AAA` reads in this particular sample.

**Most likely is not the same as certainly true.**

*The exact comparison is certified by Lean.*

---

# The sample can change the verdict

If we observe each possible read type once instead:

```text
AAA   AAT   ATT   TTA   TAA
```

then the truth wins:

$$
\frac{P(R_5\mid D)}{P(R_5\mid S)}=\frac{3125}{3888}<1
$$

Repeat just one `AAA`, and the decoy wins:

$$
\frac{P(R_6\mid D)}{P(R_6\mid S)}=\frac{15625}{11664}>1
$$

**Same candidates. Same likelihood rule. Different read counts.**

---

# What if we had infinitely many reads?

With enough idealized sampling, the observed frequencies approach the **true read distribution**.

Random over- and under-representation disappear in that limit.

A candidate that predicts the true distribution cannot be outscored **on average** by one that predicts different probabilities.

**This is the great positive result behind population maximum likelihood.**

---

# Why is that result so general?

Maximum likelihood is based on a **proper scoring rule**: in the long run, you do best by predicting the probabilities that actually generate the data.

Mathematically:

$$
\ell_S(S)-\ell_S(D)
=D_{\mathrm{KL}}(p_S\|p_D)\geq0
$$

The right side is a nonnegative penalty for predicting the wrong read frequencies.

**The truth is always a population maximum-likelihood genome.**

No special repeat assumption is needed **just to attain the maximum**.

<!--
This compares expected log likelihood under the true distribution.
It assumes the candidate universe includes the truth, with the stated
error-free, oriented, fixed-length, uniform-start model.
-->

---

# But two genomes can make a tie

Consider two different circular genomes:

```text
AAACAC
AACAAC
```

Their length-2 reads occur with the same frequencies:

| Read | `AA` | `AC` | `CA` |
|:---|---:|---:|---:|
| Count in each genome | 2 | 2 | 2 |

Unlimited two-base reads **still cannot tell these genomes apart**.

**A unique best distribution need not imply a unique genome.**

---

# When can the truth be identified?

Our population theorem gives uniqueness under a precise repeat condition.

It considers oriented circular genomes that are:

- **Primitive:** the whole genome is not a shorter block repeated.
- **P2-admissible:** certain ambiguous repeat arrangements are excluded for the read length.

Within this class, the true genome is the **unique population maximum up to circular rotation**.

**Likelihood supplies maximality; repeat structure supplies uniqueness.**

---

# A finite positive theorem as well

Our research also proves a useful **finite-sample** structural result.

Under stronger hypotheses involving read bridging, an admissible truth, and **same-length oriented competitors**, the feasible read spectra are tightly constrained.

In that setting, the true genome is a maximum-likelihood solution, uniquely up to rotation under the theorem's stated conditions.

These are **restricted guarantees**, not claims about all finite samples or arbitrary candidates.

---

# What has been proved?

The project has machine-checked results for:

- A concrete **finite likelihood reversal**.
- A positive **structural rigidity** theorem.
- **Population maximum-likelihood uniqueness** in the primitive P2 class.

The mathematics is formulated and checked in **Lean**.

Our practical conclusions apply first to a deliberately simple sequencing model: circular genomes, equal-length error-free reads, and uniformly random starts.

---

# Three take-aways

1. **Short reads contain structural information.** Repeats can hide where fragments belong.
2. **Likelihood is a beautifully simple probability calculation.** It uses *how often* different reads were sampled.
3. **Finite and population likelihood differ.** Sampling luck can favor a decoy; with exact frequencies the truth always attains the maximum, and repeat structure decides whether it is unique.

**One simple statistical idea illuminates an entire reconstruction problem.**

---

layout: end
---

# Thank you

**[Paper, Lean proofs, and presentations](https://github.com/ottojung/assemblyp1)**

<HomeLink label="Choose another audience" />

---

# Backup: the observation model

- Circular DNA strings.
- Independent reads of fixed length $L$.
- Uniform random starting positions.
- Error-free, oriented read types.
- Genomes differing only by circular rotation are equivalent.

*These assumptions make exact theorems possible; real sequencing adds errors, biases, and longer-range evidence.*

---

# Backup: a separate same-length witness

With reverse-complement-collapsed molecule read types, another finite example uses:

- True genome `AAATAT`, length 6.
- Competitor `AAAAAT`, length 6.
- Reads of length 3.

The competitor's **exact likelihood is three times larger** under the specified molecule model.

The detailed hypotheses and the other likelihood objective are in the whitepaper.

---

# Backup: primary sources

- Medvedev & Brudno (2009), *Maximum Likelihood Genome Assembly*.
- Bresler, Bresler & Tse (2013), *Optimal assembly for high throughput shotgun sequencing*.
- Shomorony, Kim, Courtade & Tse (2016), *Information-optimal genome assembly via sparse read-overlap graphs*.
- Ukkonen (1992), *Approximate string-matching with q-grams and maximal matches*.

**[Research repository](https://github.com/ottojung/assemblyp1)**
