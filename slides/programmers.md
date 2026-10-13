---
theme: default
title: "AssemblyP1 — Results for Programmers"
info: |
  A reproducible likelihood counterexample, a general statistical guarantee,
  and Lean-verified results about genome assembly.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# A correct score can prefer the wrong genome

### One tiny model · one surprising counterexample · two kinds of guarantee

**AssemblyP1 — the discoveries and how we verified them**

<HomeLink label="Choose another audience" />

<!--
This is a research presentation to general programmers, not a tutorial
on the internals of a specialist assembly algorithm.
-->

---

# The results, up front

1. **A wrong genome can score higher** than the true one on a finite read sample. We have an exact, machine-checked example.
2. **The true genome always maximizes population likelihood** when read frequencies are known exactly. A one-line probability inequality explains why.
3. **Uniqueness needs more information.** Under explicit repeat conditions, the true genome is the only population maximizer, up to rotation.

These are three different claims. The differences matter.

---

# The research workflow

```text
Specify an idealized read generator
                 ↓
Write down a precise likelihood score
                 ↓
Search small inputs for surprising cases
                 ↓
State general theorems with exact assumptions
                 ↓
Prove them in Lean → replay in CI
```

**A familiar engineering pattern:** executable examples expose edge cases; proofs establish what holds for an entire class of inputs.

<!--
Testing and theorem proving have different scopes. We used agents to
explore candidate results, but Lean's kernel checks final statements.
-->

---

# The input: a bag of short strings

Our model uses a circular genome, say `AAATT`.

A read of length 3 starts at a uniformly random position and takes three letters, wrapping around the end.

| Start | Result |
|---:|:---|
| 0 | `AAA` |
| 1 | `AAT` |
| 2 | `ATT` |
| 3 | `TTA` |
| 4 | `TAA` |

We see the reads, **not** the starting positions.

<!--
The model uses independent, error-free, oriented fixed-length reads.
The five strings are the complete length-3 cyclic windows of AAATT.
-->

---

# Treat each genome as a generator

A candidate genome induces a probability distribution over possible reads.

For instance, in `AAATT`, exactly one of five start positions produces `AAA`:

$$
P(\texttt{AAA}\mid \texttt{AAATT})=\frac15
$$

In `AAAATT`, two of six start positions do:

$$
P(\texttt{AAA}\mid \texttt{AAAATT})=\frac26
$$

**Different strings can predict different frequencies**, even when they can generate the same read types.

---

# The scoring function is tiny

```ts
function readProbability(genome: string, read: string) {
  const windows = [...genome].map((_, start) =>
    Array.from(read, (_, i) =>
      genome[(start + i) % genome.length]).join("")
  )
  return windows.filter(w => w === read).length / genome.length
}

function likelihood(genome: string, reads: string[]) {
  return reads.reduce((p, r) => p * readProbability(genome, r), 1)
}
```

Count matching circular windows; multiply their probabilities.

**Scoring a candidate is simple. Finding the best candidate is a separate problem.**

<!--
The code is self-contained TypeScript with simple array operations.
Products can underflow for long samples; production code typically
sums log-probabilities. This does not search over candidate genomes.
-->

---

# Our test fixture

The observed reads:

```text
AAA  AAA  AAT  ATT  TTA  TAA
```

Two candidates:

- **Truth:** `AAATT`, length 5
- **Competitor:** `AAAATT`, length 6

`AAA` occurs twice in the sample. Every other read type occurs once.

**Question:** Which candidate does the scoring function prefer?

---

# The probability table

| Read | Truth `AAATT` | Competitor `AAAATT` |
|:---|---:|---:|
| `AAA` | $1/5$ | $2/6$ |
| `AAT` | $1/5$ | $1/6$ |
| `ATT` | $1/5$ | $1/6$ |
| `TTA` | $1/5$ | $1/6$ |
| `TAA` | $1/5$ | $1/6$ |

Nothing fancy: **count matching start positions, then divide by genome length**.

That extra `A` creates two positions producing `AAA` instead of one.

---

# Multiply the factors

For the six observed reads:

$$
P(R\mid \texttt{AAATT})=(1/5)^6=\frac{1}{15625}
$$

$$
P(R\mid \texttt{AAAATT})=(2/6)^2(1/6)^4=\frac{1}{11664}
$$

The competitor gets more credit for the **twice-observed** `AAA`.

The calculation is simple enough to check by hand or in a unit test.

---

# The unexpected result

$$
\frac{P(R\mid \texttt{AAAATT})}{P(R\mid \texttt{AAATT})}
=\frac{15625}{11664}\approx1.34
$$

**The wrong genome wins by about 34%.**

The true genome generated the sample, but a different candidate happens to explain this particular sample better.

This is an **exact finite counterexample**, verified in Lean.

<!--
The input is valid under the oriented, independent uniform-start model,
where competitors of different lengths are allowed.
-->

---

# Flip one count, flip the result

With five reads, each type appearing once:

```text
AAA  AAT  ATT  TTA  TAA
```

the truth wins:

$$
\frac{P(R_5\mid D)}{P(R_5\mid S)}
=\frac{3125}{3888}<1
$$

Duplicate `AAA` and the competitor wins:

$$
\frac{P(R_6\mid D)}{P(R_6\mid S)}
=\frac{15625}{11664}>1
$$

**The objective didn't change; only the sample did.**

<!--
The five-read ratio is an exact arithmetic calculation, distinct
from the kernel-certified six-read example.
-->

---

# This is not a scoring bug

Likelihood answers the question:

> Which candidate assigns the highest probability to the data I actually observed?

It does **not** promise:

> Every random sample will identify the process that generated it.

That distinction should feel familiar: **passing a test case is not the same as proving a universal property**.

So what *can* we guarantee?

---

# A remarkably strong population result

Suppose sampling noise disappears: we know the true distribution of reads exactly.

Let $p_S(w)$ be the true frequency of read $w$, and $p_D(w)$ the candidate's frequency.

The average log-score of a candidate is

$$
\ell_S(D)=\sum_w p_S(w)\log p_D(w)
$$

The important identity is:

$$
\ell_S(S)-\ell_S(D)=D_{\mathrm{KL}}(p_S\|p_D)\ge0
$$

**The truth always attains the population maximum.**

No special repeat or bridging condition is needed for this *maximality* claim.

<!--
Gibbs' inequality establishes the nonnegativity.
A candidate with zero probability for a true read has
minus-infinity expected log-likelihood.
-->

---

# Same probabilities, different genomes

Two different circular genomes can generate **the same read distribution**.

```text
AAACAC
AACAAC
```

Both have the same length-2 read counts:

| Read | `AA` | `AC` | `CA` |
|:---|---:|---:|---:|
| Count | 2 | 2 | 2 |

These strings are not rotations of each other, yet their probabilities agree.

**The statistical optimum can be tied.** Distinguishing genomes is an additional structural problem.

---

# Where uniqueness comes from

AssemblyP1 proves a stronger result for a carefully defined class of genomes:

- **Primitive:** a genome is not a shorter string repeated multiple times.
- **P2-admissible:** certain confusing repeat patterns are excluded for the chosen read length.
- **Oriented, circular:** rotations are equivalent; reverse complements are not merged.

Within that class, the **population maximizer is unique up to rotation**.

**The probability argument gives the optimum; the repeat theorem identifies its genome.**

---

# A separate positive finite theorem

Finite likelihood is not always ambiguous.

Under stronger **bridging and read-support hypotheses**, our rigidity result constrains the possible read spectra.

For the theorem's **same-length, oriented candidate class**, these constraints can prevent a candidate from getting a strictly better finite likelihood.

This is an important positive result — **not** a claim about every possible genome or every sampling model.

<!--
See the paper's complete hypotheses for the positive balanced-flow result.
Do not silently broaden this to variable-length competitors.
-->

---

# What did Lean actually buy us?

**Executable test:** the six-read counterexample works for these particular inputs.

**Kernel-checked theorem:** a proof can establish a statement for every input satisfying its stated assumptions.

The project contains checked results for:

- An exact **finite likelihood reversal**
- Conditional **read-spectrum rigidity**
- **Population-likelihood uniqueness** for the primitive P2 class

The theorem statement is the contract. The Lean kernel checks that the proof matches it.

---

# What to take away

**The score is almost trivial. The guarantees are not.**

- Small, reproducible examples can defeat plausible universal conjectures.
- A correct objective can disagree with the true generator on finite observations.
- A general statistical identity gives population maximality immediately.
- Getting **uniqueness** needs precise structural assumptions.
- Formal proofs make those assumptions part of the result, not footnotes.

The interesting discovery is the boundary between these statements.

---

layout: end
---

# Paper, code, reproducible results

**[github.com/ottojung/assemblyp1](https://github.com/ottojung/assemblyp1)**

<HomeLink label="Choose another audience" />
