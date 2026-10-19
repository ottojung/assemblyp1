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
Lead with the sequencing model and the reconstruction story, then the
likelihood question. The core example uses only five possible read types. The
negative "decoy wins" example is a single short aside; the positive results
(unique spelling, population maximality, identifiability) carry the main arc.
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

*Assume error-free, oriented reads, with each start position equally likely and independent.*

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
Do not teach the Not-So-Greedy implementation in this talk. The key takeaway is
that there is a structural reconstruction result: bridging reads supply the
context that tells repeat copies apart.
-->

---

# The 2016 algorithm connects reads into a graph

A useful way to see the reconstruction: make a **graph whose nodes are the reads**.

- Draw an edge when two reads share a suffix–prefix overlap.
- Not-So-Greedy keeps the strongest overlap **and the first genuine alternative**.
- It removes misleading links and adjusts edge multiplicities.

Under the coverage and bridging conditions, that graph has a **unique Eulerian tour**, and the tour spells the true circular genome.

The tour is a function of the reads alone. So for one fixed set of reads, **at most one rotation class** can satisfy the reconstruction conditions — a *certificate about the observations*, not a claim that only one genome can produce the reads.

<!--
Cite Shomorony, Kim, Courtade & Tse (2016), Bioinformatics, DOI
10.1093/bioinformatics/btw450, Theorem 1 and its supplement. Present the idea,
not the internals: nodes are reads, edges are overlaps, and a unique Eulerian
tour spells the genome. This is distinct from the didactic de Bruijn graph
(where nodes are short k-mers).
Certificate multiplicity vs generative multiplicity: many genomes
(including nonrotational ones) can produce the SAME reads — see the
AAACAC/AACAAC example later in this talk, and the paper's extreme
case ex:ABAB (AAABAB vs AABAAB, identical 2-mer spectra). The
2016 guarantee constrains only which rotation class passes the
conditions on fixed observations. Honest labels: the unique-spelling
fact is the published 2016 premise (external); the at-most-one-class
conclusion is a paper-level corollary, not Lean-proved.
-->

---

# But the paper left another question

If the reads already contain enough information to reconstruct the genome...

**...must the true genome also be the most likely explanation of those reads?**

Those are **two different questions**.

- **Question A (conditional):** restrict candidates to those that already pass the reconstruction conditions — then the answer is the true circle, a corollary of the guarantee. (The conditions act as a *certificate about the reads*: for fixed observations, at most one rotation class can pass.)
- **Question B (unconditional):** without that restriction, must the true genome be most likely? **No** — the next slides show a decoy winning.

<!--
Mirrors the whitepaper's two-question narrative (paper sec:intro:two-questions,
sec:two-questions). Question A conditions on the truth-dependent feasible fiber
{g : F(g,R)} and is largely a corollary of the published 2016 reconstruction
theorem; Question B assumes only F(S,R) and maximizes the original unrestricted
likelihood, which is the substantive comparison. Ordinary ML never observes the
event E = F(S,R).
-->

---

# Maximum likelihood is simple

Imagine testing a proposed genome by repeating the sequencing experiment in your head.

1. How many start positions produce each read type?
2. How probable are the reads we actually saw?
3. Which candidate assigns the **highest probability** to the sample?

**Nothing more complicated than a set of probabilities and a product.**

**Why the highest-probability candidate?** If the candidates start out equally likely and every wrong answer costs the same, the most likely candidate is also the one that is right most often *on average*.

<!--
This is likelihood P(data | genome), not posterior probability P(genome | data).
Searching over all candidate genomes is a separate problem. Because a finite
sample fluctuates, the most likely genome need not be the true one; the next
slides make that precise.
Uniform start positions are not uniform read-type probabilities: the likelihood
scores each observed read string by the fraction of starts that produce it
(paper 02-model). The source's own objective is ambiguous — MB09 §6.1 uses a
fixed-N product-binomial surrogate and §6.2 a flow likelihood — and neither is
the exact iid multinomial used here; none of these is kernel-checked. One
specific transport discipline for the §6.2 flow likelihood is now kernel-checked
and refuted (#338): a reversal-symmetric flow on the minimal length-1
mixed-sign self-loop always has even inherited departure throughput, so it
cannot realize the unit physical loop flow (quotient-orbit visit count one);
`AssemblyP1.Section62ReversalOrbitTransport.symmetric_discipline_refuted`
(audit: `AssemblyP1.Section62ReversalOrbitTransportAudit`). The full §6.2
source-graph correspondence remains open.
Bayes-optimality is prior-averaged: with a uniform prior and 0-1 loss, MAP/ML
maximizes the average chance of being right, and the kernel-checked certificate
(BayesOptimalityCertificate) adds that a rule missing a per-observation
maximizer is strictly worse, ties allow several optimal rules, and a strict
maximizer forces the choice. This still says nothing for one fixed truth.
-->

---

# Two genomes make different predictions

**Truth:** `AAATT` — five equally likely start positions.

**Decoy:** `AAAATT` — six equally likely start positions.

Each genome predicts these read frequencies:

| Read type | Under $S$ | Under $D$ |
|:---|---:|---:|
| `AAA` | $1/5$ | $2/6$ |
| `AAT` | $1/5$ | $1/6$ |
| `ATT` | $1/5$ | $1/6$ |
| `TTA` | $1/5$ | $1/6$ |
| `TAA` | $1/5$ | $1/6$ |

**The extra A makes an AAA read more probable under the decoy.**

---

# The likelihood is just multiplication

Suppose six reads came from the true genome, and `AAA` happened twice:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

Under the true genome every observed read has probability $1/5$; under the decoy, `AAA` has probability $2/6$ and the others $1/6$:

$$
P(R\mid S)=(1/5)^6
\qquad
P(R\mid D)=(2/6)^2(1/6)^4
$$

We have multiplied **six ordinary sampling probabilities**.

---

# A finite aside: the decoy can win

$$
\frac{P(R\mid D)}{P(R\mid S)}
=\frac{15625}{11664}\approx1.34
$$

The wrong genome gives **this** sample about **34% more probability**, because the sample over-represents `AAA`.

**Most likely is not the same as certainly true.**

With enough idealized sampling, the over- and under-representation disappears, and the truth wins (next slides). The exact likelihood ratio is certified by Lean.

<!--
This is the one negative aside in the main deck. If every read type is observed
once instead, the truth wins (ratio 3125/3888 < 1); repeat one AAA and the decoy
wins. Same candidates, same rule, different read counts. An optimal estimator is
not an infallible estimator. The full finite reversal calculation is in backup.
The source-faithful same-length witness is AAATAT vs AAAAAT (exact ratio 3).
-->

---

# What if we had infinitely many reads?

With enough idealized sampling, the observed frequencies approach the **true read distribution**.

Random over- and under-representation disappear in that limit, and a candidate that predicts the true distribution cannot be outscored **on average** by one that predicts different probabilities.

Mathematically, the expected log-likelihood gap is a KL divergence:

$$
\ell_S(S)-\ell_S(D)
=D_{\mathrm{KL}}(p_S\|p_D)\geq0
$$

**The truth is always a population maximum-likelihood genome.**

For a **finite identifiable family**, the same KL gap makes the limit *eventual and exact*: almost surely, the ML selection set is eventually exactly the truth's rotation class (strong law + KL; classical, not kernel-checked — backup). "Infinite reads" is a limit of finite samples; it supplies **no finite read count**.

<!--
This compares expected log likelihood under the true distribution. It assumes the
candidate universe includes the truth, with the stated error-free, oriented,
fixed-length, uniform-start model. The inequality is KL nonnegativity (Cover &
Thomas 2006); the kernel form is PopulationGibbs.popLogLik_le_self'. No special
repeat assumption is needed just to attain the maximum; equality means the two
genomes induce the same read distribution. "Infinite reads" is a limit, not an
infinite product of probabilities. The eventual-exactness strengthening for a
finite identifiable family (strong law + KL; classical, not kernel-checked;
no finite n supplied) is paper prop:strong-consistency; see the backup
slide "The limit is eventual - and gives no finite number".
#265 exact finite-n pointer (2026-10-18): the limit above gives no finite n, but
for one explicit finite read-law family the tight 99% sizes are n*=85
(prior-averaged) and n*=87 (minimax-over-truths), against the kernel-checked
Hellinger sufficient 153; see the sample-complexity backup and
docs/minimax-finite-recovery-265.md. The exact numbers are external decision
theory, not Lean.
-->

---

# When can the truth be identified?

Two different circular genomes can still make a tie. Consider:

```text
AAACAC
AACAAC
```

Their length-2 read frequencies agree exactly, so unlimited two-base reads cannot tell them apart.

**A unique best distribution need not imply a unique genome.** This is **generative multiplicity**: the rotation class of any genome always produces the same distribution, and nonrotational genomes can too, as here.

Our population theorem gives uniqueness under a precise repeat condition: oriented circular genomes that are

- **primitive:** the whole genome is not a shorter block repeated;
- **P2-admissible:** certain ambiguous repeat arrangements are excluded for the read length.

Within this class the true genome is the **unique population maximum up to circular rotation**.

<!--
Kernel endpoint: Issue94Complete.population_unique_ML, fully kernel-checked with
no external premise, under primitive + P2 + the admissible candidate class +
L >= 2; the equality characterization is PopulationGibbs.popTie_iff. Likelihood
supplies maximality; repeat structure supplies uniqueness. State the qualifiers;
without them distinct non-rotation genomes can tie. Keep this generative
multiplicity (what can produce the same reads) distinct from certificate
multiplicity (which rotation class satisfies the 2016 guarantee on fixed
observations — at most one, per the algorithm slide).
-->

---

# A finite positive theorem as well

Our research also proves a useful **finite-sample** structural result.

Under stronger hypotheses involving read bridging, an admissible truth, and **same-length oriented competitors**, the feasible read spectra are tightly constrained: the truth's window spectrum is the **unique positive integer circulation** of its support graph.

In that setting the true genome is a maximum-likelihood solution, uniquely up to rotation under the theorem's stated conditions.

**These are restricted guarantees** — not claims about all finite samples or arbitrary candidates.

<!--
Kernel endpoints: OrientedRigidity.unique_positive_circulation;
SameLength62Uniqueness.unique_62_maximizer_up_to_rotation (unconditional
rotation); OrientedFinal.oriented_same_length_spectrum_rigidity. The equal-length
restriction is essential: dropping it restores strict finite counterexamples.
The general Graver-basis criterion (GraverRigidity) is a separate iff.
-->

---

# Three take-aways

1. **Short reads contain structural information.** Overlaps and bridging resolve repeats; under precise conditions they determine a unique circular genome (Question A, the conditional guarantee).
2. **Likelihood is a beautifully simple probability calculation.** It uses *how often* different reads were sampled.
3. **Finite and population likelihood differ.** Sampling luck can favor a decoy in a finite sample (Question B, the unconditional comparison); with exact frequencies the truth always attains the maximum, and repeat structure decides whether it is unique. For our structural class the finite-sample error probability obeys an explicit kernel-checked exponential bound (backup).

**One simple statistical idea illuminates an entire reconstruction problem.**

<!--
The project's machine-checked results span: a concrete finite likelihood
reversal (SameLengthSection62Counterexample), positive structural rigidity
(OrientedRigidity), and population maximum-likelihood uniqueness in the
primitive P2 class (Issue94Complete.population_unique_ML). The practical
conclusions apply first to a deliberately simple sequencing model: circular
genomes, equal-length error-free reads, and uniformly random starts. A sharp
uniform sample size ("how many reads for 99%?") over the unrestricted genome
universe is not merely open - it is FALSE: a genome and its repetition share a
read law at every length (merged #355, AB vs ABAB), so no positive uniform rate
exists there, and the 1/(8B^4) exponent is not tight. A length bound plus
exclusion of read-law duplicates restores the rate (primitive-P2 supplies both);
the sharp constant stays open. The finite-family Hellinger/Chernoff bound in
backup is a scoped sufficient answer.
-->

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

# Backup: how many reads for 99% recovery?

The limit theorem gives convergence, not a finite sample size. For a finite distinguishable family, the exact iid likelihood obeys a Hellinger/union bound:

$$
\Pr_\theta[\text{a wrong genome ties or beats the truth}]
\;\le\; |\mathcal C|\,\rho_*^{\,n},
\qquad 0\le\rho_*<1 .
$$

Inverting it gives a **sufficient** number of reads for a target bound $\delta$:

$$
n \;\ge\; \frac{\ln(|\mathcal C|/\delta)}{\ln(1/\rho_*)} .
$$

This bound is kernel-checked for a finite family.

For our **primitive-P2** class the abstract gap is now **explicit and kernel-checked**. With alphabet size $q$, read length $L\ge2$, and $B=2q^{L-1}$:

$$
\Pr_S[\exists\,D\ \text{nonrotational admissible}:\ L_D\ge L_S]
\;\le\; N_C\,\exp\!\left(-\frac{n}{8B^4}\right),
\qquad N_C\le\sum_{g=1}^{B}q^{g},
$$

where $N_C$ counts the distinct competitor read laws. A sufficient read count is $n\ge 8B^4\ln(N_C/\delta)$ for error at most $\delta$.

**Caveats.** The constants are deliberately loose and exponential in $L$; the bound controls the exact-ML **error probability**, not likelihood growth; and per-truth finite-sample success is **not monotone**. Kernel endpoints: `AssemblyP1.PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound`, `primitiveP2_ML_confidence_explicit` (paper `thm:p2-uniform-rate`).

A uniform rate over **all** genome lengths is **false**: a genome and its repetition can share a read law at every length (`AB` vs `ABAB`), forcing error `1` for every sample size; and the exponent here is **not tight**. Restoring the rate needs a **length bound** plus **no duplicate read laws**, which the primitive-P2 class supplies (merged #355; exact verifier, not kernel-checked). The *sharp* constant remains a genuinely open quantitative problem.

<!--
#265 Chernoff refinement (2026-10-18): the Hellinger constant -ln rho_* can be
replaced by the Chernoff information C_* = min_D C(p_S,p_D), with
C(p,q) = sup_{t in [0,1]} -ln sum_{w:p(w)>0} p(w)^(1-t) q(w)^t >= -ln rho(p,q).
The Chernoff union bound sum_D exp(-n C(p_S,p_D)) is termwise no larger, and
C_* is the exact large-deviation exponent of the finite-family exact-ML error
(standard Chernoff/Sanov; EXTERNAL, not kernel-checked). It is still not tight
at finite n: on the worked family p=(3/4,1/4), competitors (1/4,3/4) and (0,1),
the bound is ~3.7x the exact error at n=16 and the ratio grows ~sqrt(n). Paper
prop:chernoff-refinement / rem:chernoff-sharp; note
docs/chernoff-exponent-finite-recovery-265.md; exact check
scripts/verify_chernoff_finite_recovery_265.py. Do NOT claim a tight or minimax
finite-n bound, and do NOT claim C_* is kernel-checked; the kernel-checked
constant remains rho_* (FiniteReadRecovery).
#265 exact finite-n numbers (2026-10-18): for one explicit finite family of
binary read laws A=(1/2,1/2), B=(3/4,1/4), C=(1/4,3/4) the tight 99% recovery
sizes are EXACT (standard decision theory + exact arithmetic; NOT Lean): n*=85
for the uniform-prior Bayes optimum (V_84<0.99<=V_85=0.99006833) and n*=87 for
the minimax-over-truths optimum (error_86=0.01051594>0.01>=error_87=
0.00973853). The kernel-checked Hellinger bound above gives a conservative
sufficient size 153; evaluated at n=85 that bound value is about 6.4x the
exact per-truth error of the middle truth.
This is prior-AVERAGED: at n=85 the per-truth successes are A=0.983491 <
B=C=0.993357 (average V_85), so "99% recovery" is about the average, not each
truth, and per-truth success is not monotone. Scope: one explicit finite family
under the iid read-law model, not the unrestricted genome universe and not
MB09. Only the abstract Bayes-optimality (FiniteBayesDecision /
FiniteMapOptimality) and the Hellinger union bound (FiniteReadRecovery) are
kernel-checked. Verifier scripts/verify_minimax_finite_recovery_265.py; paper
rem:minimax-sample-size; note docs/minimax-finite-recovery-265.md.
#265 exponent findings (merged PR #355, 2026-10-19): the uniform rate over the
UNRESTRICTED universe is FALSE, not merely open. A genome and its m-fold
repetition share the same oriented read law at EVERY length (AB vs ABAB), so the
truth's own read law is a candidate and the exact-ML error is 1 for every n: no
exp(-c n) bound with c>0 and no consistency. Hand proof + exact verifier
scripts/verify_exponent_265.py (NOT kernel-checked). Even among primitive
competitors the separation vanishes: D_m=(AB)^m A has
1-rho(p_AB,p_{D_m}) -> 0 (0.1835 at m=1 to 0.0299 at m=8). The primitive-P2
exponent 1/(8B^4) is also NOT tight: exact enumeration gives worst-case
separation gamma(B)=Theta(1/B), exceeding the bound by 274, 903, 2116, 16648 at
B=4,6,8,16. Restoring the uniform rate needs a length bound plus exclusion of
read-law duplicates - exactly what primitive-P2 supplies. The sharp asymptotic
Theta(1/B) is a CONJECTURE with a named missing lemma. Sources:
docs/restricted-vs-unrestricted-exponent-265.md. thm:p2-uniform-rate stays
correct and kernel-checked; #355 only shows its exponent is conservative. No
external statistics is upgraded to Lean.
-->

---

# Backup: more reads help on average, not always

More reads cannot lower the **average** chance of guessing the genome correctly: an algorithm may simply ignore the extra read.

But for one **fixed** true genome, the chance of being the maximum-likelihood answer can go **down** when a read is added.

Two circular genomes, read length 2, alphabet `{A, C}`:

| | `AA` | `AC` | `CA` | `CC` |
| --- | ---: | ---: | ---: | ---: |
| Truth `AAC` | $1/3$ | $1/3$ | $1/3$ | $0$ |
| Competitor `AAAC` | $1/2$ | $1/4$ | $1/4$ | $0$ |

The truth wins strictly with probability $2/3$ after **one** read but only $4/9$ after **two**. With many reads the probability still returns to $1$.

**More reads guarantee eventual success, not a steady climb.**

<!--
Prior-averaged success is nondecreasing in the read count; per-truth success
need not be. Kernel endpoints: chooseMAP_success_monotone_under_refinement
(average) and NonmonotonicityWitness281.success_not_monotone (per-genome),
succ(1)=2/3 > succ(2)=4/9. No positive-probability ties for n>=1. This is the
biologists-deck analogue of the programmers Backup B4.
-->

---

# Backup: the limit is eventual - and gives no finite number

For a **finite identifiable family**, each per-read log-likelihood gap is an average of independent terms whose expectation is a KL divergence. The strong law turns that into an almost-sure limit:

$$
\frac1n\log\frac{L_S}{L_D}(R_1,\dots,R_n)
\;\xrightarrow{\text{a.s.}}\;
D_{\mathrm{KL}}(p_S\|p_D)>0 .
$$

Every wrong candidate has KL $>0$; there are finitely many, so almost surely the truth beats **all** of them simultaneously from some read count $N$ onward. Rotations of the truth tie it at every count (identical read laws). The ML selection set is therefore **eventually exactly the truth's rotation class**, and the probability of being correct tends to $1$.

**Limit, not an infinite product.** The statement is about finite samples growing without bound. It supplies no finite read count, no rate, and no guarantee for a particular sample, a fixed truth, or an unrestricted candidate universe. It is distinct from population uniqueness above, which involves no sampling at all. Classical statistics (strong law + KL nonnegativity; Durrett 2019, Cover & Thomas 2006), **not kernel-checked**; the kernel-checked Hellinger bound reaches the same conclusion because its series $\sum_n \rho^n$ is summable (Borel--Cantelli).

<!--
#265 item-5 limit statement, paper prop:strong-consistency (Section
sec:strong-consistency). Hypotheses: finite candidate family identifiable
modulo rotation, iid exact reads, correct model. Proof: strong law on the
per-read log-likelihood average + KL positivity (equality iff read laws agree)
+ finite union over wrong candidates; rotations tie at every n by design;
nonrotational ties impossible eventually since the limit separates strictly.
Support convention 0 log 0 = 0; if p_D(w)=0 < p_S(w) then KL = +infinity
and that competitor loses on every sample containing w, which recurs
eventually. Witness numbers (AAC vs AAAC, L=2, binary alphabet): KL =
(1/3)log(2/3)+(2/3)log(4/3) ~ 0.0566 > 0, Hellinger affinity
(1+sqrt(2))/sqrt(6) ~ 0.9856 < 1, geometric series summable. Exact checks:
scripts/verify_strong_consistency_265.py (success table, boundary
a < n(2-log2 3), rotation ties, summability). Sample complexity remains
open: the limit gives no finite n.
-->

---

# Backup: primary sources

- Medvedev & Brudno (2009), *Maximum Likelihood Genome Assembly*.
- Bresler, Bresler & Tse (2013), *Optimal assembly for high throughput shotgun sequencing*.
- Shomorony, Kim, Courtade & Tse (2016), *Information-optimal genome assembly via sparse read-overlap graphs*.
- Ukkonen (1992), *Approximate string-matching with q-grams and maximal matches*.

**[Research repository](https://github.com/ottojung/assemblyp1)**
