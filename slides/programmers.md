---
theme: default
title: "Genome Assembly and Maximum Likelihood"
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

# Genome Assembly and Maximum Likelihood

### A mathematical research investigation

**AssemblyP1** · A research investigation

<HomeLink label="Choose another audience" />

<!--
This is not an algorithm lecture or a progress report about software agents.
Begin with the scientific problem and develop the research question naturally.
-->

---

# The puzzle: DNA fragments without a map

A genome is a very long string made from the DNA letters **A, C, G, T**. Sequencing gives us short pieces, called **reads**, rather than the whole string.

Suppose the sequencer produces these reads, in no particular order:

~~~text
GTA      AAC      CGT      TAA      ACG
~~~

We don't know which read came first—or where any read belongs.

**Our task:** reconstruct the original circular genome from these pieces.

<!--
This slide shows INPUT and GOAL, not an algorithm. The hidden circular
source is ACGTA; the reads are deliberately unordered.
-->

---

# The mathematical version of genome assembly

This project studies an idealized problem, **not** the practical details of real sequencing.

We assume:

- A genome is a **circular string**.
- Reads have a **fixed length**, a known direction, and **no errors**.
- Every read starts at a **uniformly random position**, independently of the others.

This simple model allows us to prove statements about **which assemblies are possible**, and about **how likely each genome is to produce the observed reads**.

<!--
All main examples use oriented reads, including the variable-length
finite counterexample and later population theorem. The historical
reverse-complement molecule model is documented separately in the notes.
-->


---

# A first attempt: join the overlaps

The end of **ACG** matches the beginning of **CGT**: both share **CG**.

The other reads fit together in the same way:

~~~text
ACG → CGT → GTA → TAA → AAC → ACG
~~~

Each arrow joins reads sharing a two-letter overlap. Following the arrows spells **ACGTA**.

**We've reconstructed a circular genome!** This is the basic idea behind overlap-based assembly.

<!--
Read-overlap graph: vertices are reads, not (L-1)-mers.
AAC -> ACG closes the circular sequence. Not a de Bruijn graph.
-->

---

# What if an overlap has several choices?

Suppose our reads include **CAT, ATG, ATC, ATA**.

**CAT** ends in **AT**, and all three other reads begin with **AT**:

~~~text
           ┌→ ATG
CAT ───────├→ ATC
           └→ ATA
~~~

Every arrow is locally valid. **Which one is correct?**

Genomes contain **repeated substrings**. An overlap may match the wrong copy of a repeat.

A read extending beyond both ends of a repeat can distinguish copies; we say it **bridges** the repeat.

<!--
Introduce complications only after successful assembly. All these read types
appear in the following ambiguity example. The arrows are
possible overlaps, not all realized at one physical genome position.
-->

---


# Sometimes even all short reads are ambiguous

These ten length-3 reads, including repeated occurrences:

~~~text
ATG  TGA  GAT  ATC  TCA  CAT  ATA  TAT  ATA  TAT
~~~

come from **either** of two circular genomes:

~~~text
ATGATCATAT
ATGATATCAT
~~~

The genomes are **not rotations** of one another. Yet they produce exactly the **same length-3 reads with the same multiplicities**.

**No algorithm can distinguish them from those reads alone.**

We need conditions that prevent this kind of ambiguity.

<!--
Exact circular length-3 read counts: ATA and TAT twice; each of
ATG/TGA/GAT/ATC/TCA/CAT once. Not a counterexample to the
2016 algorithmic theorem because its bridging hypotheses do not hold.
-->

---

# Not-So-Greedy: a reconstruction guarantee

Shomorony and colleagues (2016) developed an algorithm using a **sparse read-overlap graph**. Under suitable conditions, it reconstructs the **unique true circular genome, up to rotation**.

1. **Coverage:** reads cover the genome.
2. **Triple repeats:** every copy is bridged.
3. **Interleaved repeats:** at least one repeat in every interleaved pair is bridged.

These repeat-and-bridging conditions build on **Bresler, Bresler & Tse (2013)**. The 2016 result makes them a **reconstruction guarantee**, not just a heuristic.

<!--
The source information-feasible set I_s includes the three clauses
with strict bridging (read extends on both sides of a copy).
BBT 2013 is the repeat/bridging origin; the read-overlap algorithm
is Shomorony et al. 2016. Unique recovery is Corollary 1, distinct
from the weaker existence theorem. The source theorem itself is
an external premise, not Lean-proved in this project.
-->

---

# Another approach: how likely are these reads?

Instead of joining reads by overlaps, we can compare **candidate genomes** by asking how likely each would be to produce the observations.

In our model, a read starts at a uniformly random position on a circle. Its probability is **exactly the fraction of starting positions that produce it**.

For the observed read `AAA`:

```text
Genome A: AAATT     1 of 5 positions -> P(AAA | A) = 1/5
Genome B: AAAAT     2 of 5 positions -> P(AAA | B) = 2/5
```

This is a probability **of the read if the genome is given**. It is **not yet** the probability that the genome is correct.

<!--
The circular starts are equiprobable by model assumption. A yields AAA at
one of five starts; B at two of five. This does not assume read types themselves
are uniformly distributed.
-->

---

# From a read probability to a genome probability

Suppose there are **only two candidates, A and B**, and before sequencing we treat them as equally likely.

Nature picks one of the two genomes, then one of its five read positions: **ten equally likely possibilities**.

After observing `AAA`, only three possibilities remain:

```text
A = AAATT   1 possible starting position
B = AAAAT   2 possible starting positions
```

So the probability that **B is the true genome**, *given this observation*, is **2/3**; for A, **1/3**.

**This is not a mysterious conversion of frequencies into truth probabilities:** it is counting the possible ways the data could have arisen.

<!--
Prior P(A)=P(B)=1/2. Ten equally likely (genome, start) pairs. One compatible
A pair and two B pairs. P(B|AAA)=(2/10)/(1/10+2/10)=2/3.
"Prior" means before reads; "posterior" means after reads.
-->

---

# More reads: count pairs of possible positions

Now suppose we independently observe **two reads, both `AAA`**.

Each genome has 5 × 5 = 25 *ordered pairs of starting positions*.
With our equal prior, there are 50 equally likely possibilities.

```text
A = AAATT   1 × 1 = 1 pair produces [AAA, AAA]
B = AAAAT   2 × 2 = 4 pairs produce [AAA, AAA]
```

Of the five compatible possibilities, **four belong to B**.

So the probability that B is the true genome rises to **4/5 = 80%**.

With many independent reads we **multiply** their probabilities under each candidate, then **normalize across candidates** using our assumed prior.

<!--
A likelihood = (1/5)^2 = 1/25. B likelihood = (2/5)^2 = 4/25.
Posterior(B)=(1/2*4/25)/(1/2*1/25+1/2*4/25)=4/5.
Conditional independence justifies multiplication; without it, use a joint
read model instead. Unequal priors change the normalization.
-->

---

# What that calculation looks like in TypeScript

~~~ts
const genomes = ["AAATT", "AAAAT"];
const reads = ["AAA", "AAA"];

function likelihood(g: string): number {
  return reads.reduce((p, r) => {
    const starts = [...g].filter((_, i) =>
      [...r].every((c, j) => g[(i + j) % g.length] === c)
    ).length;
    return p * starts / g.length;
  }, 1);
}

const weights = genomes.map(likelihood);
const total = weights.reduce((a, b) => a + b, 0);
console.log(weights.map(w => Number((w / total).toFixed(2))));
// [ 0.2, 0.8 ]
~~~

The last line computes **posterior probabilities with equal priors**, rounded for display.

<!--
Original JS floating-point output was 0.19999999999999998 and
0.7999999999999999. Number(toFixed(2)) prints numeric
0.2 and 0.8 as the comment states. The likelihood products
are conceptual floating-point values; for many reads use log likelihood.
-->

---

# What does it mean for an assembly algorithm to be better?

An algorithm sees the **reads** and guesses which genome produced them.

To compare algorithms, imagine repeating the **whole experiment**:

1. Pick the true genome: **A or B, equally likely**.
2. Draw two random reads from it.
3. Let each algorithm guess the genome from those reads.

**Score:** how often does the algorithm guess correctly?

For the reads **AAA, AAA**, we calculated that **B is the true genome in 80%** of experiments producing those reads. Guessing B is therefore the better decision **for this observation**.

<!--
The comparison criterion is prior-averaged 0-1 correctness: draw a genome
from the stated equal prior, independently sample two reads, and score
one if the algorithm's guess matches the hidden genome.
There are 2 * 5^2 = 50 equally likely latent (genome, start-pair)
histories. Only five produce [AAA, AAA]: one from A and four from B.
The conditional 80% is not a guarantee for a fixed true genome.
-->

---

# Counting the decisions an algorithm can get right

There are **50 equally likely experiments**: two equally likely true genomes, each with 25 possible pairs of read starts.

Group the experiments by the **reads the algorithm sees**. Here are four example rows:

| Reads observed | True A | True B | Best guess |
| --- | ---: | ---: | --- |
| `AAA, AAA` | 1 | **4** | **B** |
| `AAA, AAT` | 1 | **2** | **B** |
| `AAA, ATT` | **1** | 0 | **A** |
| `AAT, TAA` | 1 | 1 | Either |

The algorithm cannot distinguish experiments in the same row. **Guess A, and it gets the A count correct; guess B, and it gets the B count.**

So **the best possible score for any row is its larger count**.

<!--
These are ordered read pairs (not unordered bags), and each A/B
latent pair of read-start positions is equiprobable. A=AAATT and
B=AAAAT, both length five. Circular read-type counts:
A: AAA,AAT,ATT,TTA,TAA each once.
B: AAA twice, AAT once, ATA once, TAA once.
Thus read-pair counts are products of type counts; all four table
rows can be verified directly. The remaining observation rows are
treated by the general argument on the next slide.
-->

---

# The proof: choose the best guess for every observation

**Every experiment belongs to exactly one row.** To count an algorithm's correct answers, add the count it gets right in **each** row.

For any algorithm $f$, let $n_A(r)$ and $n_B(r)$ be the counts for observed reads $r$. Then:

$$
\underbrace{\frac1{50}\sum_r n_{f(r)}(r)}_{\text{accuracy of }f}
\;\le\;
\underbrace{\frac1{50}\sum_r\max\{n_A(r),n_B(r)\}}_{\text{best possible accuracy}}.
$$

**Why does ML reach the upper bound?** A genome has 25 possible pairs of starting positions. So the likelihood of $r$ is its row's count **divided by 25**.

Choosing the **larger likelihood** therefore chooses the **larger count, in every row**.

That is ML's decision rule. **No other algorithm can achieve higher average accuracy** under the assumed equal prior (ties are possible).

<!--
Formal generalization: with finite candidates H, prior π, and 0–1 loss,
accuracy(f) = Σ_r π(f(r)) P(r|f(r))
            ≤ Σ_r max_g π(g) P(r|g).
MAP attains the bound for any prior. Equal priors make MAP=ML,
even when candidates have different lengths (there the raw counts
must first be converted to candidate-relative probabilities).
The displayed 50-history argument works because A and B both have
five positions and the prior is uniform. Randomization cannot
improve on the per-row maximum. Lean FiniteBayesDecision.lean.
Prior-averaged optimality does not imply success for each fixed truth.
-->

---

# The 2016 question: does the guarantee imply ML?

We have **two methods**:

**Not-So-Greedy:** reconstruct by overlaps when the coverage and repeat-bridging conditions guarantee success.

**Maximum likelihood:** choose whichever candidate makes the observed reads most probable.

Shomorony and colleagues asked:

> If the reconstruction conditions hold, **must the true genome also maximize ordinary likelihood**?

**Our answer is no.** We found a counterexample in which the competing assembly is one base longer.

<!--
This is the source's non-Bayesian implication from the true
genome's structural event to unconditioned P(R|D) ranking.
The exact 2016 MB09 objective is not named unambiguously, but
oriented candidate-intrinsic exact likelihood is source-supported.
The counterexample is kernel-checked in OrientedVariableLengthSe62.
Do not suggest all readings have a model-independent identical
mathematical statement; keep the explicit candidate-length scope.
-->

---

# A counterexample in six reads

**True circular genome:** AAATT (length **5**).

**Competing genome:** AAAATT (length **6**).

Sample six reads of length 3 from the true genome:

~~~text
AAA    AAA    AAT    ATT    TTA    TAA
~~~

| Read | Observed | Positions in AAATT | Positions in AAAATT |
| --- | ---: | ---: | ---: |
| AAA | **2** | 1 | **2** |
| AAT | 1 | 1 | 1 |
| ATT | 1 | 1 | 1 |
| TTA | 1 | 1 | 1 |
| TAA | 1 | 1 | 1 |

**The true genome satisfies the coverage and bridging conditions.** Both genomes are valid candidates in the read-overlap assembly model.

<!--
OrientedVariableLengthSe62.lean theorem and script
verify_oriented_variable_length_se62.py. Source truth S=AAATT,
L=3, true starts 0,0,1,2,3,4; full coverage and strict bridging,
all triple copies checked, interleaved pair vacuous.
Both S and D=AAAATT admit genuine oriented Section 6.2
read-overlap candidates. Variable candidate length is essential.
No reverse-complement grouping.
-->

---

# The longer genome scores higher

Each read begins uniformly at one of its candidate genome's positions.

Under the **true genome**, each observed read type occurs at 1 of 5 starts:

$$
P(R\mid S)=\left(\frac15\right)^6=\frac1{15625}.
$$

Under the **competing genome**, AAA occurs at 2 of 6 starts; the other four read types occur at 1 of 6:

$$
P(R\mid D)=\left(\frac26\right)^2
             \left(\frac16\right)^4
           =\frac1{11664}.
$$

$$
\boxed{\frac{P(R\mid D)}{P(R\mid S)}
     =\frac{15625}{11664}\approx1.34}
$$

**About 34% higher likelihood.** The reconstruction guarantee does not force the true genome to maximize ordinary likelihood.

<!--
Exact iid ordered-read model (observation multinomial coefficient
cancels). Lean OrientedVariableLengthSe62, family M=1.
All oriented types present; no reverse-complement collapse.
The competitor is longer; a same-length requirement would
exclude this particular witness and is a distinct assumption.
-->

---

# What were the two methods asked to do?

**Not-So-Greedy's guarantee** concerns a special set of experiments: the actual genome's repeats must be sufficiently bridged.

**Ordinary ML** compares candidate genomes from the observed read probabilities, **without being told that the reconstruction guarantee applies**.

Here the longer genome explains the unusually frequent AAA reads better, while the true genome satisfies the reconstruction conditions.

**The proposed implication is false.** That suggests a different question: what if the structural guarantee itself becomes part of our statistical information?

<!--
The source's pointwise guarantee differs from prior-averaged
Bayes optimality of ordinary ML. Do not claim one algorithm
has statistically defeated the other under the same decision
problem. No need to assert competitor failure of I_s
under every interpretation. Truth S length 5, competitor D length 6.
-->

---

# What if we also know the guarantee holds?

Suppose we are told **one additional fact**:

> The actual genome and the observed reads satisfy Not-So-Greedy's reconstruction conditions.

Not-So-Greedy is a **function of the reads alone**. When those conditions hold, its theorem says that function returns the true genome.

If two different genomes both qualified for the **same reads**, it would have to return two different answers on identical input. Impossible.

**Only one circular-genome class can remain.** Given both the reads and the promise, its Bayesian posterior probability is **100%**.

**The promise does most of the work.** That's the point: this conditioned experiment gives the estimator information ordinary ML did not have.

<!--
Given external source read-only unique decoder A satisfying
F(g,r)->A(r)≈g, feasible-fibre uniqueness follows directly.
Conditional joint K(g,r)=π(g)P_g(r)1_F(g,r) supports only
[A(r)] for positive mass, giving posterior 1.
Kernel consequences ConditionalIdentifiability.lean, with
external original source theorem premise. For latent starts
must marginalize feasible histories; don't substitute arbitrary
placement-based predicates (W3/W6).
-->

---


# A new hypothesis: was finite sampling the problem?

Our six-read sample contains **AAA twice**. But the true genome AAATT produces AAA at only **1 of 5** positions.

The competitor AAAATT has **two AAA positions out of six**. In fact, the observed frequencies of **all five read types** match that competitor's predictions exactly.

**My hypothesis:** perhaps the disagreement was caused by **finite-sample fluctuations**. What happens with enough reads that the observed frequencies settle toward the true distribution?

That motivated a new problem: **population likelihood**.

<!--
Human research director's deliberate pivot. True read law is
uniform 1/5 over AAA,AAT,ATT,TTA,TAA; six observations have
frequencies (2,1,1,1,1)/6 equal to D=AAAATT spectrum.
This explanation stays oriented, consistent with the population
theorem. It does not retroactively reverse the finite negative answer.
-->

---

# Population likelihood: remove sampling noise

Here **population** means the complete read distribution from **one fixed genome**, not a population of genomes.

For our example, the full read distribution is:

| Read type | True AAATT | Competitor AAAATT | Six observed reads |
| --- | ---: | ---: | ---: |
| AAA | 1/5 | **2/6** | **2/6** |
| AAT | 1/5 | 1/6 | 1/6 |
| ATT | 1/5 | 1/6 | 1/6 |
| TTA | 1/5 | 1/6 | 1/6 |
| TAA | 1/5 | 1/6 | 1/6 |

Our small sample perfectly matches the **wrong genome's distribution**. More independent reads make the frequencies approach the **true column** instead.

Population likelihood compares predictions with that limiting read distribution.

<!--
Expected log-likelihood, not infinite product of probabilities.
No reverse-complement collapse in either finite witness or table.
Gibbs inequality ensures truth's distribution is best;
uniqueness of genome requires stronger structural arguments.
-->

---

# When the exact read distribution is known

**First:** the true genome always maximizes population likelihood. No different distribution explains the true long-run read frequencies better.

**Uniqueness is harder:** could a different genome generate exactly the same frequencies and tie?

**We proved uniqueness** for **primitive, P2-admissible** genomes under our read model. Only rotations of the true circular genome can tie.

*Primitive* means the entire genome is not a shorter pattern repeated. **P2**, rooted in the repeat analysis of **Bresler, Bresler & Tse (2013)**, excludes certain long triple and interleaved-repeat patterns.

<!--
PopulationGibbs.popLogLik_le_self' plus popTie_iff:
any distribution has expected log likelihood <= truth,
equal iff same law. Issue94Complete.population_unique_ML:
kernel-checked for primitive P2 oriented genomes, L>=2,
candidate classes up to rotation; no external Bresler axiom.
P2 excludes triple repeats of length >= L-1 and a pair of
interleaved maximal repeats both >= L-1.
-->

---

# Do we actually need infinitely many reads?

**No.** The population theorem motivates a result about **finite data**.

Fix a finite collection of candidate genomes with **distinct read distributions**. As more independent reads arrive, the probability that a wrong candidate ties or beats the truth **falls exponentially**.

So for that identifiable finite family, sufficiently many reads can give **99% recovery probability**, or any other desired confidence.

The population model identifies the limiting answer; the finite theorem explains how more data approaches it.

<!--
FiniteReadRecovery, FiniteReadRecoveryGenome,
FiniteReadRecoveryP2Bridge, FiniteReadRecoveryP2Complete:
for a finite distinguishable family C, error <= |C| rho_*^n,
rho_* < 1. Primitive P2 supplies distinction modulo rotations.
No universal constant sample count for unrestricted candidates.
-->

---

# Another finite theorem: restrict the candidates

We also proved a separate positive result about finite samples.

Compare genomes of the **same length**, and require **both truth and competitor** to meet the specified read-overlap assembly constraints.

Then **no admissible competitor has higher likelihood than the truth**.

Under the stronger structural uniqueness hypotheses, every eligible competing genome is a **rotation of the same circle**.

This identifies the boundary that our **variable-length** counterexample does not satisfy.

<!--
SameLength62Maximizer and SameLength62Uniqueness:
truth and competitor both genuine same-length Section 6.2
candidate certificates, oriented convention, full stated
information-feasible hypotheses. Not a result for the
unrestricted variable-length model or unconditional Bayes
certainty; it is a distinct structural theorem.
-->

---

# Choosing the next research question

The project began with **the 2016 question**—not a predetermined answer.

Three turns shaped the investigation:

1. **Test the implication:** search for concrete counterexamples instead of assuming the two methods agree.
2. **Explain the disagreement:** separate likelihood scoring from the information in a reconstruction promise.
3. **Go further:** ask whether sampling noise explains the finite result, then investigate population uniqueness and finite-read recovery.

**I chose the questions and redirected the research as the results arrived.**

<!--
The speaker directed the scientific goals and questions.
Independent agents worked on candidate theorems, examples,
source interpretation and Lean formalization; their branches
and notes fed back into the user's strategic pivots.
-->

---

# Why we used multiple AI research agents

The research had **several independent mathematical directions**: interpreting the papers, searching for counterexamples, finding general proofs, and formalizing the results.

**AI agents** acted as research workers. Each could use literature, run code, explore a conjecture, and produce a branch containing computations, notes, or Lean proofs.

We could investigate **different hypotheses in parallel** without discarding the earlier ones. Unlike a temporary exchange of messages, the work persisted as files and commits that other agents could build on or challenge.

**I chose the questions and changed the direction. The agents explored the resulting mathematical tasks.**

<!--
Agents were part of the founding design, not a response to encountering a
later problem. Their role is concrete parallel inquiry with durable outputs
and independent tracks. Do not introduce chatbots as an out-of-nowhere foil.
Do not imply agents independently chose the principal hypothesis.
-->

---

# How continuous research was organized

**Antonina** is our persistent task board and agent orchestrator. It tracks questions, dependencies, progress, and findings.

~~~text
    I choose research directions
               ↓
   Antonina tracks ready tasks
        and their evidence
               ↓
   Agents work on parallel branches
               ↓
       Review → merge
               ↓
    New results inform my
     next research decisions
               ↺
~~~

The board and repository let the work **continue across sessions**, rather than starting from scratch.

<!--
Antonina is host-agnostic coordination infrastructure, not the
intellectual source of research hypotheses. It stores tasks and
dispatches ready work; separate worktrees/branches preserve outputs.
Signed Git commits and independent reviews help integration.
-->

---

# Why Lean mattered

A numerical example can disprove a universal claim. But establishing a **positive theorem for every eligible genome** requires a proof.

**Lean is a proof assistant:** it checks a precise statement and a formal proof using a small independent kernel.

~~~lean
example (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
~~~

Our genome-assembly arguments are more involved, but the **same checker** verifies the logic.

**Lean cannot decide whether the definitions match the original scientific question.** That still requires human judgment and careful source reading.

<!--
Use example, not theorem and_comm, which Lean core already declares.
This Lean 4 snippet is pasteable. Kernel and axiom audits:
propext, Classical.choice, Quot.sound only for the listed
formal results. No sorry/admit in the completed proof modules.
-->

---

# What the investigation established

**We answered the 2016 implication negatively.** The true genome can meet reconstruction conditions while a longer competing genome has greater ordinary likelihood.

We also clarified what this means statistically: a reconstruction promise is additional information. When it is explicitly given, the conditional posterior identifies the true circular genome class.

Beyond the counterexample, we proved **population ML uniqueness**, **finite-family reliability**, and a **restricted same-length positive theorem**.

The results came from **human-led hypotheses**, parallel AI research, and **Lean-checked mathematics**.


<!--
The negative witness has oriented reads, variable candidate length.
Truth is I_s-feasible and ML can rank D higher. Ordinary ML's
Bayes-optimality is prior-averaged; conditional posterior certainty
uses extra truth-dependent source-decoder event. P2 population and
same-length rigidity are distinct independent contributions.
-->

---
layout: end
---

# Questions?

**Genome assembly, likelihood, and human-directed AI research.**

<HomeLink label="Choose another audience" />

---

# Backup slides

Additional calculations, definitions, and sources.

---

# Backup B1: one extra read reverses the ranking

Start with AAATT. Observe **one read from every start**:

~~~text
AAA    AAT    ATT    TTA    TAA
~~~

The truth is then **more likely** than AAAATT:

$$
\frac{P(R\mid D)}{P(R\mid S)}=\frac{3125}{3888}<1.
$$

Now observe **just one additional AAA**. The ratio multiplies by:

$$
\frac{P_D(\mathrm{AAA})}{P_S(\mathrm{AAA})}
=\frac{2/6}{1/5}=\frac53.
$$

Therefore:

$$
\frac{P(R\mid D)}{P(R\mid S)}
=\frac{3125}{3888}\cdot\frac53
=\frac{15625}{11664}>1.
$$

**One extra read changes the likelihood ordering.**

<!--
NOT a stale 'finite aside': this is backup detail for the
main oriented AAATT / AAAATT example.
M=0 exact ratio 3125/3888; M=1 ratio 15625/11664.
OrientedVariableLengthSe62.lean and accompanying independent
exact-rational verifier establish the result. No model switch.
-->

---

# Backup B2: two different notions of coverage

A source audit found our earlier formal coverage predicate was **not the same** as the 2016 paper's definition.

**Earlier sampled-position model:** every genome base lies inside a read at its **actual sampled position**.

**Historical read-string model:** in **every interval of L−1 consecutive positions**, there is a **start position where some observed read string matches**—even if that string was sampled at a different occurrence.

**Neither condition implies the other.** We preserved both models and made their distinction explicit.

<!--
Shomorony et al. supplement §6.4 Definition 1:
for every t, exists tau ∈ [t,t+L-2] and observed read string r
such that r=s[tau:tau+L-1]. The L-1 interval does NOT
contain a length-L read: it contains a matching START position.
MatchStarts saturates repeats; HistoricalCovers.lean formalizes
the exact definition alongside sampled-placement Covers.
-->

---

# Backup B3: how many reads for 99% recovery?

We proved a **finite-family exponential error bound** in the specified oriented, independent-read model.

For a true read distribution and a finite family of distinguishable competitors:

$$
\Pr[\text{some wrong candidate ties or beats the truth}]
\;\le\; |\mathcal C|\,\rho_*^{\,n},
\qquad 0\le\rho_*<1 .
$$

The affinity constant $\rho_*$ expresses how similar the competitors' read distributions are to the truth. The bound shrinks exponentially as the number of reads $n$ grows.

**What remains open:** one sharp, uniform sample-size guarantee over the unrestricted universe of genome candidates, especially across different lengths and models.

<!--
Unlike the original backup, this is now a kernel-checked result:
FiniteReadRecovery, FiniteReadRecoveryGenome, FiniteReadRecoveryP2Bridge,
FiniteReadRecoveryP2Complete. Do not claim sample complexity is wholly
open; finite-family confidence theorem is established. Finite family,
positive separation, iid oriented reads, and candidate model matter.
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
