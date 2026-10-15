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
Introduce complications only after successful assembly. All read types
appear in the full ambiguity example two slides later. The arrows are
possible overlaps, not all realized at one physical genome position.
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
The first examples use oriented reads. The historical MB09 finite
counterexample later explicitly changes to reverse-complement molecule
types. Model fidelity and theorem scope matter.
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

Shomorony and colleagues (2016) developed an algorithm based on a **sparse read-overlap graph**.

They proved it reconstructs the **unique true circular genome, up to rotation**, under these conditions on the reads:

1. **Coverage:** the reads cover the genome.
2. **Triple repeats:** every copy of a triple repeat is bridged.
3. **Interleaved repeats:** at least one repeat in each interleaved pair is bridged.

**This is a mathematical guarantee of correctness**, not just a heuristic that often works.

*Aside: practical assemblers also use de Bruijn graphs. We don't need them for this story.*

<!--
Source: Shomorony et al. 2016, doi:10.1093/bioinformatics/btw450.
Information-feasible I_s conditions have precise maximal-repeat and
strict-straddle definitions. Unique reconstruction follows from the
published Corollary 1. The source algorithm remains an external premise.
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

```ts
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
console.log(weights.map(w => w / total)); // [0.2, 0.8]
```

The code computes **likelihoods** from the sampling process; then the last line computes **genome probabilities given the data**, using an *equal prior over these two candidates*.

<!--
Runnable TypeScript for the simplified circular, equal-length, iid model.
For an unequal prior, multiply each likelihood by its prior weight before
normalizing. If the total is zero, all candidates rule out the data.
-->

---

# Why maximum likelihood beats every algorithm

Any reconstruction algorithm receives the reads, **not the hidden genome or the positions they came from**.

Our example has **50 equally likely complete experiments**: choose A or B (50/50), then choose two start positions (5 × 5).

| Observed reads: `AAA, AAA` | A was true | B was true |
| --- | ---: | ---: |
| Compatible experiments | **1** | **4** |

**The algorithm cannot distinguish those five experiments.** Guess A: one correct. Guess B: four correct. ML picks B because **these reads are four times as likely under B**.

**Why does this beat *every* algorithm?** Divide *all* experiments into groups with identical observed reads. In each group, ML guesses the genome responsible for the most experiments. No other choice wins more often **in that group**. Adding up the groups, **no algorithm can have higher overall correctness**.

*Scope: best average correctness under an equal prior and the stated sampling model—not a guarantee for each sample or true genome.*

<!--
This is the direct proof of Bayes decision optimality, instead of treating
optimality as a restatement of the posterior. For decision rule a(r):
P(a(R)=G)=sum_r pi(a(r)) P(R=r | G=a(r)).
With equal priors, each disjoint summand is maximized by choosing argmax_G
P(R=r|G), i.e. ML. Randomized rules cannot improve the maximum because
their conditional success is a convex combination of deterministic choices.
The 50 equiprobable histories arise from 2 equiprobable five-base genomes
with two independent uniform starting positions: 2 * 5 * 5 = 50.
For r=[AAA,AAA], 1 A history and 4 B histories. An algorithm choosing A
rather than B solely here loses 3/50 in prior-averaged success probability.
This proves comparison against every algorithm using the same observed reads
and candidate model. Formalized in AssemblyP1/FiniteBayesDecision.lean.
-->

---

# The question raised in 2016

We have two approaches:

**Not-So-Greedy:** reconstruct by overlaps. With coverage and bridged repeats, it is **guaranteed to return the truth**.

**Maximum likelihood:** pick the genome that makes the observed reads **most probable**.

The 2016 paper asked:

> If Not-So-Greedy's conditions hold, **must the true genome also maximize ordinary likelihood?**

This is a logical **if–then statement**, not a Bayesian posterior calculation conditioned on the event.

**We proved that the answer is no.**

<!--
The original non-Bayesian question is F(S,R) => S in argmax_D P(R|D),
where the likelihood score is NOT conditioned on F. The strict
source-supported finite counterexamples refute the implication.
-->

---

# A counterexample to the 2016 implication

The **true** circular genome is **AAATAT**. A competing genome is **AAAAAT**. Both have length **6**; reads have length **3**.

Five reads were sampled from the truth at starts 0, 0, 1, 3, 5:

~~~text
AAA   AAA   AAT   TAT   TAA
~~~

The historical likelihood model groups a read with its reverse complement. Thus TAT and ATA count together.

| Read type | Observed | True AAATAT: positions | Competitor AAAAAT: positions |
| --- | ---: | ---: | ---: |
| AAA | **2** | 1 | **3** |
| AAT | 1 | 1 | 1 |
| ATA / TAT | 1 | **3** | 1 |
| TAA | 1 | 1 | 1 |

**The truth satisfies the reconstruction conditions.** The competitor is a valid likelihood candidate, but it **does not satisfy the same bridging conditions** in this witness.

<!--
The source-faithful same-length MB09 §6.2 read-molecule witness:
SameLengthSection62Counterexample. Both genomes have genuine spelled
bidirected-flow candidate certificates. Truth satisfies full I_s at
realized starts; D fails I_s in the witness owing to an unbridged
triple repeat (audit #267, W5). Do not conclude D has zero marginalized
conditional probability from its failure at ONE set of placements.
-->

---

# Exact calculation: the implication is false

At a uniformly random start, the probability of a read type equals its number of positions divided by 6.

For the five independent reads, the **true genome** has likelihood:

$$
P(R\mid S)
= \left(\tfrac16\right)^2
  \left(\tfrac16\right)
  \left(\tfrac36\right)
  \left(\tfrac16\right)
= \frac{3}{6^5} = \frac1{2592}.
$$

The **competing genome** has likelihood:

$$
P(R\mid D)
= \left(\tfrac36\right)^2
  \left(\tfrac16\right)
  \left(\tfrac16\right)
  \left(\tfrac16\right)
= \frac{9}{6^5} = \frac1{864}.
$$

$$
\boxed{\frac{P(R\mid D)}{P(R\mid S)}=3}
$$

**The competitor scores three times higher.** This **disproves the 2016 bridging-to-ordinary-ML implication**.

<!--
Exact iid ordered molecule-type ratio is 3. The multinomial-count factor
cancels for unordered sample counts. MB09 §6.1 product-binomial ratio
on this same witness is 5, not 3. Source-faithful flow and inequalities
are Lean checked; no claim is made about an unconditional Bayes posterior.
-->

---

# What did the counterexample really show?

**Not-So-Greedy's guarantee** applies to a special set of experiments: the **actual genome and its reads** satisfy coverage and repeat bridging.

**Ordinary maximum likelihood** compares a **broader set of candidate explanations**, without using that structural guarantee as additional statistical information.

Our competitor is a legitimate likelihood candidate, even though it **doesn't satisfy the bridging conditions** in this particular case.

So the 2016 implication is **false**. But this does **not** mean ML is a worse decision rule than Not-So-Greedy on the *same* statistical problem.

**What if we were given the reconstruction guarantee as part of the information?**

<!--
W5 AAATAT/AAAAAT: competitor fails the information-feasibility
condition for the witnessed placements, but has higher ordinary
read-molecule likelihood. The failure for one placement is not proof
of zero likelihood jointly conditioned on E after marginalizing
unobserved starts. Pointwise failure and Bayes-average optimality
are different claims.
-->

---

# What if we know the guarantee applies?

Imagine we are **also told**:

> The **true genome and these reads** satisfy Not-So-Greedy's reconstruction conditions.

Now we reason using **both the reads and that promise**.

Suppose two different genomes could each be the truth under this promise for the same reads. Then Not-So-Greedy would have to return **two different genomes for exactly the same input**. But its theorem guarantees a unique result.

**Therefore only one circular genome remains possible, up to rotation.**

In Bayesian terms, its probability **given the reads and the promise** is **100%**. Choosing it is the best possible decision for this *conditioned* experiment.

The promise concerns the **unknown truth**: it is new information, not something ordinary ML already had.

<!--
Assuming the published read-only unique decoder A with
F(g,r)->A(r)≈g, feasible candidate classes for a fixed observed
read set collapse to [A(r)]. The conditional joint distribution
pi(g)P_g(r)1_F(g,r) is supported there; posterior certainty is
kernel-checked in ConditionalIdentifiability.lean under the external
NSG decoder premise. For latent start placements use the correctly
marginalized E-weighted joint law; do NOT transfer this result to
different placement-based predicates or confuse it with 2016 if-then.
-->

---


# Why investigate a model with more reads?

The finite counterexample settled the 2016 question **negatively**. But it inspired a different research direction.

The true genome AAATAT generates AAA at only **1 of 6** positions, yet our five-read sample contained AAA **twice**. The competitor AAAAAT generates AAA at **3 of 6** positions, so that unusual sample favored it.

**My hypothesis:** perhaps the intuition that assembly and likelihood should agree was fundamentally sound, and the apparent disagreement came from **finite sampling fluctuations**.

**So I changed the question:** what if we could take as many independent reads as needed, removing that sampling accident?

<!--
A new hypothesis-driven research pivot by the human director; the negative
finite answer is already resolved. The molecule frequencies motivate
an independent oriented primitive-P2 population theorem; do not
pretend the population theorem retroactively makes the finite claim true.
-->

---

# Population likelihood: remove the sampling noise

**Population** here does *not* mean a population of genomes.

It means the **complete probability distribution of reads generated by one fixed genome**—as though we knew the exact frequency of every possible read.

For independent reads, observed frequencies approach these probabilities as the number of reads grows:

```text
                    True genome    Wrong genome    Observed 5 reads
AAA type                1/6             3/6             2/5
ATA / TAT type          3/6             1/6             1/5
```

Our finite sample overrepresented `AAA` and underrepresented `ATA/TAT`. In the population limit, that fluctuation disappears.

**This is not an infinite multiplication of probabilities.** It asks which genome best explains the *exact read distribution*, without finite-sample luck.

<!--
The example uses the same molecule-type convention as the finite witness.
Convergence of empirical read frequencies to the source distribution follows
from the strong law of large numbers under conditional iid sampling.
"Population likelihood" is expected log-likelihood, not an infinite read-product.
Population-Gibbs maximality holds for the true distribution, and any distinct
distribution has strictly lower expected log-likelihood (allowing -infinity).
-->

---

# What we proved when the read frequencies are exact

**First, the true genome always maximizes population likelihood.** No alternative read distribution can fit the true long-run frequencies better.

But could an entirely different genome generate **exactly those same read frequencies** and tie?

**We proved uniqueness:** for oriented reads and **primitive, P2-admissible genomes**, the true genome is the **only population ML solution, up to rotation**.

Here *primitive* means the genome is not a shorter pattern repeated; **P2** excludes the long triple and interleaved-repeat patterns that make assembly ambiguous.

**This proves the intuition in a precise mathematical model.** It is a separate result from our finite molecule-type counterexample—not a claim that the latter was mistaken.

<!--
PopulationGibbs.popLogLik_le_self' and popTie_iff: truth maximal over
any candidate family containing it, equality iff read laws identical.
Issue94Complete.population_unique_ML: full kernel-checked uniqueness for
primitive P2 truths against any positive-length primitive P2 admissible
oriented candidate, L >= 2, no external BBT premise. P2: no triple repeat
of length >= L-1; interleaved maximal repeat pair cannot have both repeats
of length >= L-1. Prim: circular word not a nontrivial power.
Finite counterexample uses RC molecule types and different assumptions.
-->

---

# Do we actually need infinitely many reads?

**No.** Population likelihood describes the ideal target, but we also proved a practical mathematical consequence for **finite samples**.

Within **any fixed finite family of distinct admissible genomes**, the chance that a wrong genome ties or beats the truth **decreases exponentially as we take more independent reads**.

So, for any desired reliability—say **99%**—**sufficiently many reads exist** to reach it under those assumptions.

This does **not** promise a perfect answer from every finite experiment, nor does it give one universal read count that works for all possible genomes.

**The population model explained why more data restores the intuition, and the finite theorem connects it back to real-sized samples.**

<!--
Kernel checked finite read recovery: AssemblyP1.FiniteReadRecovery,
FiniteReadRecoveryGenome, FiniteReadRecoveryP2Bridge,
FiniteReadRecoveryP2Complete. For finite identifiable competitor set C
distinct from truth, failure probability <= |C| rho_*^n, rho_*<1.
For primitive P2 genome candidates modulo rotations, distinguishability
follows from Issue94Complete.population_unique_ML.
A uniform claim over unbounded candidate lengths is NOT proved.
Hypotheses: oriented iid uniform-start sampling, finite family.
-->
---

# Another positive result, in a restricted setting

We also proved an independent theorem about **finite-sample likelihood**.

Use reads with a known orientation, compare genomes of the **same length**, and require **both the truth and its competitors** to meet the specified read-overlap assembly constraints.

Then **no admissible competing genome can have higher likelihood than the truth**.

With stronger uniqueness assumptions, the only possible competitors are **rotations of the same circular genome**.

This is a significant theorem for that **restricted candidate problem**. It does not make the broader 2016 implication true.

<!--
SameLength62Maximizer and SameLength62Uniqueness under true-and-competing
genuine MB09 Section 6.2 certificates, oriented same-length model.
Separate from conditional Bayesian posterior and from population P2.
-->

---

# How I directed the investigation

The project began with a question from a 2016 paper. My job was to **find useful research directions**, not just to inspect work after it was done.

The direction kept changing as we learned:

- Could the two methods be proved to agree?
- If not, could we find **actual counterexamples** satisfying the reconstruction guarantee?
- Why did some settings admit counterexamples, while others gave **positive theorems**?
- Was the finite failure merely **sampling noise**? Could a population model recover the original intuition?
- Could all these statements be **proved rigorously**, rather than supported only by numerical tests?

**The central work was deciding which question to ask next.** New discoveries changed the plan.

<!--
The research director is the speaker. The principal intellectual work was
choosing directions and hypotheses as evidence arrived, rather than merely
checking conditions or enforcing correctness. This includes the population
pivot motivated by the finite false result. See
slides/programmers-research-notes.md and the dated intent records.
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

The setup let investigations continue across sessions—not start over whenever I returned.

~~~text
     I set priorities and propose directions
                    ↓
      Antonina board preserves tasks,
         dependencies and findings
                    ↓
     Orchestrator dispatches work
                    ↓
    Agents explore separate branches
                    ↓
        Review → tests → merge
                    ↓
       New results inform my
         next research decisions
                    ↺
~~~

**Orchestration kept independent work moving.** The board, repository, and continuous integration made the results durable and reviewable.

<!--
The Antonina board is persistent coordination state. Orchestrators dispatch
parallelizable ready tasks and continue dispatching, based on topology.
Lubko provides isolated workers; agents work on separate branches/worktrees.
GitHub PRs, review and CI are integration gates. The human director sets
research priorities and pivots. This is a loop, not just a one-off agent run.
-->
---

# Why Lean mattered

Finding a convincing example is one thing. **Proving a claim for every genome** that satisfies the hypotheses is much harder.

**Lean is a proof assistant.** We define the mathematical objects, state the theorem, and supply a proof checked by a small independent **kernel**.

~~~lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
~~~

This simple proof rearranges two assumptions. Our assembly proofs are vastly more involved, but the **same checker** verifies their logic.

**Why trust it?** The kernel checks formal proof terms instead of taking an AI agent's word. CI rebuilds and checks the proofs and audits which axioms they use.

**What it cannot do:** decide whether our definitions faithfully represent the original scientific question. That remains a research decision.

<!--
Curry-Howard correspondence, kernel checks proof terms against theorem
statements; CI uses leanchecker and axiom audit.
Allowed axioms: propext, Classical.choice, Quot.sound. No sorry/admit.
Keep mathematical correctness of a formal statement distinct from
fidelity to intended biology/published hypotheses.
-->

---

# What the investigation established

**The 2016 question has a negative answer.** Guaranteed Not-So-Greedy reconstruction does not force the truth to maximize ordinary likelihood.

The counterexample did **not** make ML inferior. The two methods were being judged on different problems. **Given the reconstruction guarantee as extra evidence**, conditional Bayesian inference identifies the true circular genome with certainty.

We also established **population ML uniqueness**, **finite-read reliability bounds**, and a **separate positive theorem** for a restricted finite setting.

The work combined **human-directed research choices**, parallel AI agents, continuous orchestration, and Lean-checked proofs.

<HomeLink label="Choose another audience" />

<!--
Avoid slogans about recovering optimality or ML losing. Historical
non-Bayesian if-then implication is false; conditional Bayes is a
distinct truth-dependent inference experiment. Preserve theorem scopes.
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
