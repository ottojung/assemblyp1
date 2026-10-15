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

# Our mathematical model

We are **not** simulating every complication of real sequencing. We study a deliberately simple question that can be proved mathematically.

- The genome is a **circular string**.
- All reads have the same length, a known direction, and **no errors**.
- Each read starts at a **uniformly random position**, independently of the other reads.

Some reconstruction theorems need **additional conditions** about which positions were observed and how repeats were bridged.

<!--
The idealized model needs to be clear before explaining graphs or claiming that
sampling frequency is a probability. Its conclusions are conditional and do not
by themselves specify a real sequencing workflow.
-->

---

# How the read-overlap idea works

Each read may follow another when its **ending matches the next read's beginning**.

```text
ACG -> CGT -> GTA -> TAA -> AAC -> ACG
```

Each arrow means a two-letter suffix matches a two-letter prefix.

The arrows form a **read-overlap graph**: each read is a vertex; an arrow means the two reads *could* be consecutive.

This simple cycle spells the circular genome `ACGTA`.

<!--
This is a read-overlap diagram, NOT a de Bruijn graph.
It is intentionally simple; the next slide explains why repeats complicate it.
-->

---

# Why repeats create ambiguity

Take the following length-3 reads, including repeated occurrences:

```text
ATG  TGA  GAT  ATC  TCA  CAT  ATA  TAT  ATA  TAT
```

When a read ends in `AT`, more than one continuation is possible. **The graph branches.**

In fact, these **two different circular genomes** yield exactly that same collection:

```text
ATGATCATAT
ATGATATCAT
```

Neither is a rotation of the other. **The short reads alone cannot distinguish them.** Longer reads that span the ambiguous repeats can.

<!--
Verified circular length-3 read counts for each:
ATA twice, TAT twice, ATG/TGA/GAT/ATC/TCA/CAT once each.
The two genomes are not rotations. This toy illustrates ambiguity, NOT a
counterexample under the bridging assumptions of the 2016 theorem.
-->

---

# Not-So-Greedy: reconstruction with a guarantee

Shomorony, Kim, Courtade, and Tse (2016) built an algorithm on a **sparse read-overlap graph**. It does not blindly follow the longest overlap:

- It retains a likely next read **and a meaningfully different alternative**.
- It removes redundant or misleading connections and tracks repeated traversals.

**Under the theorem's coverage and repeat-bridging conditions, Not-So-Greedy reconstructs the true circular genome uniquely, up to rotation.**

That is a **guarantee about this particular algorithm**, not just a promising heuristic.

*Side note:* de Bruijn graphs are another representation used widely in practical assembly. We do not need them for this argument.

<!--
Shomorony et al. (2016), DOI 10.1093/bioinformatics/btw450. The sparse
construction adjusts edge multiplicities and gives a unique Eulerian spelling.
Its Theorem 1 requires coverage and all-bridged triple repeats; the
information-feasible set I_s adds bridging of interleaved repeats. The full
I_s conditions on the later question slide are a sufficient case, not a claim
that all three are individually necessary for Theorem 1.
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

# Why can no reconstruction algorithm do better?

In this example, after two `AAA` reads, we calculate:

**A has 20% probability of being true; B has 80%.**

Any algorithm with **the same observations and candidate model** must ultimately output a genome:

- It chooses **B**: 80% probability of a correct answer *given these reads*.
- It chooses **A**: 20%.
- It randomizes: an average of those numbers, **never more than 80%**.

The argument works for **every possible collection of reads**. So choosing the highest *posterior* probability is better than or tied with **any other algorithm** in prior-averaged correctness.

With **equally likely candidate genomes beforehand**, that rule is **maximum likelihood (ML)**.

<!--
This is Bayesian decision optimality under zero-one loss over a *specified*
finite candidate set and prior. It does not claim superiority for each fixed
true genome, and it does not apply unchanged under unequal priors (then use
MAP). Kernel-checked in AssemblyP1/FiniteBayesDecision.lean, including
deterministic and randomized decisions.
-->

---

# The 2016 question: are the guarantees the same?

Recall the **three conditions** defining the paper's information-feasible read sets:

1. **Coverage:** every position in the circular genome is covered by a read.
2. **Triple repeats:** **every copy** of every triple repeat is **bridged**: a read extends beyond both ends of that copy.
3. **Interleaved repeats:** when two repeats have alternating occurrences (A–B–A–B), at least one of the repeats is **bridged**.

**These conditions guarantee that Not-So-Greedy reconstructs the one true circular genome (up to rotation).**

But do they **also** guarantee that the true genome maximizes likelihood among the permitted candidates?

**AssemblyP1 settled the precisely specified versions of this question.** The answer depends on which statistical model and candidate class we mean.

<!--
Source: docs/bridging-source-semantics.md and docs/open-problem.md.
All triple-repeat copies must be bridged (not just one); an interleaved
repeat pair needs at least one copy of either repeat bridged.
These are the source's I_s conditions, sufficient for Not-So-Greedy, and
not the complete minimal hypotheses of the algorithm's Theorem 1.
The original open-question wording did not identify a unique MB09 objective,
so distinguish exact multinomial, §6.1 binomial, and §6.2 flow candidates.
-->

---

# A positive result: the truth cannot be outscored

We also proved that **the original intuition is correct in one carefully defined setting**.

Suppose we distinguish the direction of a read and consider candidate genomes **of the true genome's length**, each genuinely compatible with the specified assembly constraints.

Under the required coverage and bridging assumptions, **no such competitor can have higher likelihood than the true genome**.

The stronger structural result says something more: under its full conditions, a compatible competitor must actually be the **same circular genome**, perhaps with a different starting position.

**This is a theorem, not an experimental observation.** The restriction to this specific read model and candidate class matters.

<!--
Oriented single-strand reads, same-length genuine 6.2 flow candidates with
truth-and-competitor feasibility, I_s on the realized read-start set.
SameLength62Maximizer.informationFeasible_62_maximizer;
SameLength62Uniqueness.unique_62_maximizer_up_to_rotation, with its precise
additional assumptions. Historical conditional BBT route is separate.
Do not transfer to RC-collapsed molecule classes or an unrestricted
candidate universe. Avoid internal circulation/spectrum jargon on slides.
-->

---

# Main discovery: maximum likelihood can choose the wrong genome

The true circular genome is **AAATAT**. A competing genome is **AAAAAT**.
Both have length **6**; each read has length **3**.

We sampled starts `0, 0, 1, 3, 5` from the **true** genome:

```text
Observed reads: AAA, AAA, AAT, TAT, TAA
```

For this historical likelihood model, a read and its **reverse complement** count as the same *molecule type*: in particular, `TAT` and `ATA` count together.

| Molecule type | Observed | True genome: occurrences | Wrong genome: occurrences |
| --- | ---: | ---: | ---: |
| `AAA` | **2** | 1 | **3** |
| `AAT` | 1 | 1 | 1 |
| `ATA` or `TAT` | 1 | **3** | 1 |
| `TAA` | 1 | 1 | 1 |

**The sample happened to contain `AAA` twice. The wrong genome predicts that type more often.**

<!--
This is source-faithful MB09 '6.2's reverse-complement molecule-type
interpretation, not the oriented-read model of the preceding positive theorem.
Complement map A <-> T. True circular molecule windows in classes:
AAA, AAT, ATA, ATA (from TAT), ATA, TAA. Wrong: AAA, AAA, AAA,
AAT, ATA, TAA. Realized starts (0,0,1,3,5) produce sequences
AAA,AAA,AAT,TAT,TAA. Source:
docs/section62-same-length-bidirected-counterexample.md
-->

---

# The exact calculation: ML prefers the wrong genome

With a uniformly random start, each type has probability
**(its occurrence count) / 6**. For five conditionally independent reads:

**True genome** `S = AAATAT`:

$$
P(R\mid S)=
\left(\tfrac16\right)^2
\left(\tfrac16\right)
\left(\tfrac36\right)
\left(\tfrac16\right)
=\frac{3}{6^5}=\frac1{2592}
$$

**Wrong genome** `D = AAAAAT`:

$$
P(R\mid D)=
\left(\tfrac36\right)^2
\left(\tfrac16\right)
\left(\tfrac16\right)
\left(\tfrac16\right)
=\frac{9}{6^5}=\frac1{864}
$$

$$
\boxed{\frac{P(R\mid D)}{P(R\mid S)}=3>1}
$$

**ML prefers the wrong genome by a factor of three.** Therefore the truth **cannot be an ML maximizer** in this candidate class.

<!--
These are probabilities of an ordered sample of read-molecule types under
independent, uniform starts. For unordered observed counts both candidate
likelihoods share the multinomial coefficient 5!/2! = 60, so the ratio is
still exactly 3. The literal MB09 '6.1 fixed-N product-binomial objective
is DIFFERENT; its ratio for this witness is 5, not 3. Do not conflate.
Both objective ratios and full '6.2 candidate feasibility are Lean-checked.
-->

---

# Why this settles a substantive case of the 2016 question

This is **not** a made-up case where assembly was impossible.

- The observed reads satisfy the 2016 **coverage and repeat-bridging conditions**, so **Not-So-Greedy's reconstruction guarantee applies** to the true genome.
- The true and competing genomes are both **legal assemblies under the 2009 read-molecule model**.
- They have the **same length**. There is no hidden benefit from adding genome positions.
- Yet the competitor has **strictly higher likelihood**.

**Therefore the reconstruction guarantee does not, in this model, force the true genome to be maximum likelihood.** We have a checked counterexample—not merely a numerical suspicion.

This does **not** contradict ML's optimality *averaged over the prior*. An optimal decision rule can still be wrong on a particular sample.

<!--
Source: docs/section62-same-length-bidirected-counterexample.md.
Kernel theorem:
AssemblyP1.SameLengthSection62Counterexample.
samelength_se62_bidirected_flow_counterexample.
It checks Shomorony information feasibility (coverage, triple all-bridged,
interleaved bridging), same length, both literal bidirected '6.2 spelled
circuits, and strict exact likelihood inequality (ratio 3).
The earlier oriented-positive result and this molecule-negative result
are compatible because their statistical/sample conventions differ.
-->

---

# Why investigate a model with more reads?

We found a real counterexample: **Not-So-Greedy is guaranteed to reconstruct the truth, yet maximum likelihood picks another genome.**

But **why** did ML lose? I hypothesized that the intuition might still be right: perhaps a **finite, unusually unrepresentative sample** was the problem—not a fundamental conflict between reconstruction and likelihood.

In the counterexample, the true genome **AAATAT** has **AAA** at **1 of 6** starting positions, but our five reads happened to include it **2 of 5 times**.

The wrong genome **AAAAAT** has **AAA** at **3 of 6** positions. This unusually AAA-heavy sample therefore favored the wrong genome.

**So I changed the research question:** what if we remove that sampling accident, by allowing as many independent reads as needed?

<!--
This research motivation is the human director's actual hypothesis, not a
mathematical consequence of the counterexample.
The 1/6 and 3/6 occurrence rates refer to reverse-complement-collapsed
molecule types in the finite witness. For a read-type-specific frequency
table these are exact. The five-read observation of AAA twice is 2/5.
This motivates moving to a DIFFERENT question; it does not undo the finite
counterexample or make ML uniformly correct at any fixed sample size.
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

We compared **a reconstruction algorithm with a success guarantee** and **maximum likelihood, statistically optimal in the specified prior-averaged sense**.

**We settled the determinate source-supported finite interpretations** of the 2016 question: there are genuine counterexamples to finite ML recovery, alongside strong positive results for carefully defined candidate classes.

When the finite failures suggested a **sampling effect rather than a fundamental obstruction**, I directed the investigation toward a population model. There, we proved **ML uniqueness up to rotation**, under explicit structural assumptions.

The research combined **human direction, parallel AI exploration, continuous orchestration, and Lean-checked proofs**.

<HomeLink label="Choose another audience" />

<!--
The old 2016 sentence does not uniquely select an MB09 objective, but its
determinate source-supported interpretations have been resolved. Do not
understate this as not having answered our original question. The
population theorem is separate (oriented primitive P2 class); do not
suggest it makes finite counterexamples disappear.
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
