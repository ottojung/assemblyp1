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

# The question left open in 2016

The 2016 paper gave Not-So-Greedy a remarkable guarantee. If the sampled reads:

1. **Cover** the circular genome;
2. **Bridge every copy of a triple repeat** (a read extends beyond both ends);
3. **Bridge at least one repeat in every interleaved pair**;

then **Not-So-Greedy reconstructs the unique true genome**, up to rotation.

The authors then asked a different question:

> Under those same conditions, **must the true genome also have the highest ordinary likelihood**?

That is an *if–then* claim about a reconstruction guarantee and a likelihood score. **It does not condition the probabilities themselves on the guarantee.**

<!--
This is the original non-Bayesian implication:
F(S,R) -> S ∈ argmax_D P(R|D), with the ORIGINAL unconstrained
likelihood, not the Bayesian conditional P(S|R,F).
The full historical information-feasible I_s is a sufficient
source condition for NSG's unique reconstruction corollary;
do not claim each condition is separately necessary.
The original source's likelihood referent has technical ambiguity
but the substantive claimed implication is refuted by strict
source-supported witnesses.
-->

---

# A read sample that makes the methods disagree

**True genome:** AAATAT. **Competing genome:** AAAAAT.

Both are circular, length 6. Read length is 3. We sampled five reads from the **true** genome:

~~~text
AAA   AAA   AAT   TAT   TAA
~~~

The historical likelihood formulation groups a read with its reverse complement: ATA and TAT are one molecule type.

| Read type | Observed | True: positions | Competitor: positions |
| --- | ---: | ---: | ---: |
| AAA | **2** | 1 | **3** |
| AAT | 1 | 1 | 1 |
| ATA / TAT | 1 | **3** | 1 |
| TAA | 1 | 1 | 1 |

**The true genome satisfies all the reconstruction conditions.** The competing genome is still eligible for ordinary likelihood scoring—even though **it fails the bridging conditions** for this witness.

<!--
SameLengthSection62Counterexample (MB09 §6.2): both true and
competitor are genuine bidirected read-molecule flow/spelling
candidates of length six. The true genome satisfies complete
source-faithful placement I_s at starts 0,0,1,3,5; D fails
I_s for the exhibited starts (audit #267, W5). Candidate eligibility
for ordinary flow ML is not the same as I_s for the truth.
Do not transfer this placement witness directly to source read-string
conditional Bayesian event or infer zero marginalized event likelihood.
-->

---

# No: ordinary likelihood can favor another genome

Each molecule type's probability is its occurrence count divided by 6. For these five independent reads:

**True genome AAATAT:**

$$
P(R\mid S)
=\left(\tfrac16\right)^2
 \left(\tfrac16\right)
 \left(\tfrac36\right)
 \left(\tfrac16\right)
=\frac{3}{6^5}=\frac1{2592}
$$

**Competing genome AAAAAT:**

$$
P(R\mid D)
=\left(\tfrac36\right)^2
 \left(\tfrac16\right)
 \left(\tfrac16\right)
 \left(\tfrac16\right)
=\frac{9}{6^5}=\frac1{864}
$$

$$
\boxed{P(R\mid D)=3\,P(R\mid S)}
$$

**Not-So-Greedy is guaranteed to return S, but D has three times its ordinary likelihood.** This is a rigorous **negative answer to the 2016 question**.

<!--
Exact iid probability of ordered molecule-type sample. Under
unordered read counts both have the same multinomial coefficient,
so the exact likelihood RATIO is 3. The alternative MB09 binomial
surrogate ratio is 5. Source-feasibility and ratios are Lean checked
in SameLengthSection62Counterexample. This is not a statement
about any posterior being incorrect.
-->

---

# Why that does not make ML inferior

The two statements make **different promises**.

**Not-So-Greedy:** *If* the actual genome and reads satisfy coverage and bridging, the algorithm reconstructs that genome. This is a **guarantee on a particular subset of experiments**.

**Ordinary ML:** Among the allowed candidates, choose the genome that best explains the **observed reads alone**. Its average-correctness optimality (with equal priors) is about **the entire sampling experiment**.

In our counterexample, the other genome is permitted in the latter comparison, but it does **not** meet the guarantee's conditions in the witnessed case.

**The 2016 implication is false. But we have not shown that Not-So-Greedy beats ML on the statistical problem ML was given.**

That leaves a useful question: **what if we include the guarantee in the statistical experiment?**

<!--
The NSG algorithm does NOT need event E as explicit input: it is
a read-only method with a conditional correctness theorem. The
conditional theorem's event is truth-dependent. ML optimizes
unconditioned P(R|D); the negative witness does not contradict
the uniform-prior, average-success theorem in FiniteBayesDecision.
Avoid 'ML lost' rhetoric or vague 'bestness' language.
-->

---

# What if we knew the guarantee held?

Suppose that, along with the reads R, we are **also told** a fact E:

> The actual, unknown genome **satisfies Not-So-Greedy's reconstruction conditions** on these reads.

Why is that powerful? Imagine **two different genomes** could both be the truth while satisfying E and producing **the same reads**.

Not-So-Greedy sees only those reads. Its theorem would force it to return **both** genomes from the **same input**—impossible unless they are the same circular genome up to rotation.

**So only one genome class remains possible.** Bayesian inference using **the reads and E** assigns that class **100% posterior probability**. Its choice is then certain.

This is **not ordinary ML**. E depends on the unknown truth and supplies additional information; it changes the statistical question.

<!--
Proof from external source read-only deterministic unique decoder A:
for every g,r, F(g,r) -> A(r) ~ g. If F(g,r) and F(h,r)
then g~h, so supported conditional joint K(g,r) =
pi(g)P_g(r) 1_F(g,r) concentrates on orbit [A(r)].
P([G]=[A(r)] | R=r, E)=1 when the denominator is positive;
conditional MAP is optimal and certain in this different experiment.
Formal consequences: AssemblyP1/ConditionalIdentifiability.lean
(feasible_fibre_unique, conditional_posterior_eq_one,
constrained_MAP_mem_orbit), with the NSG decoder as EXTERNAL
source theorem premise. In the latent-placement variant, sum
P_g(T) over compatible feasible placements; do not naively
multiply P_g(R) by existential feasibility. E is truth-dependent
and not generally observable from read strings alone.
Do NOT transfer the RC molecule witness directly to this
historical observed-read-string theorem or assume all
placement predicates obey the same uniqueness.
-->

---

# A new question: was finite sampling the problem?

Knowing the structural promise explains why **conditional** inference can be certain. But I still wanted to understand **ordinary likelihood**, without supplying that extra fact.

Look again at our counterexample. The true genome generates AAA at **1 of 6** positions, yet we observed it **2 out of 5** times. The competitor generates AAA at **3 of 6** positions, so it benefited from this unrepresentative sample.

**My hypothesis:** perhaps the mismatch was largely a **finite-sampling effect**, not a fundamental reason that the likelihood approach and reconstruction intuition could never agree.

So we asked a new question: **with as many independent reads as we need, does likelihood eventually identify the truth?**

That led us to the **population model**.

<!--
The human research director's actual pivot: the 2016 finite implication
is already answered NO. Conditional Bayes is a corollary when extra
truth-dependent information is supplied. Population changes the
amount of evidence instead, giving ordinary ML a chance to behave
as originally expected WITHOUT the feasibility side-information.
The motivating toy uses molecule types whereas the later proved
population uniqueness result uses a distinct oriented primitive-P2
model; never silently identify those hypotheses.
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

# A second positive result: restrict the candidates

More reads were **one** way to make the inference problem better behaved. We also proved a strong **finite-sample** result by changing which candidate genomes are allowed.

For **oriented reads**, compare genomes of the **same length** and require both the truth and its competitors to be **genuine assemblies under the specified read-overlap constraints**.

**No such competitor can have a higher likelihood than the truth.**

Under the full structural uniqueness hypotheses, a compatible competitor is actually **the same circular genome**, perhaps starting at a different position.

This is an important theorem in its own right—not a qualification of the negative answer to the broader 2016 question.

<!--
Kernel-checked oriented same-length genuine MB09 §6.2 setting,
both truth and competitor genuine candidate certificates:
SameLength62Maximizer.informationFeasible_62_maximizer;
SameLength62Uniqueness.unique_62_maximizer_up_to_rotation.
The latter needs its stated support/structural hypotheses.
This is a distinct finite positive theorem, not the
conditional Bayesian theorem or population P2 result.
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

**We answered the 2016 question: no.** Not-So-Greedy's reconstruction guarantee does not imply that the true genome has the largest **ordinary likelihood**.

That does **not** refute ML's statistical optimality. If the experiment **also includes the reconstruction guarantee as a fact**, the conditional posterior identifies the true genome class with certainty. It is a **different inference problem**.

We proved further results that go beyond that original question: **finite-sample rigidity for restricted candidates**, **population likelihood uniqueness** under precise repeat conditions, and **exponential finite-family recovery** as more reads arrive.

The driving contribution was **choosing and redirecting mathematical questions**, supported by parallel AI agents, continuous orchestration, and kernel-checked Lean proofs.

<HomeLink label="Choose another audience" />

<!--
Scientific hierarchy: the original non-Bayesian finite implication
is FALSE; the counterexample does NOT show ML as an algorithm is
worse on prior-averaged risk; conditional posterior certainty follows
from the externally cited unique NSG decoder when given the
truth-dependent E as side information; it is NOT ordinary ML.
Oriented same-length positive theorem, oriented primitive-P2
population uniqueness, and finite-family recovery are independent
results. Keep the talk accessible, not a catalogue of qualifiers.
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
