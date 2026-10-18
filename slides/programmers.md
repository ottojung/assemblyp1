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

# Our goal: reconstruct the genome

**What we want:** recover a genome's full DNA sequence from the short fragments, called *reads*, that a sequencer produces.

Suppose we receive these reads, in no particular order:

~~~text
GTA      AAC      CGT      TAA      ACG
~~~

We want to recover **the circular sequence that produced them**:

~~~text
ACGTA
~~~

That is **genome assembly**: reconstructing the original whole from its fragments.

<!--
This slide states the desired INPUT and OUTPUT, not the obstacles.
Do not move repeat ambiguity or difficulty discussion ahead of
the successful worked reconstruction. ACGTA is one way to write
the circular answer; rotations are the same circular genome.
The displayed reads are unordered, fixed-length windows.
-->

---

# The mathematical problem we chose to study

We investigate an **idealized mathematical model** of assembly, not the engineering details of real sequencing.

- **Genome:** a circular string of DNA letters.
- **Reads:** short, equal-length, error-free fragments sampled independently from random positions.
- **Input:** the reads themselves, not their positions or the true genome's length.

Our questions: **When can the true genome be reconstructed? How can we compare the candidates using probability?**

<!--
All the main examples assume oriented reads and uniformly distributed
random starts; read orientation is a technical convention, not a
theme to foreground on the slides. Candidate length is not given
unless explicitly introduced later as additional information.
Circular genomes are defined only up to rotation. Real sequencing
has additional sources of complexity intentionally excluded here.
-->

---

# A first reconstruction: join the overlaps

The end of **ACG** matches the beginning of **CGT**: both share **CG**.

The other reads fit together in the same way:

~~~text
ACG → CGT → GTA → TAA → AAC → ACG
~~~

Each arrow joins reads sharing a two-letter overlap. Following the arrows spells **ACGTA**.

**We reconstructed the genome!** This is the basic idea behind overlap-based assembly.

<!--
Read-overlap graph: vertices are reads, not (L-1)-mers.
AAC -> ACG closes the circular sequence. This is a positive
worked solution to the goal shown two slides earlier.
Only now introduce ambiguous overlaps and repeats.
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

# What does the "best" assembly algorithm mean?

Imagine playing the **same guessing game** many times:

1. Secretly choose genome **A** or **B**, each with a **50%** chance.
2. Draw **two random reads** from the chosen genome.
3. Show only the reads to an algorithm. It must guess **A** or **B**.

**Score:** how often does its guess match the hidden true genome?

We've already calculated that when the reads are **AAA, AAA**:

- **80%** of those games came from **B**.
- **20%** came from **A**.

So guessing **B** gets **80%** of these games right. Guessing **A** gets only **20%** right.

<!--
The candidate set is exactly {A=AAATT, B=AAAAT}, equal prior 1/2,
two independent length-3 oriented uniform-start reads.
For the observation r=[AAA,AAA],
P(r|A)=1/25 and P(r|B)=4/25.
Bayes gives P(B|r)=4/5 and P(A|r)=1/5.
Correctness is scored across repeated complete experiments
(genome, two-read sample), NOT random placements with the truth fixed.
The preceding two-read slide already proved the 80/20 split.
-->

---

# Why no algorithm can beat maximum likelihood in this game

Because **A and B are equally likely beforehand**, their probabilities *after seeing the reads* are their likelihoods **divided by the same sum**.

So ML always guesses the genome **most likely to be true** given those reads.

Now consider **any other algorithm**. For any possible reads, it either:

- **Agrees with ML:** their chance of being right is the same.
- **Disagrees with ML:** it picks an answer with **no higher chance** of being right.

It cannot make up for a worse guess elsewhere: **ML already makes the best choice for every observation.**

Therefore **ML has the highest overall chance of a correct guess** in our experiment.

**But it can still be wrong:** when the reads are **AAA, AAA**, ML's guess fails in **20%** of those cases.

<!--
Direct per-observation decision proof. General finite hypotheses
H, observations R, prior π, equal 0-1 correctness:
P(f(R)=H) = sum_r P(R=r) P(H=f(r)|R=r)
         <= sum_r P(R=r) max_g P(H=g|R=r).
MAP attains each maximum. Under uniform π, MAP equals ML, since
P(H=g|r)=P(r|g)/sum_h P(r|h) when P(r)>0.
Decisions on zero-probability observations do not affect accuracy.
Randomized rules yield convex combinations of conditional success
rates, never above their maximum.
Lean: AssemblyP1/FiniteBayesDecision.lean.
All algorithms get the same reads, prior, candidate set and
0-1 correctness measure. No truth-by-truth guarantee or extra
reconstruction-success promise is assumed.
Kernel-checked converse and tie refinement: a deterministic rule is
optimal exactly when it is pointwise MAP (BayesOptimalityCertificate
pointwiseMAP_iff_bayesOptimal); a rule missing a per-observation
maximizer strictly loses; on a tie two distinct rules can both be
optimal, while a strict maximizer forces the unique choice. The scope
remains prior-averaged, not per-truth.
-->

---

# The 2016 question: does the guarantee imply ML?

We have **two methods**:

**Not-So-Greedy:** reconstruct by overlaps when the coverage and repeat-bridging conditions guarantee success.

**Maximum likelihood:** choose whichever candidate makes the observed reads most probable.

The 2016 sentence hides **two different questions**:

- **Question A (conditional):** restrict candidates to those satisfying the reconstruction conditions. The guarantee then forces the answer to be the truth's circular class — a corollary of reconstruction, not a new likelihood result.
- **Question B (unconditional):** without that restriction, must the true genome maximize **ordinary** likelihood?

**Our answer to Question B is no.** We found a counterexample in which the competing assembly is one base longer.

<!--
Two questions (paper sec:intro:two-questions, sec:two-questions):
Question A conditions on the truth-dependent feasible fiber {g : F(g,R)}
and is largely a corollary of the published 2016 reconstruction theorem.
Question B assumes only F(S,R) and maximizes the ORIGINAL unrestricted
likelihood; that is the substantive comparison, and the source's
non-Bayesian implication from the true genome's structural event to
unconditioned P(R|D) ranking. The exact 2016 MB09 objective is not named
unambiguously, but oriented candidate-intrinsic exact likelihood is
source-supported. The counterexample is kernel-checked in
OrientedVariableLengthSe62. Do not suggest all readings have a
model-independent identical mathematical statement; keep the explicit
candidate-length scope. Ordinary ML never observes the event E=F(S,R).
-->

---

# A counterexample in six reads

**True genome:** AAATT (length **5**) · **Competitor:** AAAATT (length **6**).

**Six length-3 reads sampled from the truth:**

~~~text
AAA    AAA    AAT    ATT    TTA    TAA
~~~

| Read type | Observed | Starts in truth | Starts in competitor |
| --- | ---: | ---: | ---: |
| AAA | **2** | 1 | **2** |
| AAT, ATT, TTA, TAA (each) | 1 | 1 | 1 |

**The truth satisfies coverage and repeat bridging.** Both genomes are legitimate read-overlap candidates.

The true genome's length is **not** supplied to the assembler.

<!--
OrientedVariableLengthSe62.lean theorem and script
verify_oriented_variable_length_se62.py. Source truth S=AAATT,
L=3, true starts 0,0,1,2,3,4; full coverage and strict bridging,
all triple copies checked, interleaved pair vacuous.
Both S and D=AAAATT admit genuine oriented Section 6.2
read-overlap candidates. Variable candidate length is essential.
No reverse-complement grouping. The four grouped types
AAT, ATT, TTA, TAA are EACH observed once and occur at
one start in EACH genome. This table preserves the data
of the original five-row version without the vertical overflow.
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

# Why the two methods do not contradict each other

**Not-So-Greedy** answers **Question A**: given the reconstruction conditions, it returns the truth's circular class.

**Ordinary ML** answers **Question B**: it scores genomes using the reads, without being told whether the conditions hold for the actual source.

Our example satisfies the reconstruction conditions, yet a different candidate makes the sampled reads more probable.

This does not contradict ML's **average-accuracy optimality**. Question A and Question B are different experiments — the promise is information ordinary ML never receives.

<!--
Question A is the conditional/feasible-fiber reading; Question B is the
unconditional ordinary-likelihood comparison. Not-So-Greedy is a read-only
algorithm with a truth-dependent pointwise success theorem; ordinary ML is
a likelihood ranking over its specified candidate class. Prior-averaged
MAP/ML optimality is a distinct decision criterion. No algorithm has been
proved inferior under the same conditioned decision problem.
-->

---

# A positive result: what if the genome length is known?

Suppose we know the true genome has **length 5**. Our six-letter competitor is excluded. But can **any** valid five-letter assembly beat the truth?

**We proved a general theorem:**

Under the coverage and bridging conditions, if **the truth and every competitor are genuine read-overlap assembly candidates of the same length**, each eligible competitor is merely a **rotation of the true circular genome**.

So **the truth is a maximum-likelihood answer**—indeed, every eligible answer reconstructs the same circle.

<!--
This is not unrestricted same-length ML on all circular words.
SameLength62Maximizer.informationFeasible_62_maximizer proves exact
likelihood domination. Stronger:
SameLength62Uniqueness.unique_62_maximizer_up_to_rotation says any
genuine same-length Section 6.2 candidate is a rotation of the truth,
assuming the full InformationFeasible event at the actual sampled
starts, both truth and competitor genuine Section 6.2 certificates,
and 2 <= L <= G. A rotation has identical circular window counts.
Do not imply that just fixing lengths repairs the original
unrestricted search over all circular strings.
-->

---

# But can we assume that length is known?

In some settings, genome length can be measured or estimated independently. **Our theorem needs its exact value in advance.**

We wanted something stronger: **a guarantee that does not require knowing the answer's length before reconstructing it.**

Could we instead restrict candidates using **properties we can check on each candidate itself**, such as the absence of repeats?

That led us to investigate a different obstacle.

<!--
A candidate-length restriction is additional knowledge about the
true genome, not inherently a Bayesian extension. It can be expressed
through a prior, but the finite same-length theorem is structural.
The MB09 externally supplied N in its binomial objective is not by
itself a proof that all candidate lengths equal the true length.
The same-length theorem rules out the exhibited longer competitor,
not every failure of ML with unknown length.
-->

---

# Even genomes without repeats can fool finite ML

Try a strong structural restriction: **neither genome has any repeated two-letter substring**.

| | Genome |
| --- | --- |
| True circle | `AABBC` (length 5) |
| Competing circle | `AABC` (length 4) |

Two reads actually sampled from the truth: **AAB, BCA**. Together they cover the true circle.

Each read occurs at **1 of 5** starts in the truth, but **1 of 4** in the competitor:

$$
\frac{P(R\mid\text{competitor})}{P(R\mid\text{truth})}
=\frac{(1/4)^2}{(1/5)^2}=\frac{25}{16}>1.
$$

**Even with no repeats, a small sample may make the wrong genome appear more likely.**

<!--
This is the P1 counterexample in
docs/maximum-likelihood-models-for-genome-assembly.md section 5.
Here L=3 and the two distinct sampled start positions are 0 and 3.
Truth AABBC has length-2 windows AA,AB,BB,BC,CA; D=AABC has
AA,AB,BC,CA: each is P1 (no repeated length-2 substring).
Both are primitive. Truth coverage holds; repeat clauses vacuous.
This illustrates likelihood over a candidate-intrinsic no-repeat
class, NOT the same Section 6.2 observed-support class of the
preceding theorem. Do not present it as a counterexample to the
same-length `6.2 theorem. Lengths differ here too: the point is
that intrinsic no-repeat conditions do not alone repair finite ML.
-->

---

# The clue: the wrong genome fits our six reads exactly

Return to **AAATT** versus **AAAATT**. We observed **AAA twice** and each of the other four reads **once**:

- Sample frequencies: **2/6** for AAA, **1/6** for each other read.
- Those are **exactly the read probabilities of AAAATT**, the wrong genome.

In fact, for any finite sample, **no read distribution has greater likelihood than its observed frequencies**. AAAATT therefore achieves the **best likelihood any read distribution could achieve on our six reads**.

It was bound to beat the truth on that sample, not merely lucky to win against one particular competitor.

**My next question:** Is the problem the noise in a small sample? What if the read frequencies settled toward their true values?

<!--
For counts x_w summing to n and any probability mass function q:
log L(q) - log L(x/n)
  = sum_w x_w log(q_w/(x_w/n))
  = -n KL(x/n || q) <= 0,
with the usual zero conventions. Equality iff q=x/n.
This applies to ordered iid reads; the multinomial coefficient
for unordered count observations is independent of q, so has the
same maximizer. In this example x=(2,1,1,1,1), n=6,
q_D=x/6 and q_S=(1,1,1,1,1)/5. Thus D achieves the
global simplex optimum and S does not. This is separate from
the combinatorial constraints of which q can be realized by
a genome; here the optimal q happens to be realized by D.
The hypothesis of finite-sampling noise was the human research
director's conceptual pivot, not uncertainty about the negative answer.
-->

---

# Population likelihood: remove sampling noise

Here **population** means the complete read distribution from **one fixed genome**, not a population of genomes.

Compare our six observations with the read distributions of both genomes:

| Read type | True AAATT | Competitor AAAATT | Six-read sample |
| --- | ---: | ---: | ---: |
| AAA | **1/5** | 2/6 | **2/6** |
| AAT | **1/5** | 1/6 | 1/6 |
| ATT | **1/5** | 1/6 | 1/6 |
| TTA | **1/5** | 1/6 | 1/6 |
| TAA | **1/5** | 1/6 | 1/6 |

A small sample happens to match the **wrong column**. With more independent reads, observed frequencies approach the **true column**.

Population likelihood asks which genome best explains **those limiting frequencies**.

<!--
Population is expected per-read log-likelihood, not an infinite
product of probabilities. IID law of large numbers motivates
empirical frequencies tending to p_S. Gibbs/KL says truth's
distribution globally maximizes expected log likelihood;
genome uniqueness is a separate structural problem.
-->

---

# When the exact read distribution is known

**First:** the true genome always maximizes population likelihood. No different read distribution explains the true frequencies better.

**But could two different genomes produce exactly the same distribution and tie?**

**We proved uniqueness** if the truth and competing genomes are **primitive and P2-admissible**. In this class, only rotations of the true circular genome can tie—even when candidate lengths are not fixed in advance.

*Primitive* means the whole genome is not a shorter pattern repeated. **P2**, rooted in the repeat analysis of **Bresler, Bresler & Tse (2013)**, excludes certain long triple and interleaved repeats.

<!--
PopulationGibbs.popLogLik_le_self' and popTie_iff:
ell_S(D)-ell_S(S)=-KL(p_S || p_D) <= 0, with equality
iff p_S=p_D. Issue94Complete.population_unique_ML is checked
for primitive P2 genomes, L>=2, candidates up to rotation;
no external Bresler axiom. Candidate lengths need not agree.
P2 excludes triple repeats of length >=L-1 and interleaved
maximal-repeat pairs both of length >=L-1. Do not claim
unrestricted population uniqueness: non-identifiable
normalized spectra can tie.
-->

---

# Do we actually need infinitely many reads?

**No.** The population theorem motivates a result about **finite data**.

For an identifiable **finite family** of candidate genomes, as more independent reads arrive, the probability that a wrong candidate ties or beats the truth **falls exponentially**.

For our **primitive-P2** class the rate is now **explicit and kernel-checked**: with read length $L$, alphabet size $q$, and $B=2q^{L-1}$, the exact-ML error probability is at most $N_C\exp(-n/(8B^4))$, so $n\ge 8B^4\ln(N_C/\delta)$ reads suffice for error at most $\delta$ (full statement and caveats in backup B3).

With enough reads, ML can therefore achieve **99% recovery probability**—or any other desired confidence—for such a family.

The **limit** behind both statements is exact: for a finite identifiable family, the per-read log-likelihood gap converges to the KL divergence, so almost surely the ML selection set is eventually exactly the truth's rotation class (strong law + KL; not kernel-checked here — backup B6). "Infinite reads" is a limit of finite samples; it supplies **no finite read count**.

The population result says **what information identifies the genome**. The finite theorem tells us **how additional observations improve our chances**.

<!--
FiniteReadRecovery and FiniteReadRecoveryGenome, plus
FiniteReadRecoveryP2Bridge and FiniteReadRecoveryP2Complete:
error probability <= |C| rho_*^n for a finite distinguishable
class C and rho_* < 1. P2/primitivity ensure distinction
up to rotation under the relevant constraints. No universal
constant read count for an unrestricted competitor universe.
Probability here is over random reads from a fixed truth, not
the earlier prior-averaged Bayes decision experiment.
#265 refinement (2026-10-18): the Hellinger constant -ln rho_* can be replaced
by the Chernoff information C_* >= ln(1/rho_*), and C_* is the exact
large-deviation exponent of the finite-family exact-ML error (external
Chernoff/Sanov, NOT kernel-checked). The bound is still not tight at finite n
(~3.7x the exact error at n=16 on the worked family). Paper
prop:chernoff-refinement / rem:chernoff-sharp; see backup B3 and
docs/chernoff-exponent-finite-recovery-265.md. Do not claim a tight finite-n
bound or that C_* is kernel-checked.
-->

---

# Question A: what if we are promised reconstruction works?

There is a separate way to add information. Suppose we are explicitly told:

> The actual genome and these reads satisfy Not-So-Greedy's reconstruction conditions.

Not-So-Greedy reads **only the reads** and, under that promise, returns the true circle.

If two different genomes met the promise for the **same reads**, its single output would have to equal both. Impossible.

So with this additional promise, the **conditional Bayesian posterior is 100%** on one circular-genome class.

**This is Question A**, the conditional experiment from the earlier slide. The promise is a truth-dependent restriction — extra information ordinary ML (Question B) never receives.

<!--
This is the detailed Question A endpoint (paper sec:two-questions,
Question A). Source theorem is an external read-only unique-decoder
premise: F(g,r) => A(r) ~ g. Therefore the feasible fibre at r is
one rotation class. Conditional joint
K(g,r)=π(g)P_g(r)1_F(g,r) has support on that class,
so given (r,F) and positive mass, posterior=1.
Kernel consequences ConditionalIdentifiability.lean.
Do not substitute a placement-based predicate or ignore
marginalization over latent read starts. Unlike same-length
or population uniqueness, this uses a truth-dependent
additional event supplied as external knowledge.
-->

---

# Choosing the next research question

The project began with **the 2016 question**—not a predetermined answer.

Four turns shaped the investigation:

1. **Test the 2016 implication:** find a concrete counterexample.
2. **Repair the failure:** prove the same-length theorem, then question whether knowing the true length is a satisfactory assumption.
3. **Look deeper:** test candidate-intrinsic restrictions and identify the effect of finite-sample frequencies.
4. **Ask what more reads buy us:** prove population uniqueness and finite-read recovery results.

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

**We separated the 2016 sentence into two questions.** Question B (unconditional) is answered negatively: the true genome can meet reconstruction conditions while a longer competing genome has greater ordinary likelihood. Question A (conditional) is the reconstruction guarantee itself.

We also clarified what this means statistically: a reconstruction promise is additional information. When it is explicitly given, the conditional posterior identifies the true circular genome class.

Beyond the counterexample, we proved **population ML uniqueness**, **finite-family reliability**, and a **restricted same-length positive theorem**.

The results came from **human-led hypotheses**, parallel AI research, and **Lean-checked mathematics**.


<!--
Question A = conditional feasible-fiber reading (corollary of the published
reconstruction premise); Question B = unconditional ordinary likelihood.
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

Invert the bound: to push it below a target $\delta$, it is **enough** to take

$$
n \;\ge\; \frac{\ln(|\mathcal C|/\delta)}{\ln(1/\rho_*)} .
$$

One competitor with affinity $\rho_*=\sqrt3/2\approx0.87$ needs $n\ge 33$ reads for a $1\%$ bound.

For the **primitive-P2** admissible class the abstract gap $\rho_*<1$ is now **explicit and kernel-checked**. With alphabet size $q=|\alpha|$, read length $L\ge2$, and $B=2q^{L-1}$, over the complete nonrotational primitive-P2 class:

$$
\Pr_S\!\left[\exists\,D\ \text{nonrotational admissible}:\ L_D(R_1,\dots,R_n)\ge L_S(R_1,\dots,R_n)\right]
\;\le\; N_C\,\exp\!\left(-\frac{n}{8B^4}\right),
\qquad N_C\le\sum_{g=1}^{B}q^{g},
$$

and $n\ge 8B^4\ln(N_C/\delta)$ reads suffice for error at most $\delta$.

**Caveats.** The constants are deliberately loose and exponential in $L$; the bound controls the exact-ML **error probability**, not likelihood growth; and per-truth finite-sample success is **not monotone**. The class is primitive-P2, oriented, exact iid reads — not universal ML and not the MB09 product-binomial surrogate. Kernel endpoints: `AssemblyP1.PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound` and `primitiveP2_ML_confidence_explicit`.

**What remains open:** one sharp, uniform sample-size guarantee over the unrestricted universe of genome candidates, especially across different lengths and models.

<!--
The explicit n is the algebraic inversion of the kernel-checked union bound
(FiniteReadRecovery.eventProb_wrong_le_card; concrete instance
il_confidence_99: |Θ|=3, ρ=9/10, n=55). It is SUFFICIENT, not necessary,
and conservative (union bound; -ln ρ ≤ Chernoff exponent). It does not
cover the unrestricted universe or different lengths/models; that stays open.
FiniteReadRecovery, FiniteReadRecoveryGenome, FiniteReadRecoveryP2Bridge,
FiniteReadRecoveryP2Complete. Do not claim sample complexity is wholly open;
the finite-family confidence theorem is established. Finite family, positive
separation, iid oriented reads, and the candidate model matter.
The explicit uniform rate over the primitive-P2 class is #281, kernel-checked
in PrimitiveP2UniformSeparation (endpoints primitiveP2_exponential_error_bound
and primitiveP2_ML_confidence_explicit; B = maxLen L = 2 q^(L-1); N_C is the
number of distinct competitor read laws, N_C <= sum_{g=1}^{B} q^g). It is a
frequentist uniform-separation statement for the exact oriented iid
multinomial likelihood, distinct from the Bayes/MAP rationale. State the three
caveats: constants deliberately loose and exponential in L; it bounds the
exact-ML ERROR PROBABILITY, not likelihood growth; and per-truth finite-sample
success is NOT monotone. This is not universal ML over all genomes and not the
MB09 product-binomial surrogate.
#265 Chernoff refinement (2026-10-18): replace -ln rho_* by
C_* = min_D C(p_S,p_D), C(p,q) = sup_{t in [0,1]} -ln sum_{w:p(w)>0}
p(w)^(1-t) q(w)^t >= -ln rho(p,q). Termwise the Chernoff union bound
sum_D exp(-n C(p_S,p_D)) is no larger, and C_* is the EXACT exponent of the
finite-family exact-ML error (standard Chernoff/Sanov; EXTERNAL, not
kernel-checked). It is still not tight at finite n: on p=(3/4,1/4) with
competitors (1/4,3/4), (0,1), the bound is ~3.7x the exact error at n=16 and
the bound/exact ratio grows ~sqrt(n). Paper prop:chernoff-refinement /
rem:chernoff-sharp; note docs/chernoff-exponent-finite-recovery-265.md; exact
check scripts/verify_chernoff_finite_recovery_265.py. The kernel-checked
constant remains rho_* (FiniteReadRecovery). No tight or minimax finite-n
claim.
-->

---

# Backup B4: more reads help on average, not for every genome

Adding a read cannot lower the **prior-averaged** chance of guessing the genome correctly: a rule may simply ignore the extra read.

But the **per-genome** success probability is **not** monotone in the number of reads.

Two circular genomes, read length 2, alphabet `{A, C}`, uniform starts:

| | `AA` | `AC` | `CA` | `CC` |
| --- | ---: | ---: | ---: | ---: |
| Truth `AAC` | $1/3$ | $1/3$ | $1/3$ | $0$ |
| Competitor `AAAC` | $1/2$ | $1/4$ | $1/4$ | $0$ |

The truth is the strict exact-ML maximizer with probability

$$
\operatorname{succ}(1)=\frac23,\qquad
\operatorname{succ}(2)=\frac49,\qquad
\operatorname{succ}(1)>\operatorname{succ}(2).
$$

More reads still drive the success probability to $1$ eventually. The dip is a finite-sample effect, not a failure of consistency.

<!--
This is the #265 item-4 contrast, absent from the earlier arc:
prior-averaged success is nondecreasing in n (a rule can ignore an extra
read): FiniteBayesDecision.chooseMAP_success_monotone_under_refinement.
Per-truth success need not be: NonmonotonicityWitness281.success_not_monotone,
kernel-checked, succ(1)=2/3 > succ(2)=4/9. Tie handling: for n>=1 the exact
likelihood ratio is 3^n / 2^(2n-a) (a = number of AA reads), never 1, so no
positive-probability ties; n=0 ties. Independent exact-rational check:
scripts/verify_nonmonotonicity_witness_281.py. Do NOT claim per-truth
monotonicity; the exponential bound is about the eventual rate, not a
monotone curve.
-->

---

# Backup B5: primary sources

- Medvedev & Brudno (2009), *Maximum Likelihood Genome Assembly*.
- Shomorony, Kim, Courtade & Tse (2016), *Information-optimal genome assembly via sparse read-overlap graphs*.
- Bresler, Bresler & Tse (2013), *Optimal assembly for high throughput shotgun sequencing*.
- Berger (1985), *Statistical Decision Theory and Bayesian Analysis*.
- Cover & Thomas (2006), *Elements of Information Theory*.
- Tsybakov (2009), *Introduction to Nonparametric Estimation*.

**[Research repository](https://github.com/ottojung/assemblyp1)**

---

# Backup B6: "Infinite reads" is a limit, not a large sample

For a **finite identifiable family**, each per-read log-likelihood gap is an average of iid terms whose expectation is a KL divergence:

$$
\frac1n\log\frac{L_S}{L_D}(R_1,\dots,R_n)
\;\xrightarrow{\text{a.s.}}\;
D_{\mathrm{KL}}(p_S\|p_D)>0
\quad\text{(strong law of large numbers).}
$$

Every wrong candidate has KL $>0$; there are finitely many of them, so almost surely there is an $N$ with $L_S>L_D$ for **all** wrong $D$ at every $n\ge N$. Rotations of the truth tie it at every $n$ (identical laws). Hence the exact-ML selection set is **eventually exactly the truth's rotation class**, and the probability of being correct at $n$ tends to $1$.

**The limit is not an infinite product.** The claim is about finite samples growing without bound. It gives no finite $n$, no rate, and no guarantee for one particular sample, truth, or an unrestricted universe. Classical statistics (strong law + KL nonnegativity; Durrett 2019, Cover & Thomas 2006), **not kernel-checked**; the kernel-checked Hellinger bound reaches the same a.s. conclusion via Borel--Cantelli (summable $\rho^n$).

<!--
#265 item-5 limit statement, paper prop:strong-consistency (Section
sec:strong-consistency): hypotheses = finite candidate family identifiable
modulo rotation, iid exact reads, correct model; proof = strong law on the
per-read log-likelihood average + KL positivity + finite union; rotations tie
at every n by design; nonrotational ties are impossible eventually because
the limit separates strictly (KL > 0). Support convention 0 log 0 = 0; if
p_D(w) = 0 < p_S(w) then KL = +infinity and the competitor loses on every
sample containing w, which recurs eventually. Distinct from population
uniqueness (no sampling, law level) and from the sample-complexity problem
(this limit supplies no finite n; the explicit kernel-checked bound is the
rate statement). Witness numbers (AAC vs AAAC, L=2, binary): KL =
(1/3)log(2/3)+(2/3)log(4/3) ~ 0.0566, Hellinger affinity ~ 0.9856,
summable geometric series. Exact check: scripts/verify_strong_consistency_265.py.
-->
