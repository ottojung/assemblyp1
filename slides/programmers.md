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

# Assembly begins with overlaps

These reads came in an unknown order. But adjacent reads can agree on their last and first two letters:

```text
ACG → CGT → GTA → TAA → AAC
 ↑                       ↓
 └───────────←───────────┘
```

Following those overlaps spells the circular genome `ACGTA`.

**Assembly turns local matches into a global sequence.**

<!--
Point to ACG -> CGT: the CG suffix matches the CG prefix.
The circular cycle reuses each of the five length-3 windows once.
Explain in words; no graph theory prerequisites.
-->

---

# Why isn't assembly just joining overlaps?

A repeated stretch of DNA can connect to **different neighbors**.

Choosing the first or longest-looking overlap can join two different copies incorrectly. That can collapse repeats or rearrange the sequence.

A *bridging read* extends across a repeat and includes distinguishing letters on both sides:

```text
... G | ACGA | T ...
... C | ACGA | A ...
      repeat
```

**The extra context can rule out a wrong connection.**

<!--
Distinguish the same substring appearing twice from the full read that
extends beyond a specific copy. Avoid claiming any overlap-based greedy
heuristic is optimal.
-->

---

# The existing algorithm was the starting point

In 2016, Shomorony, Kim, Courtade, and Tse introduced **Not-So-Greedy**.

Instead of committing blindly to each largest overlap, it builds and simplifies a sparse network of plausible read connections, then reconstructs a sequence from the remaining structure.

Their theorem guarantees that **this algorithm recovers the true circular genome** under precise coverage and repeat-bridging conditions.

This is a remarkable *algorithmic* guarantee: the procedure works when those conditions hold.

<!--
Shomorony et al., "Information-optimal genome assembly via sparse
read-overlap graphs", Bioinformatics 2016,
https://doi.org/10.1093/bioinformatics/btw450
Theorem 1 and supplementary conditions. The original method prunes
spurious overlaps and modifies edge multiplicities. Deliberately explain
the ideas rather than its full graph construction.
The theorem is about the output of Not-So-Greedy, not an assertion
that every assembly method gets the source.
-->

---

# Another route: statistical inference

An assembler might choose the **shortest sequence compatible with the reads**.

But repeated DNA can make the shortest answer wrong: it may collapse multiple copies into one.

A different idea from Medvedev and Brudno (2009):

**Treat each possible genome as a hypothesis about how the reads were generated.**

Then use probability to compare hypotheses.

<!--
Medvedev & Brudno, "Maximum likelihood genome assembly",
J Comput Biol 2009, DOI 10.1089/cmb.2009.0047.
This replaced standard maximum parsimony with a likelihood framework.
The motivation is not merely that probabilities exist: statistical
decision theory provides concrete optimality theorems.
-->

---

# Every genome predicts a distribution

In our idealized model, each read begins at a **uniformly random position** on the circular genome.

If `AAATT` is the genome, just one of its five positions yields the length-3 read `AAA`.

If `AAAATT` is the genome, two of its six positions yield `AAA`.

$$
P(\texttt{AAA}\mid\texttt{AAATT})=\frac15
\qquad
P(\texttt{AAA}\mid\texttt{AAAATT})=\frac26
$$

**The two candidates predict different sampling frequencies.**

<!--
Independent, error-free, oriented fixed-length reads.
The exact MB09 molecule and approximation models are separate later
branches of the research; this is the simplest generative illustration.
-->

---

# Reads → a probability for each genome

There are two different probabilities, and we need both.

**Likelihood:** If the genome were `G`, how probable would our observed reads `R` be?

$$
P(R\mid G)
$$

**Posterior probability:** After observing `R`, how probable is it that the genome actually is `G`?

$$
P(G\mid R)=\frac{P(R\mid G)\,P(G)}{P(R)}
$$

The extra ingredient is the **prior** $P(G)$ — which genomes we considered plausible *before* seeing the reads.

<!--
This is the requested distinction between a generative likelihood and
the probability of a genome after the reads. Posterior probabilities
require a candidate set and a specified prior; there is no uniform
probability distribution over an unrestricted infinite genome universe.
-->

---

# Why maximum likelihood is interesting

This method is more than a plausible scoring heuristic.

Suppose we must return **one genome**, every wrong answer costs the same, and we have a probabilistic model with a finite set of candidates.

Then the best possible decision after observing the reads is to choose the candidate with the **largest posterior probability**.

That rule is called **MAP** (maximum a posteriori).

**When all candidates have equal prior probability, MAP becomes maximum likelihood (ML).**

Under these assumptions, **ML is at least as accurate on average as any other genome-reconstruction algorithm using the same reads**.

<!--
Optimality is for prior-averaged 0-1 recovery risk, given the same model,
prior and candidate universe. It is not a universal optimum for all losses
or a pointwise guarantee for every true genome / finite read sample.
MIT 6.011 Ch. 13: https://ocw.mit.edu/courses/6-011-introduction-to-communication-control-and-signal-processing-spring-2010/
This finite result is kernel-checked in
AssemblyP1/FiniteBayesDecision.lean.
-->

---

# Why is MAP optimal? A short proof

Imagine we have observed a particular sample $R$.

If we guess genome $D$, our chance of being right is exactly

$$
P(G=D\mid R)
$$

So no choice can do better, **for this observed sample**, than choosing its largest posterior probability.

And if it is best for every observed sample, it is also best **on average over all samples**.

That's the whole decision-theoretic argument.

**Optimal on average does not mean correct every time.**

<!--
FiniteBayesDecision.lean proves the corresponding finite-sample
decision theorem, including that randomizing the decision cannot beat
a MAP choice and that extra observations cannot hurt optimal
prior-averaged recovery under consistent marginals.
The claim compares all decision functions of the same observations.
-->

---

# Two powerful guarantees — but not the same

**Not-So-Greedy (2016)**

Under its specific coverage and bridging hypotheses, the algorithm reconstructs the true genome.

**Maximum likelihood / MAP**

Under a specified statistical model and equal priors for ML, it minimizes the *average* probability of an incorrect choice among candidate genomes.

Neither statement immediately implies the other.

The first is a **conditional algorithmic recovery theorem**. The second is an **optimal statistical decision rule**.

<!--
The Bayesian prior-averaged assertion is not a pointwise conditional
guarantee under the truth-side latent placement event from Shomorony.
Conditioning on that event changes the information provided to the
decision rule. This distinction was a major conceptual research fork.
-->

---

# The question I chose to investigate

Shomorony and colleagues ended their paper with an open question:

If the **coverage and bridging conditions make Not-So-Greedy reconstruct the true genome**, do they also guarantee that the **true genome maximizes likelihood**?

In symbols, schematically:

$$
\text{NSG's success conditions}
\quad\stackrel{?}{\Longrightarrow}\quad
S\in\operatorname*{arg\,max}_D P(R\mid D)
$$

I chose this open question as the starting point for a human-directed, AI-assisted mathematical research project.

<!--
Paraphrase of Shomorony et al. 2016, Discussion, referring to Medvedev
& Brudno 2009. Keep the antecedent about the *algorithm's* success
conditions, not merely an abstract claim that reads contain information.
The symbols are schematic; actual candidate predicates and read
conventions vary across paper interpretations.
-->

---

# A small example: the wrong answer can win

Imagine the true circular genome is `AAATT`.

We independently sample six length-3 reads:

```text
AAA   AAA   AAT   ATT   TTA   TAA
```

Compare two candidates:

**True genome:** `AAATT`, length 5

**Another genome:** `AAAATT`, length 6

Both can generate all six reads. But they predict different frequencies.

<!--
Illustrative unrestricted variable-length candidate comparison.
This example alone is NOT a source-faithful counterexample to every
2016/MB09 candidate class or strand convention.
-->

---

# The complete likelihood calculation

For these observed reads:

| | `AAA` (twice) | Four other reads (once each) |
|:---|---:|---:|
| True `AAATT` | $1/5$ | $1/5$ |
| Other `AAAATT` | $2/6$ | $1/6$ |

Multiply the probabilities for independent draws:

$$
P(R\mid S)=(1/5)^6=\frac1{15625}
$$

$$
P(R\mid D)=(2/6)^2(1/6)^4=\frac1{11664}
$$

The **wrong genome** scores about **34% higher** for this sample.

<!--
Likelihood ratio (D/S) = 15625/11664 ≈ 1.3396.
Count windows explicitly in a code or hand check.
This is an example of empirical-frequency reweighting.
-->

---

# Is this a contradiction to optimality?

No. Suppose, **just for this two-candidate example**, that the two genomes had equal priors.

Bayes' rule would assign the competitor probability

$$
P(D\mid R)=\frac{15625}{15625+11664}\approx57.3\%
$$

We know the true genome was `AAATT` because we constructed the experiment.

But **the data favors the other one**. Choosing it is still the decision that minimizes conditional error *given just this model and these reads*.

**An optimal estimator is not an infallible estimator.**

<!--
The 57.3% is posterior probability in a deliberately restricted
two-hypothesis thought experiment, not a posterior over all genomes.
The true candidate's posterior is about 42.7%. With another prior,
MAP and ML can choose different answers.
-->

---

# We settled the finite question

The 2016 paper asked whether conditions that make **Not-So-Greedy reconstruct the truth** also make the truth a **maximum-likelihood genome**.

**We resolved every determinate, source-supported formulation of that question.**

- **Unrestricted and historical molecule models:** the implication is **false**. We found strict counterexamples, including under the source's original read-string bridging conditions.
- **A specific same-length, oriented, admissible model:** the implication is **true**. We proved maximality and, with the appropriate candidate certificates, uniqueness up to rotation.

The original papers did not fix just one likelihood model. We answered the concrete alternatives rather than guessing which was intended.

<!--
Source: docs/source-notes/interpretation-matrix-217.md, Section 4;
paper/sections/03-open-question.tex and 04-finite-results.tex.
All determinate source-supported rows are resolved. Some *different*
project-specific modeling questions remain open. Source referent itself
was underdetermined; do not present this as the conjecture being unsettled.
-->

---

# These are substantial mathematical results

**Negative:** even when repeat-bridging conditions hold, finite-sample likelihood can favor a different genome. For a historical, same-length molecule model, a certified example achieves a **threefold likelihood advantage**.

**Positive:** under the oriented, same-length admissibility conditions, we proved a general result: the true genome cannot be beaten, and the reconstruction is unique up to circular rotation within the certified class.

**Beyond individual examples:** we found whole families of finite counterexamples, not merely one unlucky dataset.

Many of these results have been **checked in Lean**, not just calculated experimentally.

<!--
Examples: AAATAT -> AAAAAT, G=6, L=3, exact ratio 3 under
same-length §6.2 molecule/flow, module SameLengthSection62Counterexample;
oriented variable-length infinite families in OrientedVariableLengthSe62;
positive same-length §6.2 in SameLength62Maximizer and
SameLength62Uniqueness. Exact limitations in issue #217 matrix.
-->

---

# This research was agentic from day one

On September 17, I began AssemblyP1 with **two things already in place**:

**The mathematical problem:** a real open question from the genome-assembly literature.

**The research method:** cooperating AI research agents, durable work, adaptive orchestration, and Lean as a formal verification boundary.

The AI system wasn't added after the mathematics became complicated.

**I designed the project from the outset to conduct mathematical research by directing that system.**

<!--
Primary evidence: docs/intent-records/project.md, intent records dated
2026/09/17. The initial repository commits already seed Lean, agent
instructions, research orchestration and durable intent records.
This was the methodology at founding, not a post-hoc workaround.
-->

---

# The central work: choosing directions

The important decision was repeatedly **what mathematical question to pursue next**.

```text
2016 open problem
     ↓
Several possible likelihood interpretations
     ├── Counterexamples: where does it fail?
     └── Positive theorems: what rescues it?
                   ↓
       Why do the failures happen?
       ├── Finite sampling fluctuations
       └── Structural non-identifiability
                   ↓
       Bayesian optimality and recovery rates
```

Each result changed the next research question. I prioritized, redirected, and combined these lines of investigation instead of following a predetermined proof plan.

<!--
Provenance: early Sept 17 source-faithful fork and adaptive portfolio
intent; Sept 18-21 finite counterexamples; later positive same-length
rigidity; Sept 20 population repair intent; Oct Bayesian optimality,
identifiability, and sample complexity fronts.
This slide is about intellectual direction and adapting the frontier.
-->

---

# Multiple lines of inquiry, pursued together

Those directions became **parallel research work**.

AI agents could investigate different ideas independently: reading papers, searching small examples, proposing arguments, running computations, and developing Lean proofs.

At one point, a source-interpretation investigation could run alongside a counterexample search and a positive proof attempt.

The value wasn't that several agents agreed. It was that **different hypotheses could be tested simultaneously**, including ideas that turned out to be false.

I used their findings to choose the next questions.

<!--
Agents are persistent, tool-using research workers with independent
worktrees and evidence artifacts. Avoid a generic "what is an agent?"
or a generic tool-comparison slide: agents are introduced through their
actual research role.
-->

---

# Keeping the investigation moving

The research needed to continue beyond any individual work session.

```text
   I set and revise the research frontier
                    ↓
      Antonina: questions and dependencies
                    ↓
   Orchestrator: selects parallel work
                    ↓
       Lubko: agents in isolated worktrees
                    ↓
      Experiments, notes, proofs, PRs
                    ↓
      Reconcile results and update frontier
                    └─────────────↻
```

**The orchestrator kept the work continuous. I supplied the research direction.**

<!--
The evolving queue is Antonina; Lubko provides remote work execution,
isolated worker workspaces and agent runs; Git PRs preserve artifacts;
independent review and CI support integration.
Agent failures and completed packets feed the next dispatch.
The orchestrator schedules useful independent work based on dependency
topology, not as a substitute for the user's research judgment.
-->

---

# How could I trust the proofs?

Agents can discover clever arguments and make subtle mistakes.

**Lean** is a programming language and theorem prover. A theorem is a formal statement, and its proof must pass a small, trusted **kernel checker**.

An agent can propose or construct a proof; Lean does not trust the agent's explanation. It checks the actual formal proof.

Our CI also replays the theorem library and audits which axioms the proofs use.

**The source model determines what we are proving. Lean checks whether the proof follows from that model.**

<!--
Source: AssemblyP1/FiniteBayesDecision.lean and the finite
counterexample/maximality modules. Theorems depend on the allowed
Lean logical axioms. Distinguish proof checking from scientific
interpretation. No unverified "example" code required on the slide.
-->

---

# The result is a growing research program

We started with one open question and settled its concrete finite interpretations.

The same investigation then opened new questions: which conditions characterize identifiability, how reliably does optimal inference recover the truth from a finite sample, and **how many reads are needed for a target success probability?**

Those questions can be pursued with the same structure:

**Human-directed research questions → parallel mathematical exploration → durable results → Lean-checked theorems → new questions.**

The system matters because it supports that continuing cycle of discovery.

<!--
The initial 2016 finite question is settled across determinate
source-supported interpretations. General characterization and
sample-complexity directions remain distinct new research questions;
do not imply all are solved.
-->

---

# The Most Likely Genome

We started with a question from 2016: **Do Not-So-Greedy's reconstruction conditions also make the true genome a maximum-likelihood maximizer?**

**We settled the concrete source-supported finite versions**, proving both strong positive theorems and strict counterexamples.

Along the way, we connected genome reconstruction with a remarkable general fact: **under a specified equal-prior decision model, ML maximizes average correctness over all algorithms using those observations** — yet it can still be wrong on a particular sample.

And we did the research through a system designed from the outset for **human-directed, parallel AI exploration and Lean-checked proofs**.

<HomeLink label="Choose another audience" />
---

# Additional question: what if we had unlimited reads?

This is a **new model**, motivated by the finite sampling failures.

If we replace the observed finite sample with the exact true read distribution, the true genome always maximizes expected log-likelihood:

$$
\ell_S(S)-\ell_S(D)=D_{\mathrm{KL}}(p_S\|p_D)\ge0
$$

The hard question then changes to **uniqueness**: might two different genomes produce exactly the same read distribution?

This is why the project also studies population likelihood and structural identifiability.

<!--
Only use if asked. Do not insert population likelihood unmotivated
between the finite counterexample and finite results.
paper/sections/05-population.tex contains the full theorem.
-->

---

# Additional question: how much do the priors matter?

For two candidates with likelihoods $L_S,L_D$ and prior probabilities $\pi_S,\pi_D$:

$$
\frac{P(D\mid R)}{P(S\mid R)}
=\frac{\pi_D}{\pi_S}\frac{L_D}{L_S}
$$

Equal priors give **maximum likelihood**.

Unequal priors can change the **most probable genome after observing the reads**.

Conditioning on extra information — such as an externally disclosed structural event — changes the Bayesian problem again.

<!--
Useful if the audience asks why a deterministic reconstruction
guarantee can coexist with a finite ML counterexample.
Condition on the actual event in the sample space, including latent
read placements where relevant, rather than simply applying a
truth-feasibility indicator after ordinary likelihood.
-->
