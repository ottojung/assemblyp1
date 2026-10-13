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

Under these assumptions, no competing decision rule has a higher *average probability of correctly identifying the genome*.

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

The answer depends on the exact sampling model and which genomes are allowed as candidates.

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

# From one example to a research program

The tiny example establishes a mechanism — it does **not** settle every precise version of the 2016 question.

The research therefore branched:

- **Which finite models permit strict counterexamples?**
- **Which restrictions restore a positive theorem?**
- **What happens when read orientation or genome length changes?**
- **How does Bayesian side information change the answer?**

This was not a straight line from a conjecture to a proof. **The questions evolved as new results changed what was plausible.**

<!--
The historical paper has exact multinomial, fixed-size product-binomial
approximation, and bidirected molecule/flow interpretations, with
different candidate domains and latent read-start versus observed
read-string conditions. The project records distinct proved rows in
docs/source-notes/interpretation-matrix-217.md. Keep slide conceptual.
-->

---

# What the finite investigation found

In a **restricted, same-length, oriented** assembly model with bridging and candidate-admissibility hypotheses, the true genome has a positive maximum-likelihood guarantee.

In **broader candidate models**, strict finite-sample likelihood counterexamples exist — including variants faithful to the historical molecule/read-string conventions.

So the answer is not simply “yes” or “no” without a model.

**The interesting mathematical object became the boundary between the guarantees.**

<!--
See paper/sections/04-finite-results.tex and the interpretation matrix.
Do not transfer the positive same-length theorem to unrestricted candidate
lengths, or transfer one negative witness to an incompatible source model.
-->

---

# The research changed direction several times

**September 17:** I chose a specific open question from the literature and started a research project around it.

**September 18–21:** Counterexamples and source-model differences turned a single conjecture into several precise, different mathematical questions.

**Late September:** I pursued positive structural results alongside the negative ones, and pushed for end-to-end theorems in Lean rather than isolated lemmas.

**October:** I broadened the program: Bayesian optimality, identifiability, necessary-and-sufficient conditions, and how many reads are needed for reliable recovery.

<!--
Provenance: repository history, issues #1, #5, #21, #22, #45,
#82, #83, #87-#92, #269, #270 and #281; Sept-Oct project
research conversations. The October extensions are directions in
progress, not assertions they have all been solved.
The presenter's own major contribution was directing and redirecting
the agenda based on new mathematical evidence.
-->

---

# My central job was choosing the next question

A counterexample is useful — but **what should we ask next?**

When variable-length candidates fail, maybe equal length gives a theorem. If that works, ask whether equal length is necessary.

When the finite-sample score fails, ask whether failure is caused by **sampling noise** or by **indistinguishable genomes**.

When Bayesian optimality is proved, ask how fast recovery improves with more reads, and how its read requirements compare with Not-So-Greedy.

**The valuable work was repeatedly finding these forks and deciding which were worth pursuing.**

<!--
This is intellectual direction and hypothesis generation, not the
trivial requirement that a proof match its statement.
User pushed especially for necessary/sufficient conditions and a
like-for-like comparison of 99% recovery sample complexities.
-->

---

# Why not simply use one chatbot?

A tool-equipped chatbot can search papers, write code, and reason through a theorem.

But **one conversational session is a poor structure for a large, branching research program**:

- Only one line of work advances at a time.
- Long searches consume and eventually exceed conversational context.
- Failed attempts and partial results are easily lost.
- Independent investigations and reviews compete for attention.

I wanted **multiple persistent agents**, each able to work on a distinct question and leave inspectable evidence.

<!--
Multiple agents are not intrinsically more mathematically reliable.
The gains are concurrency, specialization, independent falsification,
durable memory and recovery, not "more votes" on whether a theorem is true.
-->

---

# What an agent actually does

An agent is an AI model **running a multi-step job with tools and a goal**.

It can read papers and code, generate hypotheses, search for counterexamples, run tests, edit files, and revise its approach after feedback.

For this project, agents worked on **different fronts**:

**Literature and model** · **Counterexample search** · **Positive proofs** · **Lean formalization** · **Independent review**

Each front produces durable artifacts — notes, issues, branches, commits, and proof results — rather than just an answer in a chat.

<!--
A workflow agent is not only a chat response. It maintains a sequence
of tool-mediated actions and a work context. Its results remain
uncertain until checked; different agents can disagree legitimately
because of model assumptions.
-->

---

# I built a continuous research loop

```text
 I choose and refine the research directions
                    ↓
       Antonina board: open questions
                    ↓
       Orchestrator selects ready work
                    ↓
   Parallel agents → isolated worktrees
                    ↓
   Experiments · Lean proofs · PRs · CI
                    ↓
     Review, reconcile, merge, update
                    └───────────↻
```

The crucial feature is the **feedback loop**: completion or failure changes the research frontier, and further work can continue from durable state.

<!--
AssemblyP1 used Antonina for its evolving issue queue, Lubko hosts for
remote commands and agents, Git branches/worktrees to isolate changes,
and GitHub PR/CI for review and integration.
The user steered through direct agent guidance and Antonina issue comments.
The orchestrator schedules using dependency topology and available
independent work, aiming to keep useful research parallel.
This represents the design, not a guarantee the service never fails.
-->

---

# Why use Lean?

Agents are useful at **inventing** arguments. They can also make subtle mistakes.

Lean is a programming language and theorem prover. A theorem is a **type**; a proof is a program whose type must match it.

```lean
theorem sum_commutes (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
```

**Lean's small kernel checks the proof**, not the agent's confidence.

The kernel does not have to trust the creativity, confidence, or correctness of the agent that proposed it.

<!--
Lean reference: https://lean-lang.org/doc/reference/latest/
Elaborators/tactics generate proof terms; the small trusted kernel
checks them. The project additionally replays the library through
lean4checker and audits axioms in CI.
This is why the trust boundary is smaller than for free-form AI prose.
-->

---

# We proved a piece of the statistical story

AssemblyP1 includes a Lean-checked finite Bayesian theorem:

**For any finite hypothesis and observation spaces, a pointwise MAP decision rule has at least as high prior-averaged success as any other decision rule.**

The development also covers randomized decision rules and the fact that additional information cannot hurt optimal Bayesian recovery.

That is an example of how a **general claim about optimal decisions** can become a machine-checked theorem, not just an intuition.

<!--
AssemblyP1/FiniteBayesDecision.lean:
pointwise_MAP_optimal; pointwise_MAP_optimal_randomized;
finite_iid_MAP_optimal;
chooseMAP_success_monotone_under_refinement.
Distinguish this generic finite decision result from a complete
assembly-specific ML theorem for every historical model.
-->

---

# What do we actually need to trust?

**Agent-generated arguments:** useful ideas, **not** automatically reliable.

**Lean-checked proof:** a result follows from its formal premises in the kernel's logic.

**Scientific interpretation:** those premises must still describe the intended sequencing model.

This gives a division of labor:

**I guide the questions. Agents explore. The orchestrator sustains the work. Lean checks mathematical proofs.**

None of these roles replaces the others.

<!--
Lean cannot detect a faithfully proved theorem about an unintended
definition. The user directed source-model fidelity as scientific
interpretation; that is different from reducing research to a checking
workflow. Keep this slide human-centered.
-->

---

# What I wanted to explore next

The most interesting questions now go beyond a yes/no statement:

- When does the read data **uniquely identify** the true genome?
- Under what conditions does the optimal Bayesian or ML rule recover it **with high probability**?
- How many random reads give, say, **99% success**?
- Under the **same sampling assumptions**, how does this compare with Not-So-Greedy?

Those are research directions, not claims that every theorem has already been proved.

<!--
The user elevated sample complexity, monotonic finite recovery,
identifiability and necessary/sufficient characterizations in
October 2026; AssemblyP1 issue #281 concerns exponential ML recovery
bounds, and #269 concerns Bayesian decision optimality.
-->

---

# The Most Likely Genome

We started with a deceptively simple question:

**Does an assembly algorithm's success guarantee imply that the true genome also maximizes likelihood?**

The answer depends on the model. But the investigation revealed something broader:

**A method can be statistically optimal without being correct on every sample.**

And difficult mathematical research can be advanced by combining **human direction, persistent agents, and machine-checked proofs**.

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
