# The conceptual story behind the programmers' talk

## What this talk is about

The project is not primarily a tutorial on genome assembly, a catalogue of
proofs, or a productivity report on agents. It studies an apparent collision of
two powerful ideas:

1. **Algorithmic reconstruction guarantees.** Under precise coverage and
   repeat-bridging conditions, Shomorony et al.'s Not-So-Greedy algorithm
   returns the true circular genome (up to rotation).
2. **Statistical decision optimality.** Given a finite candidate class, a
   sampling model, a prior, and equal cost for each wrong answer, choosing the
   maximum-posterior candidate minimizes expected misclassification. With a
   uniform prior, this is maximum likelihood.

These are not contradictory. Algorithmic recovery is guaranteed *pointwise on
a structurally defined event*; Bayesian optimality is *prior-averaged under a
probabilistic model*. They may condition on different information. Moreover,
P(reads | genome) (likelihood) is not P(genome | reads) (posterior); the
latter also needs a prior.

The motivating 2016 question is whether the *success conditions for that
particular algorithm* imply that the true genome also maximizes the likelihood
of those observed reads. It is wrong to replace that antecedent with a generic
claim that the reads contain information; it is wrong to portray the
consequent simply as a vague "principled score."

### Why likelihood can be called optimal, precisely

For finite hypotheses H, finite observations X, a prior π and read model
P(X|H), MAP selects argmax_H π(H)P(X|H). For any observed x and decision
a(x), its probability of being correct is P(H=a(x)|x). This is bounded by
max_H P(H|x). Average that inequality over x: MAP minimizes prior-averaged
0–1 loss among all decisions using the same observations (including randomized
decisions). For a uniform prior over **the stated finite candidate set**,
ML=MAP. This statement is exact at finite n; it does not say ML succeeds
on every sample or that it minimizes risk for every fixed genome. AssemblyP1
formalizes this result in AssemblyP1/FiniteBayesDecision.lean.

For a two-candidate illustrative model, S=AAATT, D=AAAATT,
R=[AAA,AAA,AAT,ATT,TTA,TAA] at L=3:
- L(S)=1/15625
- L(D)=1/11664
- L(D)/L(S)=15625/11664≈1.33959
- with equal priors ONLY over these two candidates,
  posterior(D|R)=15625/(15625+11664)≈0.5726.
Thus a statistically optimal rule can select a genome other than the
constructed source for a particular finite sample. That example illustrates
a variable-length mechanism; it is not by itself a certificate about every
historical candidate universe.

## How the inquiry actually developed

The role of the human research director was **generating and choosing useful
questions and research pivots** in response to evidence, not simply enforcing
ordinary correctness preconditions.

- **Sept 17, 2026:** Chose the open question in Shomorony et al. among
  mathematical research candidates. Set an adaptive, goal-directed research
  program instead of deciding upfront whether to prove or disprove the claim.
  Began examining the Medvedev–Brudno likelihood and published definitions.
  Examples of early historical GitHub issue evidence:
  [#1](https://github.com/ottojung/assemblyp1/issues/1),
  [#5](https://github.com/ottojung/assemblyp1/issues/5),
  [#7](https://github.com/ottojung/assemblyp1/issues/7).
- **Sept 18–21:** Pursued candidate counterexamples and complementary
  mathematical routes. Ambiguous models forked into exact multinomial,
  binomial approximation, sequence vs molecule, candidate-length and
  bridging interpretations. Strong negative examples encouraged a better
  question: *which changes to hypotheses eliminate the failure?*
  [#21](https://github.com/ottojung/assemblyp1/issues/21),
  [#22](https://github.com/ottojung/assemblyp1/issues/22),
  [#36](https://github.com/ottojung/assemblyp1/issues/36).
- **Sept 21–25:** The positive frontier included oriented same-length
  circulation/spectrum rigidity. Finite-sample failure prompted the distinct
  population model as an explanatory repair; then normalized spectra,
  period/primitivity and P2 led to a nontrivial uniqueness problem.
  The user directed the formalization toward actual full target statements,
  not merely proxy implications.
  [#45](https://github.com/ottojung/assemblyp1/issues/45),
  [#82](https://github.com/ottojung/assemblyp1/issues/82),
  [#83](https://github.com/ottojung/assemblyp1/issues/83),
  [#87](https://github.com/ottojung/assemblyp1/issues/87),
  [#89](https://github.com/ottojung/assemblyp1/issues/89).
- **Oct 9–12:** The agenda expanded from settling interpretations of the
  2016 question to a coherent theory of finite Bayesian/ML inference:
  distinguish conditional structural guarantees from unconditional ML,
  seek necessary/sufficient conditions and finite recovery criteria,
  understand whether more observations improve recovery, bound error decay,
  compare algorithms' read requirements for 99% recovery under the same
  sampling model. This is a proposed ongoing frontier, not a claim that all
  those questions are solved. Repo modules and notes:
  AssemblyP1/FiniteBayesDecision.lean; project tasks #269–#281.

The research method was already agentic at the founding. The presentation must not mistake the background obligation to check a
mathematical claim for the principal intellectual contribution. The
story is about asking better questions.

## Research method: present from the beginning

The multi-agent method was part of AssemblyP1 **on September 17**, not a response to later difficulty. The original [intent records](../docs/intent-records/project.md) require both a faithful research target and cooperating AI agents, adaptive orchestration, durable research artifacts, and Lean formal verification.

Two aims were intertwined from the outset: **solve a genuine mathematical question** and **conduct the investigation through human-directed AI research**. The user chiefly chose promising questions and changed the frontier when new discoveries suggested a better direction.

Different agents explored literature interpretation, counterexample search, positive mathematical proofs, computation, and formal verification. They produced durable evidence in separate branches and worktrees. The value was independent *exploration* rather than agent consensus.

The orchestrator was part of that research method from its founding. Antonina maintained questions and dependencies; Lubko ran work in isolated environments; the orchestrator dispatched parallelizable work and replenished tasks; pull requests and CI preserved reviewed outcomes. The loop continued across work sessions, while the user supplied and changed the intellectual direction.

Lean provides the distinct **proof trust boundary**. A theorem is a formal statement; a proof term is checked by a small kernel, regardless of the source that generated it. CI also replays modules and audits axioms. Lean cannot determine whether a theorem statement reflects the intended biological model, so primary-source interpretation remains separate.

**Original problem status:** The [finite interpretation matrix](../docs/source-notes/interpretation-matrix-217.md) records a resolved classification of all determinate source-supported readings of the 2016 bridging-to-ML question. Restricted positive theorems and broader negative counterexamples have been proved. The historical sentence did not select one likelihood objective, so resolution meant settling its concrete readings rather than pretending the original question remains unsolved. Unresolved newer problems should not be confused with the already settled finite question.

This is not a story comparing AI tools. It is the story of a research method designed at founding, how mathematical discoveries repeatedly changed its direction, and what it accomplished.

## Sources for presenter notes

- Shomorony, Kim, Courtade and Tse (2016), *Information-optimal genome assembly
  via sparse read-overlap graphs*:
  https://doi.org/10.1093/bioinformatics/btw450
  The Not-So-Greedy guarantee and the ML question in Discussion.
- Medvedev and Brudno (2009), *Maximum likelihood genome assembly*:
  https://doi.org/10.1089/cmb.2009.0047
  The likelihood alternative to shortest compatible sequence.
- MIT 6.011, Chapter 13, section 13.2.1, Bayesian hypothesis testing:
  https://ocw.mit.edu/courses/6-011-introduction-to-communication-control-and-signal-processing-spring-2010/
  MAP minimizes conditional and average 0-1 error.
- Lean Language Reference, Elaboration and Compilation / The Kernel:
  https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/
- AssemblyP1 internal: docs/research-orchestration.md,
  docs/skills/research-orchestrator.md,
  docs/maximum-likelihood-models-for-genome-assembly.md,
  paper/sections/04-finite-results.tex,
  paper/sections/05-population.tex,
  AssemblyP1/FiniteBayesDecision.lean.

## Editorial guards

- Preserve the original opening three slides; explain overlaps and bridging
  before moving to probability.
- Explain **posterior genome probability** via Bayes, not just read likelihood.
- State exact MAP optimality and uniform-prior ML relation *before*
  introducing the 2016 conjecture.
- Present the antecedent as **Not-So-Greedy's success conditions** and
  consequent as **true genome is an ML maximizer**.
- Do not celebrate checking assumptions as a major research direction.
- Keep the audience-facing content as accessible to ordinary programmers,
  without irrelevant graph vocabulary or arbitrary code decorations.
- Do not inject population likelihood into the finite story; explain
  it as a separate model only when motivated.
- For a research talk, explain who chooses questions, who explores,
  what persists, and what the kernel checks.


## Editorial correction: the 2016 negative result and conditional Bayes

The 2016 question is an ordinary non-Bayesian CONDITIONAL IMPLICATION: if the
observed reads satisfy information feasibility for the true genome, must
that genome maximize the UNCONDITIONED likelihood of the observed reads?
The substantive answer is **NO**, established by the strict W5 molecule
counterexample AAATAT versus AAAAAT, and other source-supported witnesses.
Do not frame the audience-facing answer as model-dependent or suggest the
question is still open.

The counterexample does NOT show maximum likelihood is a statistically
inferior algorithm. Ordinary ML is optimized on a broader candidate task
than the truth-conditional Not-So-Greedy success guarantee. In the W5
example, the competitor is allowed by the ordinary likelihood/candidate
formulation but fails I_s for the witnessed placements.

We separately studied **conditional Bayesian inference** to recover
optimality under the actual structural promise. The joint law of genome,
reads, and the event E must be conditioned, rather than simply reusing
ordinary likelihood. Under the original read-only unique-reconstruction
guarantee F(g,r) => A(r) equivalent to g, the possible feasible true
genomes for the same observed read strings are one equivalence class.
Conditional posterior mass on that class is one; conditional MAP is
correct and optimal for the conditioned experiment. E is truth-dependent
and extra side information, not determined by reads alone. This is a
corollary of the published deterministic guarantee with an external NSG
premise, and the consequences are checked in
AssemblyP1/ConditionalIdentifiability.lean.

Do not overextend this conditional result to arbitrary placement-based
predicates or reverse-complement molecule variants: certain W3/W6
counterexamples satisfy the differently defined placement feasibility.
Failing a specific placement test does not automatically make the entire
marginalized P(R,E | D) equal to zero. Presenter notes must keep the event,
observations, and model conventions consistent.

The oriented same-length restricted positive result and the primitive-P2
population uniqueness theorem are independent discoveries, not
qualifications of the negative original answer. The later population
model was motivated by the research director hypothesizing finite-sample
noise, not by uncertainty about the already negative finite answer.

Primary internal sources: docs/issue266-conditional-identifiability.md,
docs/audit-267-finite-ml-vs-conditional-bayes.md,
docs/bayes-optimality-conditional-feasibility-267.md,
paper/sections/03-open-question.tex.
