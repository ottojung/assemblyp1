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

The presentation must not mistake the background obligation to check a
mathematical claim for the principal intellectual contribution. The
story is about asking better questions.

## Why agents, why orchestration, why Lean

**One tool-using chatbot** is useful but tied to one conversational trajectory.
Multiple agents can pursue genuinely different hypotheses concurrently, use
their own tools and worktrees, and leave durable traces. Their answers do not
gain credibility from numerical consensus.

**Persistent orchestration** (Antonina board, Lubko, Git branches/worktrees,
GitHub PRs and CI) turns those investigations into a loop: choose research
frontier → dispatch independent packets → run experiments or proof attempts →
reconcile outcomes → merge credible artifacts → generate the next frontier.
A worker can stop or fail without erasing the state. The human research
director changes the questions as evidence accumulates. The system's
scheduling and recovery are engineering, not scientific guarantees.

**Lean** makes a theorem statement a formal type and a proof an object whose
validity is checked by a small kernel. High-level tactics and AI may generate
proof objects, but errors in their reasoning do not by themselves allow a
false proof past the kernel. AssemblyP1 also audits axioms and replays Lean
modules in CI. The kernel proves consequences of formal definitions; it
does not validate by itself whether the definitions faithfully represent
the biological/scientific question.

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
