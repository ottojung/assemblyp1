# Issue 272: source-faithful bridge findings (partial)

## Scope and model alignment

The local source-faithful condition in `AssemblyP1.SourceFaithfulIs` is a
property of a circular truth and an exact realized start set. It is not a
posterior statement. `SameLength62Maximizer.informationFeasible_62_maximizer`
and `OrientedSameLengthML.informationFeasible_exactLik_maximizer` conclude an
exact likelihood *maximizer* over the literal same-length spelled-candidate
class, with a certificate for the truth and the candidate. Maximizer does not
mean unique maximizer. Rotation is the equivalence used for circular genomes.
Thus no posterior-singleton corollary follows merely from that endpoint: even
truth-ML plus positive prior and likelihood leaves all tied alternatives in the
posterior support. A prior can resolve some ties, but positive prior on two tied
orbits cannot.

The primary source is Shomorony et al., “The Unobservable Genome,” IEEE/ACM
Transactions on Computational Biology and Bioinformatics 13(4), 2016,
DOI 10.1109/TCBB.2015.2478463. Its repeat-bridging information condition is a
sufficient reconstruction result in its stated random-read model; its
information-theoretic obstructions are necessary impossibility results in
that model. They are not automatically an iff for finite-sample Bayesian
posterior certainty. That transfer requires aligning read length, genome
length, orientation, read multiplicities, candidate class and the event
conditioning law. This note does not claim that alignment or import either
historical theorem as a Lean theorem.

## Exact logical bridge

For a fixed positive-probability read observation `r`, let `C(r)` be the
candidate rotation-orbits with positive prior and positive likelihood. If the
truth is known to satisfy a supplied predicate `I_s(g,r)` and conditioning is
performed on that event, the posterior support is exactly
`{[g] in C(r) | I_s(g,r)}`. Consequently it is a singleton precisely when
exactly one supported orbit satisfies `I_s`. This follows directly from
Bayes' formula; it does not assert that `I_s` is observable from reads, nor
that the sampler supplied it. In particular, truth-only feasibility
`I_s(g_true,r)` is not enough: a competing orbit can also satisfy the same
predicate.

Accordingly the safe implication table is:

| Assumption | Established conclusion | Posterior singleton? |
|---|---|---|
| Source-faithful `I_s` on truth at realized starts | Historical-condition hypothesis, in project model | Not implied |
| `I_s` plus exact §6.2 candidate certificates | Truth is an exact ML maximizer (Lean theorem named above) | Not implied without eliminating every supported competing orbit |
| Supplied event `I_s(g,r)` and exactly one positive-prior, positive-likelihood orbit remains in its fibre | Conditional finite posterior is singleton | Yes, by finite Bayes support characterization |

This rules out using truth feasibility alone as the bridge. A concrete exact
counterexample matching the same orientation, read-multiplicity and candidate
universe remains to be checked before elevating the failure to a
Lean-checked AssemblyP1 example.

## Remaining concrete work

Inspect the 2016 theorem's precise finite/infinite sampling and candidate
universe clauses against `SourceFaithfulIs`, `FiniteBayesDecision`, and
`FiniteSideInformationColoring`. Then construct a smallest finite read
experiment with two non-rotation same-length candidates, exact observed read
multiset, and both candidates satisfying the same source-defined promise (or
prove that such an example is impossible under the exact predicate). Kernel
check that enumeration and compare it with the historical theorem hypotheses.
Until then the implication between source-faithful `I_s` and posterior
singleton remains open at the requested source-faithful bridge level.
