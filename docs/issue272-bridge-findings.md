# Issue 272: source-faithful bridge findings (partial)

_Status: 2026-10-27. Read with the exact posterior characterization in
[`issue272-finite-bayesian-side-information.md`](issue272-finite-bayesian-side-information.md)
and the read-string / obstruction comparisons in
[`issue272-read-string-is-vs-unambiguous.md`](issue272-read-string-is-vs-unambiguous.md)
and [`issue272-bresler-obstruction-gap.md`](issue272-bresler-obstruction-gap.md)._

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

This rules out using truth feasibility alone as the bridge to posterior
certainty. A subtlety is that the local `InformationFeasible` property is
truth-and-start-set dependent; the historical read-string adapter is instead
the supplied event obtained by existentially marginalizing over compatible
placements. These are distinct conditioning questions. For the adapter, the
exact criterion is still: among positive-prior, positive-likelihood candidates
that satisfy that supplied event, exactly one rotation orbit remains. Its
existing Lean theorem `FiniteReadOnlyDecoderCertainty` proves an `I_s`-failure
can coexist with certainty for a read-only decoder (`AAAB`, `L=3`,
`Y={AAA,ABA}`); this disproves necessity for existence of *some* certain
read-only decoder, not necessity for the particular Not-So-Greedy algorithm.

The read-string comparison already supplies the complementary, positive
direction: `ABAB` is `I_s`-feasible at `Y={AB,BA}` but `AABB` in a different
rotation orbit also realizes the read set. This refutes singleton support for
the read-realizable fibre without conditioning on the supplied `I_s` event;
the candidate `AABB` is specifically not `I_s`-feasible there. Thus it does
not refute singleton posterior *after conditioning on* the historical `I_s`
event. The verified decoder-certain `AAAB` witness likewise establishes
read-only recovery in the unconditioned support, not a two-orbit conditioned
`I_s` fibre. A concrete aligned pair satisfying the same source-defined event
on two positive-supported non-rotation candidates remains unestablished.

## Remaining concrete work

1. Align the 2016 random-read event (ordered sample/multiplicities and placement
   sampling) with the project’s literal read-string adapter and candidate
   universe; the source’s reconstruction result cannot be transferred merely
   from the support-only read-set model.
2. Decide whether source `I_s` is sufficient for posterior singleton under the
   *supplied-event conditioning law*, separately from its external decoder
   guarantee and from its local exact-start-set likelihood-maximizer theorem.
   Search for two different-orbit positive-supported candidates in the same
   conditioned `I_s` fibre, or prove that the historical theorem excludes
   them under fully aligned assumptions.
3. Keep algorithm-specific necessity for the literal 2016 Not-So-Greedy
   decoder open; the existing `AAAB` counterexample only concerns whether some
   read-only decoder can be certain.

No new source-faithful counterexample is claimed here. The checked artifacts
remain the existing kernel proofs: generic posterior iff, exact ML maximizer
endpoints, read-string `I_s`/unambiguous incomparability, the `I_s`-not-necessary
read-only certainty example, and the attributed Bresler obstruction comparison.
