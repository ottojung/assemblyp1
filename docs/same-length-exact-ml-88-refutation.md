# #88 settled: the oriented same-length exact ML claim is false, with a kernel-checked refutation

This note records the outcome of issue #88. The target theorem — *information
feasibility `I_s` implies the true sequence is a maximum-likelihood sequence* —
is **false** for the oriented same-length exact Medvedev–Brudno objective, and
the refutation is kernel-checked in
`AssemblyP1/SameLengthExactMLCounterexample.lean`. The §6.2 support-spelled
candidate restriction does **not** rescue it: the counterexample competitor
satisfies the literal merged predicate
`AssemblyP1.Section62Flow.SpelledFeasible62` (issue #100) in strict oriented
single-strand mode.

Everything below is kernel-checked. There is no `sorry`, no `admit`, no
`native_decide`, and no new axiom: `AssemblyP1.lean` carries a `#print axioms`
audit, and every theorem listed there depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## 1. The exported refutation theorem

`AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`
is the single theorem that carries all four required components at once:

```lean
InformationFeasible truthGenome 2 readStarts ∧
  competitorGenome.len = truthGenome.len ∧
  Section62Flow.SpelledFeasible62 Base W strandToList idRep idRc 2 1
    observedVerts competitorSpelling walkFlow
    (Section62Flow.noTerminals W) candidateThroughput ∧
  ¬ Is62MaximumLikelihood truthGenome competitorGenome 2 realizedReads ∧
  ¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads
```

Read conjunct by conjunct:

1. **Full source-faithful `I_s`.** `truth_information_feasible` is a single
   `decide` on `SourceFaithfulIs.InformationFeasible` itself, over every
   admissible repeat length and every selection of starts. No clause is assumed
   and no weakened stand-in is substituted.
2. **Same genome length.** `competitorGenome.len = truthGenome.len = 4`, by
   `rfl`. The competitor is not longer than the truth, which is the case the
   pre-existing `AssemblyP1.ExactVariantECounterexample` does *not* cover.
3. **The literal §6.2 predicate.** `competitor_spelledFeasible62` discharges all
   five conjuncts of `SpelledFeasible62` in strict oriented single-strand mode
   (`idRep` and `idRc` both the identity: no reverse-complement collapse). The
   overlap graph is the *actual* `overlapEdges` on the observed reads `AB` and
   `BA`; the circuit is the real cyclic walk `AB → BA → AB → BA` of the
   competitor; and the flow is the walk's own certificate.
4. **Objective failure.** `competitor_likelihood = 1/4` against
   `truth_likelihood = 1/16`.

## 2. The instance

Alphabet `{A, B}`, circular genome of length `4`, read length `L = 2`.

```
truth      :  A  A  B  B          candidate :  A  B  A  B
positions    0  1  2  3                     0  1  2  3
```

The truth's four length-`2` windows are `AA, AB, BB, BA` (at starts `0,1,2,3`).

**The realization.** Two reads: the placement at start `1` returns `AB`, the
placement at start `3` returns `BA`. The two distinct latent starts are
therefore `{1, 3}`, and that `Finset` is exactly what is handed to
`InformationFeasible`. `realized_reads` records the coupling by `decide`, and
`realizedReads = [observedAB, observedBA]` is the multiset the objective
consumes. This matters: the hypothesis and the observation are built from *one*
realization, not from two unrelated configurations.

**Why `I_s` holds.** Clause 1 (`Covers`) is satisfied and is the only
non-vacuous clause: the read at start `1` covers `{1,2}` and the read at start
`3` covers `{3,0}`, so together they cover all four positions. The truth has no
*triple* repeat at any length `1 ≤ e < 4` (the `A` positions are `{0,1}` and the
`B` positions are `{2,3}`), so clause 2 is vacuous; and the only two repeats, at
starts `(0,1)` and `(2,3)`, do not interleave, so clause 3 is vacuous. All of
this is a *conclusion* of the computation, not an assumption.

**The competitor.** `ABAB` has windows `AB, BA, AB, BA`, so it spells each
observed read type twice.

**The arithmetic.** With the observation-only multinomial coefficient divided
out (it is `2!/1!1! = 2`, a positive constant independent of the candidate, so
reinserting it cannot move a maximizer):

```
truth      = (1/4)^1 · (1/4)^1 = 1/16
competitor = (2/4)^1 · (2/4)^1 = 1/4   >   1/16
```

## 3. The §6.2 acceptance boundary, and exactly where it fails

The predicate `SpelledFeasible62` requires (i) every visited vertex to be an
observed read molecule, (ii) every step to be an edge of the §6.2 overlap graph,
(iii) every step to survive the transitive edge reduction, (iv) the walk to be a
bidirected circuit, and (v) an explicit feasible §6.2 flow with zero terminal
usage. The competitor satisfies all five:

| conjunct | why |
| --- | --- |
| `VisitsObserved` | the walk visits only `AB` and `BA`, the observed reads |
| `StepsInGraph` | `AB → BA` and `BA → AB` are genuine length-`1` overlaps (`sufOf [A,B] 1 = [B] = preOf [B,A] 1`) |
| `StepsSurviveReduction` | vacuous: a step has length `1`, and the reduction needs a *strictly shorter positive* overlap |
| `BidirectedCircuit` | in strict single-strand mode `sgnX = 1` and `sgnY = -1`, so `sgnX (step i) = -sgnY (step i-1)` always |
| `Feasible62` | the walk flow is `2` on each of the two step types; throughput `8` at each vertex; signed balance `8 - 8 = 0`; no terminals |

In strict mode `strandsOf rc verts = verts ++ verts.map id` enumerates each class
twice, so `overlapGraph` carries four copies of each step type and the throughput
is `4 · 2 = 8`. `candidateThroughput` supplies `d` to match, as the predicate's
`d` argument intends.

**Where the boundary actually is.** The observation is that the restriction is
*not* symmetric. The truth `AABB` has windows `AA` and `BB` that were never
observed, so the truth itself is **not** a §6.2-feasible candidate
(`truth_not_spelled_on_observed`). Clause 1 of `I_s` is only *position*
coverage; full length-`L` window coverage is strictly stronger, and `I_s` does
not provide it. So the §6.2 class can simultaneously

* contain a genuine same-length competitor that beats the truth, and
* exclude the truth itself.

A maximizer statement over that class therefore has to be phrased as "every
feasible same-length competitor has likelihood at most the truth's", which is
`Is62MaximumLikelihood` — and that is exactly what
`section62_maxLikelihood_refuted` refutes.

The two positive statements that remain true are recorded separately and are
*not* claimed to be refuted here:

* over the **support-equality** (spelled-circuit) candidate class,
  `AssemblyP1.OrientedSameLengthML.same_length_exactLik_maximizer` holds under
  the no-long-triple-repeat premise — the counterexample's competitor has a
  strictly smaller window support, so it is outside that class;
* `AssemblyP1.OrientedSameLengthML.covering_constant_reads_is_constant`: if every
  realized read returns the same symbol and the realized starts cover the
  genome, the genome is that constant word, so the truth spells all of its
  windows and attains the maximum objective value `1`. This rules out the whole
  family of apparent counterexamples that concentrate on a single read type,
  for every read length and every alphabet.

## 4. Cross-check of the two independently reported witnesses

Both were re-checked here against the realization semantics, independently of the
reporting agent.

**Witness A — truth `AAATAT`, `G = 6`, `L = 3`, reads `AAA, AAA, AAT`,
competitor `AAAAAT`, likelihood ratio 9.** The arithmetic is correct
(`d_S(AAA) = 1`, `d_D(AAA) = 3`, `d_S(AAT) = d_D(AAT) = 1`, so the ratio is
`3² = 9`). But the coupling fails: `AAA` occurs only at start `0` and `AAT` only
at start `1`, so the realized start set is forced to be `{0, 1}`, which does
**not** cover — positions `4` and `5` are uncovered by length-`3` reads at
starts `0, 1`. `InformationFeasible` is therefore `False` at the forced start
set; it is `True` only for `R = {0,…,5}`, which is not the realized start set.
Independently of that, the competitor is also outside the §6.2 class: its
length-`3` windows include `010` and `100`, which were never observed. So this
witness is evidence for the *unrestricted* claim but not a valid `I_s` instance
and not a §6.2-feasible candidate.

**Witness B — the "all-zero competitor" family.** This family is impossible, and
the obstruction is a theorem rather than a search result: if every realized read
returns the constant word `0^L` and the realized starts cover the genome, then
the genome is `0^G`, so `d_S(0^L) = G` and the truth already attains likelihood
`1`. Clause 1 of `I_s` alone forbids `0 < |{starts with 0^L window}| < G` together
with coverage. Exhaustive enumeration over binary genomes for `G ≤ 14` found
`110461` configurations with `0 < |Z| < G` and **zero** of them covering. This
is `AssemblyP1.OrientedSameLengthML.covering_constant_reads_is_constant` in
Lean.

**Correction to an earlier claim in this branch.** An earlier version of the
computational harness in this worktree keyed the observation `x` by the
spectrum *count* rather than by the read-type word, so every observation was
malformed, the truth's likelihood was always `0`, and the search reported "0
counterexamples" vacuously. Those earlier results are void; the numbers quoted
here come from the corrected harness, which compares a non-degenerate truth
likelihood on every observation.

## 5. The bridging bridge: why the old proof route was blocked anyway

Independently of the counterexample, the intended route to a *positive* theorem
was blocked, and `AssemblyP1/BridgingBridge.lean` records the exact reason. The
previously external "Fact D" claimed that a length-`L` read bridges a repeat copy
only if the copy has length `≤ L - 2`, so that `I_s` forbids long Bresler triple
repeats. That is **false**, because a read can bridge a copy by going the other
way around the circle.

`bridgingLength` is the sharp, kernel-checked replacement:

```lean
BridgesCopy S L R e t  →  e + 2 ≤ L  ∨  S.len - e ≤ L
```

* the first disjunct is the intended straddling mode: the read covers a base
  before `t - 1` and a base after `t + e`, so it spans `≥ e + 2` bases;
* the second is the **wraparound mode**: the read covers the whole *complement*
  arc `[t + e, t - 1]` of length `S.len - e`, which a read of length `L` can do
  whenever `S.len - e ≤ L`.

Consequently `informationFeasible_tripleRepeat_ge_G_sub_L` gives the sharp
statement: if `R ∈ I_s`, `2 ≤ L ≤ S.len`, and the truth carries a triple repeat
of length `e ≥ L - 1`, then `S.len - L ≤ e`. So `I_s` forbids exactly the long
triple repeats whose complement arc is longer than a read, and leaves the
wraparound regime `max (L - 1) (S.len - L) ≤ e < S.len` unresolved. An
exhaustive search over binary genomes for `G ≤ 9` found `23956` instances of full
`InformationFeasible` together with `HasLongTripleRepeat`, all in that regime.

`informationFeasible_sharp_no_long_triple_repeat` is the honest replacement: it
discharges `¬ HasLongTripleRepeat` from `InformationFeasible` plus the explicit
nondegeneracy hypothesis `SharpNoLongTripleRepeat`, which is the weakest
condition under which the rigidity chain can be run. It is consumed by the
positive theorem `informationFeasible_exactLik_maximizer`, which is preserved
separately and is **not** refuted by §1, because it ranges over the
support-equality candidate class.

Note that `I_s → ¬ HasLongTripleRepeat` is *not* asserted anywhere in this
branch. It is false, and the wraparound counterexample is recorded in
`docs/oriented-same-length-ml-88.md` §"Fact D".

## 6. Exact theorem surface

Refutations (all kernel-checked, `AssemblyP1/SameLengthExactMLCounterexample.lean`):

| theorem | content |
| --- | --- |
| `truth_information_feasible` | full source-faithful `I_s`, by `decide` |
| `realized_reads` | the coupling between the start set and the observation |
| `truth_no_long_triple_repeat` | the truth has no long triple repeat, so §1 is not a wraparound artifact |
| `competitor_spelledFeasible62` | the literal §6.2 predicate, all five conjuncts |
| `section62_maxLikelihood_refuted` | `¬ Is62MaximumLikelihood truth candidate` |
| `truth_not_maximum_likelihood` | `¬ IsSameLengthMaximumLikelihood truth`, i.e. the unrestricted same-length claim also fails |
| `same_length_exact_ML_refutation_62` | **the single exported refutation** |
| `truth_not_spelled_on_observed`, `competitor_spelled_on_observed`, `acceptance_boundary` | the precise §6.2 boundary condition |

Positive results preserved separately:

| theorem | content |
| --- | --- |
| `BridgingBridge.bridgingLength` | the sharp bridging-length dichotomy |
| `BridgingBridge.informationFeasible_tripleRepeat_ge_G_sub_L` | `I_s` bounds long triple-repeat lengths from below by `G - L` |
| `BridgingBridge.informationFeasible_sharp_no_long_triple_repeat` | `I_s` + nondegeneracy ⟹ no long triple repeat |
| `OrientedSameLengthML.informationFeasible_exactLik_maximizer` | **the preserved positive partial theorem**: full `I_s` + a genuine realization + nondegeneracy ⟹ exact ML maximizer over the support-equality class |
| `OrientedSameLengthML.covering_constant_reads_is_constant` | covering constant reads force a constant genome, hence a maximizer |
| `OrientedSameLengthML.truth_is_spelled_candidate_of_realization` | the realization layer; removes the former `hobs` premise |

## 7. What would still be open

* The same-length claim restricted to the **support-equality** candidate class is
  still open modulo the wraparound regime, and is exactly
  `informationFeasible_exactLik_maximizer` plus the characterization in §5.
* An `I_s`-derived replacement for the wraparound regime — e.g. a theorem that
  wraparound-bridged long triple repeats are themselves impossible, or that they
  still force spectrum rigidity — is not formalized. §1 shows this is no longer
  urgent for the ML claim, but it is the natural next repeat-theoretic question.
* Whether the published 2016 sentence was intended with *any* support-based
  candidate restriction at all remains an interpretation question; §3 shows that
  the natural §6.2 restriction, read as "candidates live on the observed read
  types", is satisfied by the counterexample and therefore does not change the
  answer.
