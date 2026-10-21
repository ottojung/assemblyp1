# §6.2 transitive reduction: exhaustive dependent-classification matrix (#284, requirement 6)

**Status:** mechanical, reproducible audit. This note classifies **every**
`AssemblyP1/*.lean` theorem or proof that depends on the old literal predicate
`Section62Flow.isReducibleB` (and on its downstream abbreviations
`isReducible`, `transitivelyReduced`, `ReductionVacuous`,
`StepsSurviveReduction`, `SpelledFeasible62`). It uses the exact three-way
taxonomy required by issue #284 requirement (6):

* **SURVIVES** — the conclusion is still true, and is either unchanged or has a
  kernel-checked corrected analogue;
* **MUST-BE-REPROVED** — the conclusion used the old predicate's (non)vacuity
  in an essential way and fails, or needs a new proof, under the corrected
  reduction;
* **ALREADY-SUPERSEDED** — the object was the old predicate itself (or a fact
  about it); it is retained as the audited model but is replaced as the
  operative reduction.

The mechanical scanner is
[`scripts/verify_284_reduction_survival_matrix.py`](../scripts/verify_284_reduction_survival_matrix.py),
run by CI. The earlier prose reevaluation is
[section62-reduction-dependent-reevaluation-284.md](section62-reduction-dependent-reevaluation-284.md);
this note is the exhaustive, file:line-backed companion.

<!-- survival-matrix:dependents-start -->
Section62BridgingCounterexample
SameLengthSection62Counterexample
PerOccurrenceSameLengthCounterexample
SameLengthSection62Parametric
HistoricalCoverageSameLengthWitnesses
SameLengthExactMLCounterexample
SameLength62TieUniqueness
SameLength62Maximizer
Section62VariableOverlap247e
Section62NonSpelledFlow
MLEscape
Primitive62Uniqueness
AcgtWitness211
SameLength62NonprimitiveRotation
SameLength62Uniqueness
<!-- survival-matrix:dependents-end -->

## The two predicates

| predicate | file:line | status |
|---|---|---|
| `Section62Flow.isReducibleB` / `isReducible` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):182, :197 | preserved unchanged as the audited model (requirement 1); kernel-proved vacuous on every proper-overlap edge by [../AssemblyP1/Section62ReductionVacuityAudit.lean](../AssemblyP1/Section62ReductionVacuityAudit.lean):23 |
| `Section62Flow.transitivelyReduced` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):223 | preserved; identity on any proper-overlap edge list ([../AssemblyP1/Section62ReductionVacuityAudit.lean](../AssemblyP1/Section62ReductionVacuityAudit.lean):41) |
| `Section62Flow.ReductionVacuous` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):236 | preserved; the corrected analogue is the per-witness `…_graph_spelling_reduction_eq_self` identity |
| `Section62Flow.StepsSurviveReduction` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):480 | preserved; corrected analogue `Section62ReductionWitnessAudit.StepsSurviveReductionSpelling` (:71) |
| `Section62Flow.SpelledFeasible62` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):501 | preserved; corrected analogue `Section62ReductionWitnessAudit.SpelledFeasible62Spelling` (:82) |
| `Section62SpellingReductionCandidate.isReducibleSpellingB` / `transitivelyReducedSpelling` | [../AssemblyP1/Section62SpellingReductionCandidate.lean](../AssemblyP1/Section62SpellingReductionCandidate.lean):181, :200 | **the corrected spelling-preserving reduction**: genuine suffix/prefix overlaps through an observed intermediate strand, proper legs, composition law `l₁ + l₂ = readLen + e.len`, same spelled word by `spellPath_eq_spellDirect` (:133); legs forced longer by `replacement_overlaps_longer` (:261) |

The literal predicate demands both replacement overlaps *shorter* than the
direct edge **and** `l₁ + l₂ − readLen = e.len`. For proper equal-length reads
those are arithmetically incompatible, so the old reduction is the identity.
Every statement below that says "these walk steps survive the reduction"
therefore had, under the old predicate, the real content "these walk steps lie
on the unreduced `overlapEdges` graph".

## Classification summary

| category | files | verdict |
|---|---|---|
| definition site (old model) | 1 | ALREADY-SUPERSEDED as the operative reduction; retained as the audited model |
| direct genuine dependent (statement/proof references an old identifier) | 10 | **all SURVIVES** |
| transitive dependent (reaches the old predicate only through `Is62Candidate62`) | 5 | **all SURVIVES** |
| old-model behavior audit | 1 | SURVIVES (facts about the old predicate) |
| unrelated local `SpelledFeasible62` | 2 | not dependents (own definition) |
| non-dependent references to the old model | 6 | not dependents (prose-only or corrected-model modules) |

There are **0 MUST-BE-REPROVED** rows.

## Table 1 — old-model definition sites

| symbol | file:line | verdict |
|---|---|---|
| `isReducibleB`, `isReducible`, `transitivelyReduced`, `ReductionVacuous`, `StepsSurviveReduction`, `SpelledFeasible62` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean):182, :197, :223, :236, :480, :501 | **ALREADY-SUPERSEDED** as the operative reduction; **preserved unchanged** as the audited model (requirement 1). Replacement: `isReducibleSpellingB` / `transitivelyReducedSpelling` / `StepsSurviveReductionSpelling` / `SpelledFeasible62Spelling`. |

## Table 2 — direct genuine dependents

Every row's evidence line contains the old identifier that makes the theorem a
dependent. All verdicts are SURVIVES.

<!-- survival-matrix:genuine-start -->
| dependent (module.symbol) | evidence file:line | what it concludes | verdict | corrected replacement / kernel bridge |
|---|---|---|---|---|
| `Section62BridgingCounterexample.truth_steps_survive_reduction` | [../AssemblyP1/Section62BridgingCounterexample.lean](../AssemblyP1/Section62BridgingCounterexample.lean):726 | truth steps survive | SURVIVES | `bridging_truth_steps_survive_spelling` ([WitnessAudit:159](../AssemblyP1/Section62ReductionWitnessAudit.lean)) |
| `Section62BridgingCounterexample.competitor_steps_survive_reduction` | :732 | competitor steps survive | SURVIVES | `bridging_competitor_steps_survive_spelling` (:167) |
| `Section62BridgingCounterexample.truth_spelled_feasible62` | :755 | literal §6.2 spelled candidate | SURVIVES | `bridging_truth_spelled_feasible62_spelling` (:176) |
| `Section62BridgingCounterexample.competitor_spelled_feasible62` | :762 | literal §6.2 spelled candidate | SURVIVES | `bridging_competitor_spelled_feasible62_spelling` (:186) |
| `Section62BridgingCounterexample.graph_reduction_vacuous` | :810 | old reduction is identity | SURVIVES | `bridging_graph_spelling_reduction_eq_self` (:146) |
| `Section62BridgingCounterexample.se62_bridging_bidirected_flow_counterexample` | :895 | the counterexample | SURVIVES | general `spelledFeasible62_old_implies_spelling` ([WitnessAudit:108](../AssemblyP1/Section62ReductionWitnessAudit.lean)) |
| `SameLengthSection62Counterexample.truth_steps_survive_reduction` | [../AssemblyP1/SameLengthSection62Counterexample.lean](../AssemblyP1/SameLengthSection62Counterexample.lean):772 | truth steps survive | SURVIVES | `sameLength_truth_steps_survive_spelling` ([WitnessAudit:216](../AssemblyP1/Section62ReductionWitnessAudit.lean)) |
| `SameLengthSection62Counterexample.competitor_steps_survive_reduction` | :778 | competitor steps survive | SURVIVES | `sameLength_competitor_steps_survive_spelling` (:224) |
| `SameLengthSection62Counterexample.truth_spelled_feasible62` | :795 | literal §6.2 spelled candidate | SURVIVES | `sameLength_truth_spelled_feasible62_spelling` (:232) |
| `SameLengthSection62Counterexample.competitor_spelled_feasible62` | :802 | literal §6.2 spelled candidate | SURVIVES | `sameLength_competitor_spelled_feasible62_spelling` (:242) |
| `SameLengthSection62Counterexample.graph_reduction_vacuous` | :836 | old reduction is identity | SURVIVES | `sameLength_graph_spelling_reduction_eq_self` (:204) |
| `SameLengthSection62Counterexample.samelength_se62_bidirected_flow_counterexample` | :921 | the counterexample | SURVIVES | general transfer |
| `SameLengthSection62Counterexample.samelength_historical_se62_bidirected_flow_counterexample` | :992 | the counterexample | SURVIVES | general transfer |
| `PerOccurrenceSameLengthCounterexample.truth_steps_survive_reduction` | [../AssemblyP1/PerOccurrenceSameLengthCounterexample.lean](../AssemblyP1/PerOccurrenceSameLengthCounterexample.lean):754 | truth steps survive | SURVIVES | `perOccurrence_truth_steps_survive_spelling` ([WitnessAudit:272](../AssemblyP1/Section62ReductionWitnessAudit.lean)) |
| `PerOccurrenceSameLengthCounterexample.competitor_steps_survive_reduction` | :760 | competitor steps survive | SURVIVES | `perOccurrence_competitor_steps_survive_spelling` (:280) |
| `PerOccurrenceSameLengthCounterexample.truth_spelled_feasible62` | :778 | literal §6.2 spelled candidate | SURVIVES | `perOccurrence_truth_spelled_feasible62_spelling` (:288) |
| `PerOccurrenceSameLengthCounterexample.competitor_spelled_feasible62` | :785 | literal §6.2 spelled candidate | SURVIVES | `perOccurrence_competitor_spelled_feasible62_spelling` (:299) |
| `PerOccurrenceSameLengthCounterexample.graph_reduction_vacuous` | :820 | old reduction is identity | SURVIVES | `perOccurrence_graph_spelling_reduction_eq_self` (:260) |
| `PerOccurrenceSameLengthCounterexample.PerOccurrenceSameLengthMaximality` | :901 | maximality | SURVIVES | general transfer |
| `PerOccurrenceSameLengthCounterexample.peroccurrence_samelength_se62_bidirected_flow_counterexample` | :930 | the counterexample | SURVIVES | general transfer |
| `SameLengthSection62Parametric.parametric_se62_historical_literal_counterexample` | [../AssemblyP1/SameLengthSection62Parametric.lean](../AssemblyP1/SameLengthSection62Parametric.lean):451 | parametric counterexample | SURVIVES | general transfer (imports the same-length witness, readLen 3 / oMin 2) |
| `SameLengthSection62Parametric.parametric_se62_counterexample` | :476 | parametric counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w1_historical_literal_se62_flow_counterexample` | [../AssemblyP1/HistoricalCoverageSameLengthWitnesses.lean](../AssemblyP1/HistoricalCoverageSameLengthWitnesses.lean):357 | historical literal counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.HistoricalSameLengthMaximality` | :374 | maximality | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w1_historical_se62_flow_counterexample` | :391 | counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w1_historical_full_se62_flow_counterexample` | :410 | counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w2_historical_literal_se62_flow_counterexample` | :541 | historical literal counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.HistoricalPerOccurrenceSameLengthMaximality` | :558 | maximality | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w2_historical_se62_flow_counterexample` | :571 | counterexample | SURVIVES | general transfer |
| `HistoricalCoverageSameLengthWitnesses.w2_historical_full_se62_flow_counterexample` | :593 | counterexample | SURVIVES | general transfer |
| `SameLengthExactMLCounterexample.Is62MaximumLikelihood` | [../AssemblyP1/SameLengthExactMLCounterexample.lean](../AssemblyP1/SameLengthExactMLCounterexample.lean):443 | ML maximizer definition (uses `SpelledFeasible62`) | SURVIVES | general transfer |
| `SameLengthExactMLCounterexample.competitor_spelledFeasible62` | :459 | literal §6.2 spelled candidate | SURVIVES | general transfer (readLen 2 / oMin 1 ⇒ full-overlap graph) |
| `SameLengthExactMLCounterexample.section62_maxLikelihood_refuted` | :512 | refutation | SURVIVES | general transfer |
| `SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62` | :523 | refutation | SURVIVES | general transfer |
| `SameLength62TieUniqueness.truth4_spelledFeasible62` | [../AssemblyP1/SameLength62TieUniqueness.lean](../AssemblyP1/SameLength62TieUniqueness.lean):597 | literal §6.2 spelled candidate | SURVIVES | general transfer (readLen 2 / oMin 1 ⇒ full-overlap graph) |
| `SameLength62TieUniqueness.truth4_is62Candidate` | :622 | candidate | SURVIVES | general transfer |
| `SameLength62Maximizer.Is62Candidate62` | [../AssemblyP1/SameLength62Maximizer.lean](../AssemblyP1/SameLength62Maximizer.lean):185 | candidate definition (contains `SpelledFeasible62`) | SURVIVES | general transfer |
| `Section62VariableOverlap247e.edgeAAB_BAB_not_reducibleB` | [../AssemblyP1/Section62VariableOverlap247e.lean](../AssemblyP1/Section62VariableOverlap247e.lean):133 | old predicate is `false` on the length-`1` edge | SURVIVES | audited-model fact; the corrected predicate is `true` here |
| `Section62VariableOverlap247e.D_full_spelled_feasible62` | :278 | literal §6.2 spelled candidate | SURVIVES | general transfer (`fullOverlapMin = 2 = readLen − 1` ⇒ full-overlap graph) |
| `Section62VariableOverlap247e.S_full_spelled_feasible62` | :309 | literal §6.2 spelled candidate | SURVIVES | general transfer |
| `Section62NonSpelledFlow.graph_reduction_vacuous_literal` | [../AssemblyP1/Section62NonSpelledFlow.lean](../AssemblyP1/Section62NonSpelledFlow.lean):584 | old reduction is identity on `graph1` | SURVIVES | audited-model fact; the corrected reduction is nontrivial here |
| `Section62NonSpelledFlow.spelled_subset_general` | :876 | spelled ⊆ general feasible | SURVIVES | unchanged (last conjunct of `SpelledFeasible62` is the same `Feasible62`) |
<!-- survival-matrix:genuine-end -->

## Table 2b — transitive dependents (via `Is62Candidate62`)

`SameLength62Maximizer.Is62Candidate62` (direct dependent, Table 2) is a `Prop`
whose definition contains `Section62Flow.SpelledFeasible62`, hence
`StepsSurviveReduction` and `transitivelyReduced`. Any theorem whose statement
or proof assumes `Is62Candidate62` therefore depends on the old predicate
transitively. All verdicts are SURVIVES, discharged by the same general
transfer (the old `SpelledFeasible62` conjunct inside `Is62Candidate62` lifts to
`SpelledFeasible62Spelling`).

<!-- survival-matrix:transitive-start -->
| dependent (module.symbol) | evidence file:line | transitive carrier | verdict | corrected replacement |
|---|---|---|---|---|
| `MLEscape.Is62SpelledMLMax` (and its uses) | [../AssemblyP1/MLEscape.lean](../AssemblyP1/MLEscape.lean):290 | `Is62Candidate62` | SURVIVES | `Is62Candidate62` with `SpelledFeasible62Spelling` |
| `Primitive62Uniqueness.D_is_genuine` | [../AssemblyP1/Primitive62Uniqueness.lean](../AssemblyP1/Primitive62Uniqueness.lean):246 | `Is62Candidate62` | SURVIVES | same |
| `AcgtWitness211.¬Is62Candidate62` | [../AssemblyP1/AcgtWitness211.lean](../AssemblyP1/AcgtWitness211.lean):86 | `Is62Candidate62` | SURVIVES | same |
| `SameLength62NonprimitiveRotation.…` | [../AssemblyP1/SameLength62NonprimitiveRotation.lean](../AssemblyP1/SameLength62NonprimitiveRotation.lean):93 | `Is62Candidate62` | SURVIVES | same |
| `SameLength62Uniqueness.…` | [../AssemblyP1/SameLength62Uniqueness.lean](../AssemblyP1/SameLength62Uniqueness.lean):111 | `Is62Candidate62` | SURVIVES | same |
<!-- survival-matrix:transitive-end -->

## Table 3 — old-model behavior audits (facts about the old predicate itself)

| object | file:line | verdict |
|---|---|---|
| `Section62ReductionVacuityAudit.shorter_overlaps_cannot_compose` | [../AssemblyP1/Section62ReductionVacuityAudit.lean](../AssemblyP1/Section62ReductionVacuityAudit.lean):16 | **SURVIVES** (fact about the old predicate; used to prove its vacuity) |
| `Section62ReductionVacuityAudit.current_reducible_false_of_proper` | :23 | **SURVIVES** |
| `Section62ReductionVacuityAudit.transitivelyReduced_eq_self_of_proper` | :41 | **SURVIVES** |

## Table 4 — non-dependents that mention the old model

These files mention the old identifiers only in comments or in the corrected
analogue's own definition; none concludes the old predicate.

| file | references | role |
|---|---|---|
| [../AssemblyP1/Section62ReductionDependencyAudit.lean](../AssemblyP1/Section62ReductionDependencyAudit.lean) | prose (:8, :29) | corrected bridge module |
| [../AssemblyP1/Section62ReductionWitnessAudit.lean](../AssemblyP1/Section62ReductionWitnessAudit.lean) | code (transfer argument) + prose | corrected witness audit |
| [../AssemblyP1/Section62VisitTransport.lean](../AssemblyP1/Section62VisitTransport.lean) | prose (:26) | corrected-model diagnostic |
| [../AssemblyP1/Section62VisitWindowBridge.lean](../AssemblyP1/Section62VisitWindowBridge.lean) | prose (:38) | corrected-model bridge |
| [../AssemblyP1/Section62WindowBoxSharpness.lean](../AssemblyP1/Section62WindowBoxSharpness.lean) | prose (:49) | corrected-model sharpness |
| [../AssemblyP1/Section62GlobalCircularAudit.lean](../AssemblyP1/Section62GlobalCircularAudit.lean) | prose (:63) | global corrected replacement |

## Table 5 — unrelated local predicates

| file | local definition | not a dependent of the §6.2 predicate |
|---|---|---|
| [../AssemblyP1/OrientedVariableLengthSe62.lean](../AssemblyP1/OrientedVariableLengthSe62.lean) | own `SpelledFeasible62` (:284) | distinct per-vertex feasibility, no `transitivelyReduced` |
| [../AssemblyP1/ShortFiniteMLCounterexamples.lean](../AssemblyP1/ShortFiniteMLCounterexamples.lean) | own `SpelledFeasible62` (:300) | distinct per-vertex feasibility, no `transitivelyReduced` |

## Why there is no MUST-BE-REPROVED row

The old reduction is the identity on any proper-overlap edge list, so a
dependent's survival conjunct was vacuous: it asserted graph membership, not
reduction survival. The corrected reduction is the identity precisely when every
graph edge is a full overlap `readLen − 1` ([../AssemblyP1/Section62SpellingReductionCandidate.lean](../AssemblyP1/Section62SpellingReductionCandidate.lean):227
`fullOverlap_not_reducible`), because `l₁ + l₂ ≤ 2·readLen − 2 < readLen + (readLen − 1)`
(:220 `omega_strict`). Every direct dependent in Table 2 is either

* a **full-overlap** graph (`readLen = 3`, `oMin = 2` for the bridging,
  same-length, per-occurrence, historical and parametric witnesses; or
  `readLen = 2`, `oMin = 1` for `SameLengthExactMLCounterexample` and
  `SameLength62TieUniqueness`; or `fullOverlapMin = 2` for
  `Section62VariableOverlap247e`), or
* the single **nontrivial** case `Section62NonSpelledFlow.graph1` at `oMin = 1`,
  whose old-predicate identity fact (`graph_reduction_vacuous_literal`) is an
  audited-model fact, while its nontrivial certificates are stated on
  `reducedList` and transferred by
  [../AssemblyP1/Section62ReductionDependencyAudit.lean](../AssemblyP1/Section62ReductionDependencyAudit.lean):103
  `nonspelled_reduction_spelling_eq` (corrected reduction = `reducedList`).

Hence the general kernel bridge
`Section62ReductionWitnessAudit.spelledFeasible62_old_implies_spelling`
([:108](../AssemblyP1/Section62ReductionWitnessAudit.lean)) covers every
`SpelledFeasible62` dependent uniformly, and no dependent conclusion is falsified
or left un-proved. The precise reason there is no MUST-BE-REPROVED row is that
the old predicate was *vacuous*, so no dependent proof used a nontrivial removal.

## Independent finite regression

`scripts/verify_284_reduction_survival_matrix.py` independently re-implements
the two predicates on the concrete
`Section62SpellingReductionCandidate` instance (`regressionGraph`, read length
`3`, `o_min = 1`, three observed molecule classes and their reverse complements)
and asserts:

1. the direct `1`-overlap `0 → 2` and both `2`-overlap legs `0 → 1`, `1 → 2` are
   members of the complete `overlapEdges` graph (9 edges: 5 of length 2, 4 of
   length 1);
2. the old `isReducibleB` is `false` on every edge (vacuous) and in particular
   on the direct edge;
3. the corrected `isReducibleSpellingB` is `true` on the direct edge and
   `false` on both legs;
4. the corrected reduction removes exactly the 4 redundant edges, including the
   direct edge, and keeps both legs;
5. the forced-longer arithmetic `directLen < l₁ ∧ directLen < l₂` holds for the
   witness, and `l₁ + l₂ ≤ 2·readLen − 2 < readLen + (readLen − 1)` holds for
   all proper `l₁, l₂ < readLen` (so no full-overlap edge is reducible).

## Axiom hygiene

Every corrected bridge cited above is Lean-kernel-checked and depends only on
`propext`, `Classical.choice`, and `Quot.sound` (some depend on none); the
`#print axioms` endpoints are listed in
[../AssemblyP1/Section62ReductionWitnessAudit.lean](../AssemblyP1/Section62ReductionWitnessAudit.lean):312
and the root [../AssemblyP1.lean](../AssemblyP1.lean). No `sorry`, `admit`,
`axiom`, or `native_decide` is introduced. The old predicate is unchanged
(requirement 1).

## References

* Medvedev–Brudno, *Maximum Likelihood Genome Assembly* (2009), §3.1–§3.4,
  §6.2, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
* Myers, *The fragment assembly string graph* (2005), §2–§3, Fig. 4,
  <https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>.
