# §6.2 transitive reduction: dependent-conclusion reevaluation (#284)

**Status:** kernel-checked dependency audit. This note records, for issue #284
requirement (6), exactly which existing §6.2 conclusions referenced the old
literal predicate `Section62Flow.transitivelyReduced` and whether each survives
under the corrected spelling-preserving reduction
`Section62SpellingReductionCandidate.transitivelyReducedSpelling`. It adds no
new mathematical claim beyond the modules it cites and changes no existing
symbol.

## The two predicates

| predicate | file | status |
|---|---|---|
| `Section62Flow.isReducibleB` / `transitivelyReduced` | [../AssemblyP1/Section62BidirectedFlow.lean](../AssemblyP1/Section62BidirectedFlow.lean) | preserved unchanged as the audited model; kernel-proved vacuous on every proper-overlap edge by [../AssemblyP1/Section62ReductionVacuityAudit.lean](../AssemblyP1/Section62ReductionVacuityAudit.lean) |
| `Section62SpellingReductionCandidate.isReducibleSpellingB` / `transitivelyReducedSpelling` | [../AssemblyP1/Section62SpellingReductionCandidate.lean](../AssemblyP1/Section62SpellingReductionCandidate.lean) | the corrected two-edge spelling-preserving reduction: genuine suffix/prefix overlaps through an observed intermediate strand, proper legs, composition law `l₁ + l₂ = readLen + e.len`, same spelled word by `spellPath_eq_spellDirect`; legs forced longer by `replacement_overlaps_longer` |

The literal predicate demands both replacement overlaps *shorter* than the direct
edge **and** `l₁ + l₂ − readLen = e.len`; for proper equal-length reads those are
arithmetically incompatible, so `transitivelyReduced` is the identity. Every
statement below that says "these walk steps survive the transitive reduction"
therefore had, under the old predicate, the real content "these walk steps lie on
the unreduced `overlapEdges` graph".

## Dependents of the old predicate and their verdicts

| dependent | uses old predicate as | verdict | kernel bridge |
|---|---|---|---|
| `Section62BridgingCounterexample.truth_steps_survive_reduction`, `.competitor_steps_survive_reduction`, `.truth_spelled_feasible62`, `.competitor_spelled_feasible62` | `StepsSurviveReduction` / `SpelledFeasible62` | **survives verbatim** (`oMin = readLen − 1 = 2`; graph already reduced) | `Section62ReductionWitnessAudit.bridging_*` |
| `SameLengthSection62Counterexample.truth_steps_survive_reduction`, `.competitor_steps_survive_reduction`, `.truth_spelled_feasible62`, `.competitor_spelled_feasible62` | `StepsSurviveReduction` / `SpelledFeasible62` | **survives verbatim** | `Section62ReductionWitnessAudit.sameLength_*` |
| `PerOccurrenceSameLengthCounterexample.truth_steps_survive_reduction`, `.competitor_steps_survive_reduction`, `.truth_spelled_feasible62`, `.competitor_spelled_feasible62` | `StepsSurviveReduction` / `SpelledFeasible62` | **survives verbatim** | `Section62ReductionWitnessAudit.perOccurrence_*` |
| `Section62NonSpelledFlow` `Feasible62` certificates on `reducedList` (`star21_feasible62_reduced`, `truth_feasible62`, `star31_feasible62`) | longer-overlap `reducedList`, plus literal vacuity | **survives**; at `oMin = 1` the corrected reduction equals the repository's longer-overlap reduction `reducedList` | `Section62ReductionDependencyAudit.nonspelled_reduction_spelling_eq`, `.star21_feasible62_spelling_reduced`, `.truth_feasible62_spelling_reduced`, `.star31_feasible62_spelling_reduced` |
| `Section62BidirectedFlow.SpelledFeasible62` / `StepsSurviveReduction` definitions | definition site | **retained as the audited model** (requirement 1); corrected analogues `SpelledFeasible62Spelling` / `StepsSurviveReductionSpelling` added alongside | `Section62ReductionWitnessAudit` |

No dependent conclusion is falsified by the correction; no conclusion requires
re-proving beyond the bridges above.

## The uniform reason the `oMin = readLen − 1` witnesses survive

For each of the three witnesses the read length is `3`, the threshold is
`oMin = 2`, and every generated edge has the maximal proper overlap length
`readLen − 1 = 2`. By `fullOverlap_not_reducible` no such edge is
spelling-preservingly reducible, so the corrected reduction is the identity:

```
transitivelyReducedSpelling … graphList = graphList
```

proved for each witness in
[../AssemblyP1/Section62ReductionWitnessAudit.lean](../AssemblyP1/Section62ReductionWitnessAudit.lean)
(`bridging_graph_spelling_reduction_eq_self`,
`sameLength_graph_spelling_reduction_eq_self`,
`perOccurrence_graph_spelling_reduction_eq_self`). Hence the corrected step
survival coincides with plain graph membership, and each witness satisfies the
corrected predicate `SpelledFeasible62Spelling`
(`…_truth_spelled_feasible62_spelling`, `…_competitor_spelled_feasible62_spelling`).

## The genuinely nontrivial case

At `oMin = 1` the corrected reduction is *not* the identity.
`Section62NonSpelledFlow`'s `AAATT` graph has length-`1` edges, and the corrected
reduction removes exactly the sixteen spelled through an observed read, leaving
the longer-overlap `reducedList`. The non-spellable flow countermodel survives
because its single length-`1` edge `AAT → TAA` has only the *unobserved*
intermediate `ATA` as a spelling detour; see
`Section62ReductionDependencyAudit.nonspelled_reduction_spelling_eq` and
[section62-nonspelled-flow-domain.md](section62-nonspelled-flow-domain.md).

## What this does and does not settle

* **Settled here (requirement 6).** Every §6.2 finite witness and flow certificate
  that referenced the old vacuous reduction survives under the corrected
  spelling-preserving reduction, with kernel-checked bridges.
* **Already settled elsewhere (requirements 1–5).** Old predicate preserved
  ([section62-reduction-vacuity-20261012.md](section62-reduction-vacuity-20261012.md));
  corrected predicate and forced-longer lemma
  ([../AssemblyP1/Section62SpellingReductionCandidate.lean](../AssemblyP1/Section62SpellingReductionCandidate.lean));
  finite positive regression with a genuinely removed edge and Myers comparison
  ([section62-longer-overlap-mismatch.md](section62-longer-overlap-mismatch.md),
  [section62-myers-ideal-transitivity-284.md](section62-myers-ideal-transitivity-284.md));
  global walk-language preservation
  ([../AssemblyP1/Section62GlobalSpellingPreservation.lean](../AssemblyP1/Section62GlobalSpellingPreservation.lean),
  `global_walk_signed_expansion`); Observation 7 for the corrected graph
  ([section62-observation7-skipped-windows.md](section62-observation7-skipped-windows.md)).
* **Still open (not requirements of this note).** Correspondence to the *full
  practical* Myers 2005 algorithm (`FUZZ = 10`, contained reads, parallel overlap
  identifiers) and unrestricted genome/flow realizability. The corrected model
  here is the idealized error-free equal-length relation; see
  [section62-myers-ideal-transitivity-284.md](section62-myers-ideal-transitivity-284.md).

## Axiom hygiene

Every theorem cited above is Lean-kernel-checked and depends only on
`propext`, `Classical.choice`, and `Quot.sound` (some depend on none). No
`sorry`, `admit`, `axiom`, or `native_decide` is introduced by this note or by
[../AssemblyP1/Section62ReductionWitnessAudit.lean](../AssemblyP1/Section62ReductionWitnessAudit.lean).

## References

* Medvedev–Brudno, *Maximum Likelihood Genome Assembly* (2009), §3.1–§3.4, §6.2,
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
* Myers, *The fragment assembly string graph* (2005), §2–§3, Fig. 4,
  <https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>.
