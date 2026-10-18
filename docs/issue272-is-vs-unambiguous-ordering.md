# Issue #272: `I_s` versus `Unambiguous` — the ordering question

_Status: 2026-10-17 (literal read-string adapter landed, PR #297). Mathematical
formalization front. Companion Lean module:
[`AssemblyP1/FiniteSideInformationOrdering.lean`](../AssemblyP1/FiniteSideInformationOrdering.lean),
audited by
[`AssemblyP1/FiniteSideInformationOrderingAudit.lean`](../AssemblyP1/FiniteSideInformationOrderingAudit.lean).
Extends, without duplicating, the merged modules
[`AssemblyP1/FiniteBayesianSideInformation.lean`](../AssemblyP1/FiniteBayesianSideInformation.lean)
(PR #195, `b0a6e9f`) and
[`AssemblyP1/FiniteSideInformationOrder.lean`](../AssemblyP1/FiniteSideInformationOrder.lean)
(PR #204, `c312cbbc`)._

## The question

The merged `#272` modules left one ordering question **OPEN** (§6 of
[the side-information-order note](issue272-side-information-order.md)):

> Is the source-faithful information-feasibility predicate `I_s`
> (Shomorony--Kim--Courtade--Tse 2016) ordered against the read-only promise
> `Unambiguous`: does `I_s ⇒ Unambiguous`, does `Unambiguous ⇒ I_s`, or neither?

## The answer

**Neither**, and the reason is structural, not a missing lemma:

* `Unambiguous` is a **read-only** promise — it depends only on the observed
  read `r`, not on the unknown truth `g`.
* `I_s` (`SourceFaithfulIs.InformationFeasible`) is a **truth-dependent**
  promise — its coverage and bridging clauses are predicates of the candidate
  genome.

They therefore live in different promise families. The read-only boundary
theorem proved here applies only to the read-only family, so it does not order
`I_s`; and the general non-implication theorem shows that sufficiency of a
truth-dependent promise never forces it below `Unambiguous`.

| statement | status | theorem |
|---|---|---|
| Any promise implying `Unambiguous` is sufficient | kernel-checked | `sufficient_of_imp_unambiguous` |
| Read-only promise is sufficient **iff** it implies `Unambiguous` | kernel-checked | `sufficient_readonly_iff_imp_unambiguous` |
| `Unambiguous` is a read-only promise | kernel-checked | `unambiguous_promise_readOnly` |
| Singleton truth-dependent promise is sufficient | kernel-checked | `singleton_promise_sufficient` |
| Sufficient truth-dependent promise need not imply `Unambiguous` | kernel-checked | `singleton_promise_not_imp_unambiguous` |
| `Unambiguous` need not imply a truth-dependent promise | kernel-checked | `unambiguous_not_imp_singleton` |
| Combined neither-implication, one model | kernel-checked | `truthdependent_sufficient_incomparable` |
| Concrete three-candidate witness | kernel-checked | `ThreeCandidate.neither_implication` |
| `I_s` is **not** a read-only promise | kernel-checked | `IsTruthDependence.informationFeasible_not_readOnly` |
| Literal read-string adapter for `I_s` as one observation type | kernel-checked (PR #297) | [`FiniteSideInformationReadStringAdapter`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean) / [adapter note](issue272-read-string-adapter.md) |

All endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`
(`#print axioms` audit); no `sorry`, `admit`, `axiom`, or `native_decide`.

## 1. The read-only boundary

`Unambiguous π p orbit r` says the read support at `r` lies in a single rotation
orbit. The merged `unambiguous_sufficient` already shows it is sufficient. Two
new facts pin down its exact role in the promise order:

* `sufficient_of_imp_unambiguous`: if `E ⇒ Unambiguous` pointwise, then `E` is
  sufficient. (Sufficiency is downward closed under strengthening; the merged
  `sufficient_of_stronger` applied to `unambiguous_sufficient`.)
* `sufficient_readonly_iff_imp_unambiguous`: for a read-only promise
  `φ : Obs → Prop`,
  ```
  Sufficient π p orbit (fun _ r => φ r)  ↔  ∀ r, φ r → Unambiguous π p orbit r.
  ```
  So `Unambiguous` is the **exact** sufficient lower boundary of the read-only
  family, refining the merged "unique weakest read-only sufficient promise"
  result into a pointwise criterion.

## 2. Truth-dependence defeats the boundary

For any model, the singleton promise `fun g _ => g = g₀` is sufficient (its
fibre has at most one candidate). But:

* `singleton_promise_not_imp_unambiguous`: if some read `r` is genuinely
  ambiguous (`∃ h, 0 < π h, 0 < p h r, orbit h ≠ orbit g₀`) while `g₀` is
  possible at `r`, then `g = g₀` does **not** imply `Unambiguous`.
* `unambiguous_not_imp_singleton`: if `Unambiguous r` holds and a candidate
  `g₁ ≠ g₀` is possible at `r`, then `Unambiguous` does **not** imply `g = g₀`.

`truthdependent_sufficient_incomparable` packages both failures for one model and
one promise; `ThreeCandidate.neither_implication` instantiates it on a concrete
finite model (three candidates, two reads; read `0` ambiguous, read `1`
unambiguous) that is deliberately distinct from the merged `Incomparable`
(two candidates) and `NoWeakest` (four candidates) witnesses.

This is the manuscript-ready statement: **sufficiency alone never orders a
truth-dependent promise against the read-only `Unambiguous`.**

## 3. The source predicate `I_s` is truth-dependent

Fix genome length `G = 5`, read length `L = 3`, and read-start set
`R = {0,3}`. Represent a candidate by its length-`5` spelling `Fin 5 → Base` and
read the source predicate as

```
isPromise w R := InformationFeasible (ofSpelling w) 3 R.
```

* `truthSpelling = AABBC` is `I_s`-feasible at `(L, R) = (3, {0,3})`
  (`truthSpelling_feasible`; the same certificate as the merged
  finite-sampling witness).
* `aaaabSpelling = AAAAB` is **not** `I_s`-feasible at the *same* `(L, R)`
  (`aaaabSpelling_not_feasible`): its only maximal triple repeat has length
  `2 = L - 1`, which clause 2 of `I_s` forbids because no length-`3` read can
  straddle it.

Since two candidates with the same `(L, R)` disagree on `I_s`,
`informationFeasible_not_readOnly` proves

```
¬ AdmReadOnly isPromise,
```

i.e. `I_s` is not a read-only promise. Consequently the read-only boundary
theorem of §1 — and the merged read-only weakest-promise theorem — **do not
apply** to `I_s`. This is the precise structural obstruction to reading
`I_s ⇒ Unambiguous` off the merged semantics.

## 4. Why this is not merely a missing bridge

The literal source event is `I_s(S, R)` for the *true* genome `S` and the
*sampled start set* `R`. The observed data, however, are read *strings*; `R`
itself is latent, and the candidate's intrinsic length makes `Fin S.len`
candidate-dependent. This is exactly the placement/string gap analysed in
[`AssemblyP1/ConditionalIdentifiability.lean`](../AssemblyP1/ConditionalIdentifiability.lean)
(#266): the source event must be expressed at the placement level as
`E g T` and marginalised over compatible placements, not read as a function of a
single observation type. That adapter is now provided by
[`FiniteSideInformationReadStringAdapter`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean)
(PR #297): it fixes the distinct read-string set as one observation type and
makes `I_s` a well-typed truth-dependent promise, but proves that promise is
read-dependent (outside both `AdmReadOnly` and `AdmTruthOnly`). The verdict
therefore remains "neither" — now for the well-typed promise, since sufficiency
alone still does not order a truth-dependent promise against `Unambiguous`.

## 5. Remaining open work

1. **Concrete historical read-string adapter.** LANDED (PR #297; see
   [`issue272-read-string-adapter.md`](issue272-read-string-adapter.md)): the
   adapter fixes the distinct read-string set as one observation type, defines
   the source-faithful truth-dependent promise by marginalising
   `HistoricalInformationFeasibleLiteral` over the compatible placements,
   proves it is read-dependent, and applies `weakest_admissible_iff_union` to
   the resulting read-dependent `I_s` family. The *decoder-level* certainty
   endpoint is now LANDED as an attributed-premise bridge
   ([`AssemblyP1.FiniteSideInformationDecoderEndpoint.lean`](../AssemblyP1/FiniteSideInformationDecoderEndpoint.lean)):
   a read-only decoder `A` carrying the external 2016 Not-So-Greedy guarantee as
   an explicit hypothesis implies conditional posterior one on the true orbit
   class. The external guarantee itself remains attributed, not proved. OPEN
   (external premise only).
2. **`I_s` necessity for the specific Not-So-Greedy decoder.** Still OPEN and
   source-level; the order results here do not address it.
3. **Weakest source-defined bridging promise.** Still reduced by
   `weakest_admissible_iff_union` to whether the union of source-defined
   sufficient promises is itself source-defined and sufficient. OPEN.

## 6. No duplication

* The merged `FiniteBayesianSideInformation` (`Sufficient`, `Stronger`,
  `Unambiguous`, `TwoCandidate`, `Incomparable`, `NoWeakest`) is imported and
  reused unchanged.
* The merged `FiniteSideInformationOrder` (`AdmReadOnly`, the union criterion,
  `NoWeakestProb`) is imported and reused unchanged.
* `#266` (`ConditionalIdentifiability`) and `#269` (`FiniteBayesDecision`) cores
  are neither imported nor modified.
* The new `ThreeCandidate` model and the general singleton-promise theorems are
  new; they are not the merged `Incomparable`/`NoWeakest` witnesses.
