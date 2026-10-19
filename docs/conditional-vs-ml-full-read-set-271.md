# Full-read-set weighted placement mass for the #271 separation witness

_Status: research comparison note. This closes open item 2 of
[`conditional-vs-ml-genome-adapter-271.md`](conditional-vs-ml-genome-adapter-271.md)
by re-reading the finite `(A ∧ ¬B)` separation witness of
`AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` at the placement level, with
the source-literal event
`AssemblyP1.HistoricalCovers.HistoricalInformationFeasibleLiteral` and the
abstract weighted placement mass
`AssemblyP1.ConditionalIdentifiability.PlacementModel` / `placementJoint`._

> **Kernel-check status.** The module
> `AssemblyP1/ConditionalVsMLFullReadSet271.lean` is written and its finite
> content has been independently reproduced by a Python model of the exact
> `SourceFaithfulIs` predicates (all placements and reads, `G = 4`, `L = 2`).
> The Lean kernel replay was **not** completed in this environment: at the time
> of writing, every Lean invocation that loads an `.olean` (including
> `import Init.Data.Array.Basic`) deadlocked in the Lean runtime
> (`futex_wait_queue` / `io_sq_thread`, ≈0 CPU over tens of minutes) under a
> host load of ≈60–80 on 32 cores. This is an environment blocker, not a
> mathematical one; the statements below are labelled accordingly and the module
> is committed on a branch for kernel replay as soon as the toolchain runs.

## 1. The shared model, at the placement level

The adapter's finite model is re-read with the observation being the
**deduplicated observed read-string set** `Y : Finset Read`:

| axis | choice |
| --- | --- |
| candidate universe | the three rotation-orbit classes `0001`, `0011`, `0101` (`Fin 3`) |
| placement | `T : Finset (Fin 4)` (sampled read starts) |
| observation | `Y : Finset Read`, the induced set of oriented length-`2` strings |
| feasibility | `fullFeasible g T := HistoricalInformationFeasibleLiteral (genOf g) 2 T` |
| consistency | `fullConsistent g T Y := observedTypes_ofFinset (genOf g) 2 T = Y` |
| weight | `fullWeight g T := (1/4)^{|T|}` (each sampled start chosen among four positions) |
| event mass | `placementJoint fullModel fullWeight Y g = ∑_{T : consistent ∧ feasible} fullWeight g T` |

The resulting `PlacementModel` has its external Not-So-Greedy field
`decode_correct` **proved** (not hypothesized) on this finite model.

## 2. The finite content (independently reproduced)

Write `Y1 = {00,01,10,11}` (all oriented length-`2` strings), `Y2 = {01,10}`,
`Z0 = {00,01,10}`, and `Tfull = {0,1,2,3}`.

* **Coverage at read length two.** `HistoricalCovers S 2 obs` is
  `∀ t, ∃ d : Fin 1, …`; `Fin 1` is a singleton, so it says every position's
  length-`2` window lies in `obs`. Hence the window-type image of `S` is
  contained in `obs`, and `HistoricalCovers (genOf g) 2 obs` holds exactly when
  `obs` is the window-type image: `Y1` for `g = 1`, `Y2` for `g = 2`, `Z0` for
  `g = 0`.
* **Candidate `0` is never literally feasible.** `0001` has the length-`1`
  triple repeat `A` at starts `{0,1,2}`; the literal triple clause demands all
  three copies bridged, but `bridgesCopy_length` forces `e + 2 ≤ L`, i.e.
  `3 ≤ 2`.
* **The literal event pins the read set.** A consistent, literally feasible
  placement forces the observed read set to be `Y1` (candidate `1`) or `Y2`
  (candidate `2`); this is the proved `decode_correct`.
* **Support at the full read set.** At `Y1` the literal weighted mass is
  strictly positive on the truth orbit `1` (the saturated placement `Tfull`
  contributes `(1/4)^4`) and zero on `0` and `2`.
* **Certainty.** The merged #266 theorem `placement_posterior_certain` applied at
  `Y1` gives that the conditional mass of the decoder's orbit equals the total
  mass; combined with the support facts, the conditional posterior on the truth
  orbit is exactly `1`.

## 3. The precise boundary: the single-read witness does not lift

The adapter's `(A)`-side event is the **placement-based**
`SourceFaithfulIs.InformationFeasible` at the two-start placement `{0,2}`
(`feasible_genOf_one`). On this model that placement is `InformationFeasible`
but **not** `HistoricalInformationFeasibleLiteral`
(`witness_placement_not_literal`): at read length `2` the literal §6.4 coverage
clause forces every position to be a match start, and `{0,2}` leaves positions
`1` and `3` uncovered.

Consequently the literal weighted placement mass **vanishes at every
single-read observation**: literal feasibility forces coverage, coverage forces
the window-type image (cardinality `≥ 2`) into the observed set, and a singleton
cannot contain it. So:

* the single-read `(A ∧ ¬B)` separation is **not** reproduced by the literal
  full-read-set mass at the same observation; and
* at the full read set `Y1`, the literal mass gives `(A ∧ B)` coincidence — the
  truth is recovered with certainty and it is also the unique positive-mass
  candidate.

This is a representation/saturation boundary, recorded honestly rather than
manufactured into a contradiction. It sharpens the adapter's warning that the
`E`-event (`InformationFeasible`) and the source-literal historical event are
different predicates, and that the single-read observation is strictly weaker
than the full sampled read set.

## 4. Relation to the merged classification (reuse, no fork)

* `AssemblyP1.ConditionalIdentifiability.PlacementModel`,
  `placementJoint`, `placement_support_subset_orbit`, and
  `placement_posterior_certain` are reused by name; no generic posterior lemma is
  re-proved.
* The `(B)`-side is untouched: ordinary R-only ML classification remains
  #255/#258/#259/#261.
* `E → B` remains open and is not claimed. On this model `E` is refuted as
  ML-sound by the adapter (`sep_truth_not_ml`); the placement-level statement
  here is about the literal historical event, not about `E`.

## 5. Open items

1. **Kernel replay.** Run `lake build AssemblyP1.ConditionalVsMLFullReadSet271
   --wfail`, `leanchecker`, the `AxiomAudit271.lean` extension, and CI once the
   Lean runtime can load `.olean` files in this environment.
2. **`InformationFeasible` placement model.** A placement model whose event is
   the placement-based `InformationFeasible` (rather than the literal historical
   predicate) would directly contain the adapter's `E`; the present module shows
   the two events are not interchangeable at read length `2`.
3. **Larger read length.** The coverage obstruction is specific to `L = 2`
   (where the §6.4 interval `[t, t+L-2]` is a single position). For `L ≥ 3` the
   literal event can be attained by non-saturated placements, and the
   single-read/full-read-set comparison may differ.
