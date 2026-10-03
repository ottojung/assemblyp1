# #94 — the two-transposition step: the criterion is *crossing*, and
# `TwoTranspositionsBlock` is false

Board issue 94 (AssemblyP1 #89), front `B94-TWOTRANS-0101`, branch
`board/94-replacement`.  Builds on `docs/rematching-invariant-94.md`
(front `94a02`) and `AssemblyP1/BBTReplacementInvariant.lean` §6.

## 1. The verdict

`TwoTranspositionsBlock`, as named by front `94a02` §7, is **false**.  It is
refuted by the honest `00101` crossing that the whole `ρ` reformulation of
§5 was built around.  Kernel-checked in
`AssemblyP1/BBTReplacementInvariant.lean` §6.4 as
`not_TwoTranspositionsBlock`.

## 2. Why the cycle criterion asked for in §8 step 1 is the wrong one

Front `94a02` §8 asked for: *"`nextPos ∘ ρ` being a single cycle forces the
transpositions of `ρ`, read in the cyclic order `0, 1, …, K - 1`, to form a
single descending run"* (`Arratia`--`Buchberger`--`Reid` /
`Haar`--`Vahidi`--`Wolf`).  In the `ρ` language used here, that is false.
`nextPos` is the successor of the circle itself, so

> `nextPos ∘ ρ` is a `K`-cycle **iff the chords of `ρ` cross**.

Concretely, and these two are **kernel-checked by `decide` at `K = 5`**:
an involution `ρ` with `nextPos ∘ ρ` one cycle is a **crossing pair** of
transpositions (`crossing_criterion_5`), and a lone transposition never gives
a `K`-cycle (`one_transposition_not_oneCycle_5`).  A *nested* ("descending")
pair never gives one either — that direction is **not** kernel-checked in this
module; it is covered by the Python census below (`K = 4, 5, 6`: the only
involutions with one cycle are the crossing pairs, plus the identity), which
is evidence, not a proof.  The general form is recorded, unproved, as
`CrossingCriterion`.

This is fatal to the plan, and worth stating plainly: the crux configuration
`crux_rematchShape` (front `94a02` §5.3) **already assumes** the crossing,
because the two constituents interleave.  So the cycle criterion is not new
information at the crux — it is the interleaving restated.

## 3. The counterexample

`S = 00101`, `L = 3`, `K = 5`:

| fact | value | kernel name |
| --- | --- | --- |
| successor map | `θ5 = ![3,4,1,2,0]`, one cycle | `θ5_oneCycle` |
| fibre preserving | yes | `θ5_fibrePreserving` |
| selects an interleaving | `{1,3}` and `{2,4}` | `θ5_selectedInterleaved` |
| rematching permutation | `ρ5 = ![2,3,0,1,4] = (0 2)(1 3)` | `ρ5_values`, `θ5_is_nextPos_ρ5` |
| transpositions | `(prevPos 1 prevPos 3)`, `(prevPos 2 prevPos 4)` | `ρ5_transpositions` |
| interleaving | `1 < 2 < 3 < 4` | `starts_interleave_00101` |
| `Preceding`-clause | `Preceding 2 = Preceding 4 = 0` | `preceding_blocked_00101` |
| shift-class preservation | `ρ5` preserves every shift class | `ρ5_shiftClass` |
| conclusion | `¬ LongObstruction hG5 3 S5b` (`00101` is `P2`) | `not_longObstruction_00101` |

The refutation is `not_TwoTranspositionsBlock`, whose axiom set is
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## 4. Which clause fails, and whether it is repairable

The `Preceding`-clause of `TwoTranspositionsBlock` is **satisfied** at the
counterexample: the *blocked* constituent `(2, 4)` is one of the two crossing
constituents.  So the clause does not exclude anything, and it is **not
repairable in that role**: for a genome without a `LongObstruction`, an
interleaved pair *must* be blocked at some constituent — that is
`interleaved_maximal_pair` (front `94b02` §5.2, `BBTMaximalExtension`), already
in this repository.  Under `¬ LongObstruction` the clause is therefore not a
restriction at all; it is a consequence.

What actually excludes `00101` is **badness**: `θ5` satisfies
`OrbitVertexEq` (`θ5_orbitVertexEq`), i.e. it is good, so it is outside the
scope of `SupportDichotomy`.  That hypothesis is absent from
`TwoTranspositionsBlock` as stated.

## 5. The surviving statement

`TwoTranspositionsBlockBad` (§6.5) is `TwoTranspositionsBlock` with
`¬ OrbitVertexEq` added.  It is stated as a `Prop` and **not proved**.  It is
also **not a new obligation**: it is `InterleavingObstructionNeeded` (§5.4)
restricted to the two-transposition case.  A front that proves it has not
gained anything over one that proves §5.4 directly.

## 6. Bounded census of `00101` at `L = 3` (Python, complete over `Fin 5`)

Every permutation of `Fin 5` was enumerated (120 of them, so this is
*complete* for one-cycle `θ`, not merely evidence):

* one-cycle `θ`: 24;
* of those, fibre-preserving at `L = 3`: **2** — `nextPos` (`ρ = id`, the
  truth) and `θ5` (`ρ = (0 2)(1 3)`);
* of those, **bad**: **0**.

So `00101` has no bad fibre-preserving one-cycle `θ` at all, and
`TwoTranspositionsBlockBad` cannot be refuted at `00101`: any counterexample
to the strengthened form must live on a different genome.

The script is `scratch/twotrans_0101.py` (untracked).

## 7. What a later front should do instead

Do **not** try to repair `TwoTranspositionsBlock`, and do not build the
three-way simultaneous extension.  The remaining obligation is still
`InterleavingObstructionNeeded` (§5.4), and the useful structural news is that
the interleaving already implies the blocking, so no amount of `Fin`
permutation bookkeeping about chords can help: the cycle criterion is
equivalent to the interleaving hypothesis.