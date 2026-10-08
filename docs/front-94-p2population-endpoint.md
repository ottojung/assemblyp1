# Front 94 `94-primitive-p2pop`: primitive-P2 population endpoint

`[scheduler-turn]` — owner: AssemblyP1 #94 primitive-P2 uniqueness endpoint
(worktree `/workspace/assemblyp1-94-axiomaudit`, branch
`agent/94-primitive-p2pop-connect`).

## state

`working`. The primitive-P2 population reduction is driven to the exact
endpoint, with the single deep BBT input isolated as a named postcondition.

## summary (what changed, this turn)

Integrated the already-merged `AssemblyP1.P2GcdOne.gcd_one_of_primitive_P2`
into the population reduction and landed a new module
`AssemblyP1/P2PopulationEndpoint.lean` (registered in `AssemblyP1.lean`). It
proves, in the admissible range `2 ≤ L ≤ G`, `2 ≤ L ≤ K`:

1. `popTie_primitiveP2_equal_spectra` — a population tie between two primitive
   P2 genomes forces **equal lengths and equal complete L-spectra**, with **no**
   BBT/Ukkonen/condensed-graph hypothesis. Both gcd-one obligations are
   discharged project-side by `gcd_one_of_primitive_P2` and the
   proportional-cancellation (`population_uniqueness_of_spectra`). This is the
   sharpest statement of how far `P2` + primitivity + `lem:gibbs` reach.
2. `population_tie_primitiveP2_rotation_of_bbtUniqueAt` — the full
   tie-to-rotation endpoint composing (1) with the single `BBTUniqueAt`
   postcondition, used once, only for the final "equal spectra ⟹ RotEquiv".
3. `population_unique_ML_up_to_rotation_of_obstruction_range` — `thm:population`
   (both halves) carrying `EulerianCycleObstruction L` as the postcondition that
   `bbtUniqueAt_of_obstruction` feeds to (2).

This **narrows, and does not eliminate, the residual**: gcd one is now fully
project-side (the BBT-dependent `gcd_one_of_primitive_P2_words` route is no
longer on the critical path *within this range*), and the sole remaining deep
input is `EulerianCycleObstruction L` consumed exactly once.

## interface for the BBT/replacement sibling (`/workspace/assemblyp1-94-replacement`)

The endpoint closes `thm:population` in the range `2 ≤ L ≤ G` **iff** that
front proves `AssemblyP1.BBTEulerian.EulerianCycleObstruction (α := α) L`
(equivalently `UniqueEulerianCycle`, or `BBTUniqueAt`, via the identifications
already in `BBTEulerian`). Plug it into

```
population_unique_ML_up_to_rotation_of_obstruction_range _ hG (by omega) _ S
  hPrimS hP2S hObs
```

with no other hypothesis. Nothing else on this route is outstanding.

## resources / how to resume

- Module: `AssemblyP1/P2PopulationEndpoint.lean`; aggregator block: `AssemblyP1.lean`
  (~line 695 `P2GcdOne`, then the new `P2PopulationEndpoint` section, #print
  axioms at 752-754).
- Gates: `lake build` exit 0 (8996 jobs); `lake build --wfail` exit 0.
- Axioms: all three endpoint theorems depend only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Naming caveat: importing `P2GcdOne` pulls in the List-flavored
  `AssemblyP1.IsPrimitive` (AmpBmpPrimitivity), which shadows the circular-word
  `PopulationReduction.IsPrimitive`; the new module writes the primitivity
  hypotheses **fully qualified** to avoid the collision.

## next

- Complementary obligation, not idled: this front can pursue the range just
  outside `2 ≤ L ≤ G` — i.e. the read-longer-than-genome / small-window arm where
  the multiplicity cap does not apply — as the primitive-P2 analogue of the
  already-landed `Issue94KShort.obstruction_short_window` (`#94 front 94c20`).
  It must not duplicate the BBT/replacement sibling or the SlidePreserves-
  Interleaved census front.
