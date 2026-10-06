# Issue #89 / board 94, front `94iface`: the residual is `P2LongUnique`, and
# that is the target a route has to hit

Branch `research/94-phoebe-end2end`, module
`AssemblyP1/Issue94P2PrimInterface.lean`, namespace
`AssemblyP1.Issue94Interface`. Companion (compile-gated) module
`AssemblyP1/Issue94LongWindowSplit.lean`, namespace
`AssemblyP1.Issue94Split`.

**Bottom line.** `Issue94EulerianRealize` landed the converse bridge, so
`EulerianCycleObstruction L ↔ BBTUniqueAt L` at `2 ≤ L`. That means the
endpoint's residual is no longer an internal gap: it is `thm:BBT` and nothing
else. This front does three further things, all kernel-checked:

1. **Names the residual in the weakest form the endpoint actually consumes.**
   It is *not* `BBTUniqueAt L` and *not* `EulerianCycleObstruction L`. It is
   `BBTP2Prim L`: complete-spectrum uniqueness restricted to `P2`-**and
   primitive** truths.
2. **Splits it into one range.** The `K ≤ L - 1` half is already a theorem
   (`Issue94KShort`, for arbitrary words). So the residual is
   `P2LongUnique L` alone --- the `K ≥ L` half.
3. **Proves the reduction from it to the population endpoint**, so any route
   that proves `P2LongUnique L` has a one-line application afterwards.

## 1. Where the slack is: the two use sites

`PopulationUniqueness.population_unique_ML_up_to_rotation` takes one hypothesis,
`hPevzner : EulerianCycleObstruction L`, and derives everything else through
`bbtUniqueAt_of_obstruction`. `EulerianCycleObstruction` reaches the population
objective at exactly **two** sites, `PopulationUniqueness.lean:212` and `:214`,
and at both:

| | |
|---|---|
| the word `BBTUniqueAt` is applied to | the truth `S` or `W` |
| its class | `P2`, hence `Ukkonen`, **and** `IsPrimitive` |
| its competitor `E` | ranges over **all** `Fin K → α` |
| genome length `K` | **unrestricted** |

So `BBTUniqueAt L` is used only where `P2` and primitivity already hold. That is
the whole slack, and it is what `BBTP2Prim` isolates.

Note the asymmetry in `BBTCompleteSpectrumUniqueness` (`P2.lean:154`): `Ukkonen`
is demanded of the **truth only**, never of the competitor. So no hypothesis on
`E` is needed, and `BBTP2Prim` correctly does not state one.

## 2. The interface

```lean
def BBTP2Prim (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), P2 hK L W → IsPrimitive W →
    ∀ E : Fin K → α,
      specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W
```

Stated on the project's own objects only: no `EulerianCycle`, no `Matching`, no
`pullback`, no `AltF`, no chord vocabulary. A route does not have to build any
graph machinery to hit it.

`BBTP2Prim'` is the same with `BBTCompleteSpectrumUniqueness` packaging (the
competitor quantified inside); `bbTP2Prim_iff_bbTP2Prim'` proves the two
interderivable at `2 ≤ L`, the sole use of `2 ≤ L` being `P2.imp_Ukkonen`.

## 3. The long/short split, and why the short half is free

```lean
def P2LongUnique    (L : ℕ) := BBTP2Prim restricted to L ≤ K
def ShortRangeUnique (L : ℕ) := BBTP2Prim restricted to K < L
```

`long_short_of_long : P2LongUnique L → ShortRangeUnique L → BBTP2Prim L` --- a
case split on `L ≤ K`, no arithmetic beyond `omega`.

`ShortRangeUnique L` is **inhabited for every `L ≥ 2`**, because
`Issue94KShort.vertexCycleEq_short_window_general` proves the short window for
an **arbitrary** circular word: no `P2`, no primitivity, no `Ukkonen`. So of the
two ranges, one is already closed and the residual is `P2LongUnique L`.

## 4. The reduction, kernel-checked

| theorem | meaning |
|---|---|
| `population_unique_ML_of_P2Prim` | `thm:population` from `BBTP2Prim L`; conclusion **verbatim** that of `PopulationUniqueness.population_unique_ML_up_to_rotation` |
| `population_unique_ML_of_long_unique` | same, from `P2LongUnique L` + `ShortRangeUnique L` |
| `population_unique_ML_same_length_of_P2Prim` | the `same_length` reading |
| `population_tie_implies_rotation_of_P2Prim` | the two-genome reading |
| `bbTP2Prim_of_bbtUniqueAt`, `bbTP2Prim_of_obstruction` | the interface follows from what is already postulated, so nothing is lost |
| `population_unique_ML_of_BBTUniqueAt` | the endpoint follows from `thm:BBT` **in its source form**, through the `Issue94EulerianRealize` bridge, with no Eulerian-cycle object named |

The last line is the clean dependency statement of #89: after that bridge
landed, the published theorem is a sufficient hypothesis for the endpoint, and
nothing of this project's own stands between them.

## 5. Placement relative to the other lines of work

* `BBTP2Prim L` is **weaker** than `EulerianCycleObstruction L`: it drops the
  `Ukkonen`-only words, the primitivity-free range, and the disjunction. Whether
  the weakening is *strict* is not claimed. It would be strict unless `P2` and
  `Ukkonen` are interderivable on the whole circle --- which
  `AssemblyP1/Issue94P2Iff.lean` asserts and whose own module banner marks
  **UNVERIFIED**. This front does not use it and reaches no verdict.
* The ladder route's residual is `BBTLadder.LadderVertexCycle` /
  `Issue94TW1EdgeType.BlocklessLadderVertexCycle`. Per
  `docs/issue-94-eulerian-realize.md`, `BBTLadder.CrossingChordsCoalesce` is
  **refuted at `L = 1`**, so that route's own bound `2 ≤ L` is necessary; a route
  hitting `P2LongUnique L` carries no such bound and is not exposed to that
  refutation.
* `Issue94TW5Single.uniqueEulerianCycle_iff_labelPreserving` shows the
  Eulerian-cycle object is equivalent to a `LabelPreserving` statement, and
  `BBTEulerian.UniqueEulerianCycle` is the object `BBTP2Prim` reduces to at
  `2 ≤ L` (`BBTUniqueAt ↔ UniqueEulerianCycle ↔ EulerianCycleObstruction`, and
  `Issue94Realize.obstruction_iff_bbtUniqueAt` closes the outer direction). So a
  route proved in any of these languages can be converted before being applied.

## 6. On Cohn–Lempel / block deletion

No Cohn–Lempel or block-deletion architecture exists in this repository yet: a
search over all 497 refs, all commit subjects and bodies, the whole working tree
and all reflogs returns nothing. There are empty placeholder branches
(`research/94-phoebe-blockdelete`, `-cle`, `-ladderdelete`) all pointing at
`d895bc4` with no block-delete commits. So this module is the **plug-in point**
rather than a consumer: whatever such a route proves should be delivered as an
inhabitant of

```lean
AssemblyP1.Issue94Interface.P2LongUnique L      -- at 2 ≤ L
```

after which `population_unique_ML_of_long_unique` applies immediately. The
interface is deliberately free of the graph vocabulary such a route would
naturally introduce, so it can be proved in isolation and combined here.

## 7. Build status, and what was verified

`AssemblyP1/Issue94P2PrimInterface.lean`:

```
$ lake build AssemblyP1.Issue94P2PrimInterface
```

exit 0, **no warnings**, no errors. Every `#print axioms` line reports only
`propext`, `Classical.choice`, `Quot.sound`; `grep -c sorryAx` on the output is
`0`. It is registered in `AssemblyP1.lean` and its import chain reaches
`Issue94EulerianRealize` (16 modules) but **not** `AssemblyP1.Issue94OrbitSearch`.

`AssemblyP1/Issue94LongWindowSplit.lean`: **not compiled on this host.** It
imports `AssemblyP1.Issue94KShort`, whose transitive imports reach
`AssemblyP1.Issue94OrbitSearch`, which is OOM-killed (exit 137) under the 8 GiB
cgroup on this container. This is pre-existing and recorded at
`docs/issue-94-eulerian-realize.md` §7 and `docs/board94-green-restore.md`; it
is not caused by this front and no scheduling decision is derived from it.

To establish that the *content* of that file is sound anyway, every statement in
it was elaborated in a throwaway probe (`scratch94/SplitProbe.lean`, since
deleted) against the real `Issue94P2PrimInterface`, with the two applications of
`Issue94KShort` replaced by `axiom`-typed hypotheses of exactly their stated
signature. All elaborated; the resulting `#print axioms` output listed only
those two stand-ins. So the content is checked and what is **not** checked is
that the two stand-ins are supplied by the named `Issue94KShort` declarations.
Both are one-line applications of already-merged theorems at their stated
signatures (`Issue94KShort.lean:536` and `:553`). The `axiom`s existed only in
the deleted probe and are not in the committed file.

The split module is deliberately **not** registered in `AssemblyP1.lean`, since
that would put the `OrbitSearch` OOM on the aggregator's critical path.

## 8. What this does not do

* **No inhabitant of `BBTP2Prim L` or `P2LongUnique L`, at any `L`.** Issue #89
  is not settled. The remaining mathematical content is `thm:BBT` on the
  `P2`-primitive class in the long window, and those `def`s are its exact
  statement.
* No definition was changed to make anything provable. `BBTUniqueAt`,
  `BBTCompleteSpectrumUniqueness`, `EulerianCycleObstruction`,
  `UniqueEulerianCycle`, `P2`, `Ukkonen`, `IsPrimitive`, `RotEquiv`,
  `specCount`, `Matching`, `pullback`, `window`, `vtx`, `AdmClass`,
  `popSpectrum`, `PopLogLik`, `PopTie` are used exactly as their own modules
  state them.
* No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter
  suppression in either committed file. The only `set_option`s are
  `maxHeartbeats` and the repository-conventional
  `linter.unusedSectionVars`.