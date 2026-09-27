# `#89`: the ladder route, the block decomposition, and four refuted invariants

_Status: 2026-09-27. Kernel-checked partial results plus **finite refutations**.
Nothing here is a proof of `thm:BBT`; `AssemblyP1.P2.BBTUniqueAt` is still
unproved, and `AssemblyP1.PopulationUniqueness` still takes it as a hypothesis.
No `sorry`, no `admit`, no new `axiom`._

This note records the outcome of the ladder / global-block packet on
`agent/issue89-ladder-current`. It supersedes the "What is still missing"
paragraph of the `AssemblyP1/BBTLadder.lean` header, and it corrects two
statements that were in circulation as candidates for the remaining step.

## 0. The representation, and a step that must not be taken

The pull-back presentation `σ : Fin G ≃ Fin G` is **arbitrary**; `nextPos` and
`prevPos` are *geometric* maps on genome starts. In particular

```text
AltF hG σ (σ i)  =  σ (i + 1)          -- FALSE in general
```

is not a valid identity: it would force `vtx (σ i)` to be constant along the
listing, and `AltF_vtx` only says `vtx (AltF q) = vtx q`. The identities that
*are* kernel-checked, and that this packet uses, are

| lemma | statement |
| --- | --- |
| `Succ_apply` | `Succ hG σ (σ i) = σ (nextPos hG i)` |
| `Succ_eq_altF` | `Succ hG σ x = AltF hG σ (nextPos hG x)` |
| `AltF_vtx` | `vtx hG L S (AltF hG σ q) = vtx hG L S q` |

So the alternative traversal lives on **geometric** starts as

```text
f  = AltF hG σ                (a (L-1)-mer-preserving permutation)
ρ  = nextPos                  (the one-step rotation)
J  = f ∘ ρ = Succ hG σ        (the successor of the listing)
```

and "one `G`-cycle" --- `EulerianCycle`'s `single` clause --- is "`J` is a single
`G`-cycle". Every claim below is in this representation. `scripts/`
transcribes it directly.

## 1. The block decomposition, and what is now proved

Write `supp = Support f`. Under `P2` + primitivity, `f` is an involution
(`BBTLadder.AltF_sq`) whose two-element orbits are doubled `(L-1)`-mer pairs
(`orbit_is_doubledPair`), so `supp` is a set of chords of the condensed
multigraph, one per branch object the traversal actually re-pairs at.

`supp` splits into **blocks** by the deterministic maximal extension:
`x ~ y` iff the orbits of `x` and `y` carry the same `maxPair`. Two facts are
**proved** in `BBTLadder.lean` §6, from `P2` alone:

* `orbit_maxPair_isRepeat` --- every support orbit extends to a maximal repeat of
  length `≥ L - 1` (this is `maxPair_isRepeat`, i.e. `R1` at `n = 2`, read at the
  support). Without it, `P2.imp_ExtCrossing` has nothing to apply to.
* `support_blocks_nonCrossing` --- two **crossing** support chords do not have
  **crossing** maximal extensions. This is `P2.imp_ExtCrossing` instantiated at
  the support, and it says the blocks are **laminar**.

Each block is vertex-invisible: `ladder_of_coalescing` puts its two orbits at
`rotAdd ℓ p` and `rotAdd ℓ q` for the single pair `(p, q)`, and `ladder_arc_eq`
gives `vtx (rotAdd i p) = vtx (rotAdd i q)` for every shift that fits in the
block's maximal repeat.

So `#89` reduces to exactly two statements, both now `Prop`s with **no
inhabitant** (`BBTLadder.lean` §7):

1. **`CrossingChordsCoalesce`** (the repeat-theoretic core) --- two crossing
   support chords must carry the **same** deterministic maximal extension.
2. **`LadderVertexCycle`** (the global block lemma) --- a laminar family of
   vertex-invisible ladder blocks forces the vertex listing to be a rotation of
   the truth's, i.e. `VertexCycleEq`.

`LadderVertexCycle` replaces the previous `LadderRotationGap`. The old
statement took a *local* antecedent --- two orbits coalesce --- and a *global*
conclusion, `VertexCycleEq`. That is the wrong way round twice over: it makes the
block structure an *assumption*, and it cannot be applied to a support that does
not coalesce (see §2, item 2: such supports exist). What has to be *derived* is
`CrossingChordsCoalesce`; what has to be *assembled* is `LadderVertexCycle`.

Note the target is `VertexCycleEq` throughout, never start-level equality and
never `f = id`. `S = 00101`, `G = 5`, `L = 3` has `f = (1 3)(2 4) ≠ id` and a
**correct** `VertexCycleEq`; a route that concludes `f = id` is refuted by it.

## 2. Four invariants that are refuted (finite certificates)

`scripts/verify_ladder_blocks_89.py` enumerates, for every primitive `P2` word,
every `(L-1)`-mer-preserving involution `f` with `J = f ∘ ρ` a `G`-cycle, and
checks each candidate. Over binary `G ≤ 10` and ternary `G ≤ 7` that is **3770**
genuine traversals with nontrivial support. Results:

| candidate | result |
| --- | --- |
| `VertexCycleEq` | **0 failures** / 3770 — `thm:BBT` at `K = L-1` survives `G = 10` |
| `CrossingChordsCoalesce` | **0 failures** / 3770 |
| `LadderVertexCycle` (read off the listing) | **0 failures** / 3770 |
| `nextSupport (f x) = f (nextSupport x)` | **70 failures** |
| "support = the single ladder of one maximal repeat" | **70 failures** (the same 70) |
| "support = ⊔ full ladders of all maximal repeats of length ≥ L-1" | **2550 failures** |
| "the geometric gap lengths of a ladder are equal" | refuted by `S = 00101` |

These are *finite refutations*, which is the strongest thing a search can give
here; the completeness of the search is not itself proved.

**(1) Support-commutation is FALSE.** With `nextSupport x` the next support point
clockwise after `x`, the claim `nextSupport (f x) = f (nextSupport x)` for
`x ∈ supp` is verified for `G ≤ 9` (1110 cases) and **fails at `G = 10`**. Smallest
witness:

```text
S = 0010010101,  G = 10,  L = 5  (K = 4)
K-mers:  0,3 -> 0010   1,8 -> 0100   2,9 -> 1001   4,6 -> 0101   5,7 -> 1010
f = (0 3)(1 8)(4 6)(5 7)            supp = {0,1,3,4,5,6,7,8}
nextSupport(0) = 1,  f(nextSupport 0) = f(1) = 8
nextSupport(f 0) = nextSupport(3) = 4  ≠  8
```

`VertexCycleEq` nevertheless **holds** here. So support-commutation is not a
lemma; it is an artefact of `G ≤ 9`. This is the reason the packet does not
pursue it.

**(2) The support is not a single ladder.** The same 70 witnesses have support
spanning **two** maximal repeats: in the witness above, the four chords carry
just two maximal extensions, one at the start pair `{1, 8}` of length 6 (carried
by the chords `{0,3}` and `{1,8}`) and one at `{4, 6}` of length 5 (carried by
`{4,6}` and `{5,7}`). They do not interleave (Ukkonen forbids that), so the block structure is
genuinely *laminar with more than one block*, and the block argument has to be
global. This is also why `LadderRotationGap` was unusable: its antecedent, "two
orbits coalesce", need not hold.

**(3) The support is not the full ladder union.** For `S = 000101`, `L = 3`,
`f = (2 4)(3 5)`, the support is `{2,3,4,5}` while the union of the full ladders
of all maximal repeats of length `≥ 2` is all of `Fin 6`. A traversal need not
re-pair at *every* branch vertex, so the support is a union of *partial* ladders
and one cannot charge the unvisited branch objects to the support.

**(4) Equal geometric gap lengths are FALSE.** For `S = 00101`, `G = 5`, `L = 3`,
`f = (1 3)(2 4)`: `nextSupport` commutes here, but the gaps `2 → 3` and `4 → 1`
have lengths 1 and 2. Combinatorially, `f` is the *antipode* on the cyclic order
of the support (`f = nextSupport^{|supp| / 2}`), which is not a statement about
geometric lengths. Since `f` is an involution, "commutes with `nextSupport`" and
"is the antipode" are equivalent, so item (1) refutes the antipode form too.

## 3. Why the purely combinatorial form is unavailable

`nextSupport`-commutation is false for *abstract* involutions at `G ≥ 8`: take
`G = 8`, `supp` everything, `f = (0 2)(1 3)(4 6)(5 7)`. Then `f ∘ ρ` is a
`G`-cycle, and `f` is not a rotation of the cyclic order of `supp` (it is shift 2
on `{0,1,2,3}` and shift −2 on `{2,3}`, consistently). So a purely combinatorial
proof is impossible and the **word** must enter.

The word enters through a sharp observation: if chords `{a, c}` and `{b, d}`
cross with `a < b < c < d` and `vtx a = vtx c`, `vtx b = vtx d`, then, since
`vtx (x+1) = shift (vtx x)`, one gets `shift² (vtx a) = vtx a` — the repeated
`K`-mer has period 2. In the `G = 8` example that forces the whole word to be
periodic, so primitivity kills it. Making this precise is the job of
`CrossingChordsCoalesce`, and it is the place where the missing repeat theory
lives.

## 4. The next step, stated as a program

1. **`CrossingChordsCoalesce`.** Take two crossing support chords, extend both
   maximally, and show the extensions coincide. The available tools are
   `orbit_maxPair_isRepeat` (§6.1), `support_blocks_nonCrossing` (§6.2) for the
   *contrapositive* direction, and `P2.imp_ExtCrossing` to show the extensions
   are **not interleaved** — so the only remaining possibility is coincidence.
   This is the "shift left" iteration of
   `docs/arratia-shift-left-invariant-89.md` §1: the shift either reaches the
   both-leftmost configuration (an innermost chord, excluded by
   `EulerianCycle_no_innermost_chord`) or collides (a three-way repeated
   `K`-mer, excluded by `P2` clause 1), and the *load-bearing* clause is that
   the shift preserves the block, which is what "coalesce" records.
2. **`LadderVertexCycle`.** With the blocks laminar and each vertex-invisible,
   show the traversal visits the blocks in geometric order. This needs no `P2`:
   the search verifies it on the unfiltered set too, so it is a statement about
   `f`, `ρ` and the block order alone.

## 5. Reproducing

```sh
python3 scripts/verify_ladder_blocks_89.py --bin 10 --tri 7
```

Roughly 20 minutes. `--bin 6 --tri 5` is a fast smoke test.

## 5. Corrections: the coalescence statement is about *unordered* pairs, and
## the block lemma needs a *global* antecedent

Two defects were found by audit of this branch's `AssemblyP1/BBTLadder.lean`
after §1--§4 above were written.  Both are recorded here because they are easy
to reintroduce.

### 5.1 Ordered `maxPairStart` equality is refuted

`Interleaved (mkGenome hK S) a b c d` is
`FourDistinct a b c d ∧ (InOpenArc a b c ↔ ¬ InOpenArc a b d)`
(`SourceFaithfulIs.Interleaved`, line 365), so it is **symmetric in `c` and
`d`**.  A hypothesis about `(a, b, c, d)` is therefore a hypothesis about
`(a, b, d, c)`, while `maxPairStart a b` and `maxPairStart b a` are the two
*swapped* starts of one repeat.  So the ordered conclusion

```text
  maxPairStart a b = maxPairStart c d  ∧  maxPairStart b a = maxPairStart d c
```

cannot hold in general.  Witness, from the search's own vocabulary:

```text
S = 00101,  G = 5,  L = 3,  f = (1 3)(2 4)   -- a genuine traversal, VertexCycleEq holds
a = 1, b = 3, c = 4, d = 2
Interleaved 1 3 4 2      : the open arc from 1 to 3 is {2}, so 4 is outside and 2 inside
maxPairStart 1 3 = 1     maxPairStart 3 1 = 3
maxPairStart 4 2 = 3     maxPairStart 2 4 = 1
ordered conclusion       : 1 = 3 ∧ 3 = 1        -- FALSE
unordered conclusion     : {1,3} = {1,3}        -- TRUE
```

The fixed interface is `BBTLadder.SameExtension hK S a b c d`, the disjunction
of the two orientations.  Every statement in this branch now uses it, and the
one-step-slide proof of §6 needs it in that form.

### 5.2 The block lemma's antecedent must quantify over *all* crossing pairs

`LadderVertexCycle` in its first draft took a *single* crossing pair of support
chords coalescing as its antecedent and concluded the global `VertexCycleEq`.
That is the same defect as the original `LadderRotationGap`: a local hypothesis
with a global conclusion.  It cannot be applied to a support that does not
coalesce, and it makes the block structure an assumption rather than the thing
to be derived.  The fixed form quantifies over **all** crossing quadruples:

```text
  (∀ a b c d, support chords ∧ Interleaved → SameExtension)  ⟹  VertexCycleEq
```

The conclusion is the full `VertexCycleEq` and is not weakened.

This is also the reduction the search supports: "every crossing support pair
coalesces" implies `VertexCycleEq` on the *unfiltered* set too --- 1110 of 1832
binary and 1050 of 1614 ternary instances satisfy the hypothesis, and **none**
of those fails `VertexCycleEq`.  Note the hypothesis holds in *exactly* the
primitive-`P2` instances in that range, which is a consistency check on the
statement rather than on the proof.

## 6. The coalescence proof, and the three `Prop`s that remain

Let `k = L - 1 ≥ 1`, let `w = vtx` be the `(L-1)`-window labelling, and call
`{a, b}` with `a ≠ b` and `w a = w b` a **chord**.

1. **Fibres have size two**, so two chords sharing an endpoint are *equal*
   (`BBTCrossingCoalesce.three_starts_ne`, proved).
2. **The canonical unordered extension is constant along a component.**  Join
   `{a, b}` to `ρ {a, b}` when the latter is a chord.  The `ρ`-orbit of a chord
   is the finite backward list `C_j = {a - j, b - j}`, `j ≤ β`, whose head is
   the chord `{maxPairStart a b, maxPairStart b a}`; the canonical extension is
   constant on the list, hence on each component.  Primitivity excludes a cyclic
   component, since a cycle would propagate `S x = S (x + (b - a))` round the
   circle, a nontrivial period.  So components are paths.
3. **Slides never meet a chord of another component**, by (1).
4. **A one-step slide preserves interleaving** provided no endpoint collision
   (`SlidePreservesInterleaved`).  By (3) the condition holds all the way down,
   so sliding each chord to its component head preserves the crossing.  Hence
   the two heads cross.
5. **Contradiction**: the heads are maximal repeats of length `≥ L - 1`
   (`maxPair_isRepeat`), so they cannot cross --- that is `P2`'s clause 2, read
   as `P2.imp_ExtCrossing`.  So the two chords are in one component and share
   their canonical unordered extension.

So the whole of `#89` on this route is three `Prop`s, and nothing else:

| `Prop` | module | kind | instances checked |
| --- | --- | --- | --- |
| `CrossingPairsCoalesce` | `BBTCrossingCoalesce` | target | 2534 + 168, 0 failures |
| `SlidePreservesInterleaved` | `BBTCrossingCoalesce` | new cyclic-order fact | 2490, 0 failures |
| `ShiftLeftPersistence` | `BBTCrossingCoalesce` | word-level | (endpoint case proved) |

`ShiftLeftPersistence` is stated for a plain shift amount rather than for
`pairBack`, and is not proved here for a *visibility* reason rather than a
mathematical one: the predicate `P2RepeatResidual.backAgree` behind `pairBack`,
`pairBack_ge` and `pairBack_spec` is `private` to
`AssemblyP1/P2RepeatResidual.lean`, so `pairBack_ge` cannot be applied from
another module.  That lemma belongs next to `pairBack`, in that file.

Everything else in `BBTLadder.lean` §1--§6 and in `BBTCrossingCoalesce.lean`
§1--§4 is **proved** (subject to the build status recorded in the commit
messages).  No `sorry`, no `admit`, no new `axiom`, no linter suppression.
