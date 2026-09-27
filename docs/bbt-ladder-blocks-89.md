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
