# Board 94, front `94comp` --- the interlace graph on chords

Companion note for `AssemblyP1/Issue94InterlaceComponents.lean` and
`scripts/verify_interlace_components_94.py`.

## 1. The graph

Motivated by Arratia--Bollobas--Coppersmith--Sorkin (2000) on the interlace
polynomial: study the **interlacement structure** of the changed branch
transitions rather than the traversal as a whole.

* **vertices** = the transposition orbits of `f = AltF hK σ` --- the changed
  branch transitions, each counted once as the unordered chord
  `{a, AltF hK σ a}`;
* **edges** = `Interleaved` between the two chords, in the current tour;
* **blocks** = the classes of `BBTLadder.SameExtension`, i.e. of the unordered
  pair `{maxPairStart hK S a b, maxPairStart hK S b a}` of deterministic
  maximal-extension starts.

**No statement about the interlace polynomial is made or needed.** The
Arratia--Bollobas--Coppersmith--Sorkin input used here is the *graph*, which is
a finite combinatorial reformulation of the support, not a spectral statement.

## 2. The question, and the answer

> Does `Issue94CrossingChords.CrossingChordsCoalesce_ge2` plus a packaged
> transitivity/equivalence lemma for `SameExtension` force **each connected
> component into one maximal-extension ladder**?

**Yes --- proved, and weak.** In the kernel:

| lemma | content |
|---|---|
| `pair_two_eq` | two-element `Finset`s are equal only by matching or swapping |
| `SameExtension_iff_pairEq` | `SameExtension a b c d` **is** `ExtPair a b = ExtPair c d` |
| `ExtPair_comm` | `ExtPair` does not see the order of its two arguments |
| `SE_refl`, `SE_symm`, `SE_trans` | `SameExtension` is an equivalence relation |
| `BlockClass` | that equivalence, as a `Setoid` on pairs of starts |
| `InterlaceChords` | the adjacency: two support chords interlace |
| `InterlaceConnected` | "in one connected component", inductively |
| `interlaceChords_block` | an edge coalesces (`CrossingChordsCoalesce_ge2` + `AltF_sq`) |
| `connected_block` | a path coalesces (`interlaceChords_block` + `SE_trans`) |
| `InterlaceComponent_block` | each component sits in one extension class |
| `InterlaceComponents_ladder` | two chords of a component are two distinct parallel shifts of one ladder |

`InterlaceComponents_ladder` is the asked-for statement, with an inhabitant. It
is derived from `CrossingChordsCoalesce_ge2`, `AltF_sq`, `ladder_of_coalescing`
and the §1 equivalence, and from nothing else.

The reason it is weak: it is *automatic*. "Edges stay inside equivalence classes"
plus transitivity *always* implies "every component lies in one class", for any
equivalence relation. The packaged transitivity lemma carries no word content at
all --- `SameExtension_iff_pairEq` is `Finset` ext and nothing else.

## 3. Evidence (`scripts/verify_interlace_components_94.py`)

Exhaustive over all primitive `P2` words and every genuine traversal (every
`vtx`-preserving involution `f` with `J = f ∘ nextPos` a single `G`-cycle):
binary `G ≤ 10` (2720 traversals), ternary `G ≤ 7` (1050), plus binary `G ≤ 12`
(19232) for T3/T5.

| predicate | bin `≤10` | bin `≤12` | tri `≤7` |
|---|---|---|---|
| T1 edge ⟹ same block | 0 | --- | 0 |
| T2 component inside one block | 0 | --- | 0 |
| T3 block = component | 0 | 0 | 0 |
| T4 block is a parallel ladder | 0 | --- | 0 |
| T5 component contiguous in the support | 0 | 0 | 0 |
| T6 tour walks the support clockwise | **2720** | --- | **1050** |
| T7 component repaired by rotating its own points | **2790** | --- | **1050** |
| T8 tour preserves each component | **2790** | --- | **1050** |

T1--T5 hold: the components of the interlace graph **are** the maximal-extension
ladders, and each is cyclically convex in the support. So the component
description is *correct*, and the residual for `BBTLadder.LadderVertexCycle` is
**not** a graph-theoretic one.

T6--T8 fail, minimally at `G = 5`:

> `S = 00101`, `L = 3`, `f = (0)(1 3)(2 4)`, support `{1, 2, 3, 4}`, chords
> `{1, 3}` and `{2, 4}`. One component, one ladder, contiguous, genuine
> traversal --- and `J(0) = 3`, `J(1) = 4`, `J(2) = 1`, `J(3) = 2`, `J(4) = 0`,
> so **`J(4) = 0` leaves the component**.

`J(4) = 0` is the whole negative answer: **the traversal is not a permutation of
a single component's support points**, so no component can be repaired in
isolation. The T7 and T8 failure counts coincide exactly (2790 = 2790 binary,
1050 = 1050 ternary), and on the instances where `J` *does* preserve the
component there are **zero** T7 failures --- so T7 is not an independent
obstruction.

Note `S = 00101`, `L = 3` has `VertexCycleEq` **true** (it is the `00101`
witness of `BBTLadder.lean` §7, with a nonidentity `AltF`), so T6--T8 refute
*component independence* and the "the traversal walks the blocks in geometric
order" proof strategy, **not** `LadderVertexCycle`.

## 4. Precise residual

1. **Block ⟹ connected** (`T3`, `ShiftPairInterlace`): two parallel shifts of one
   pair interlace whenever the shift lies inside the pair's arc. Purely
   cyclic-order, `decide`-closed, zero failures --- **not proved**, and the first
   genuinely non-formal component-level lemma.
2. **`BBTLadder.LadderVertexCycle`** still has **no** inhabitant. §3 shows the
   missing step is not component-local. The invariant that survives is per-*ladder*
   vertex-invisibility (`AltF_vtx'` + `ladder_arc_eq`): a ladder's repair moves
   points **across** the two ends of its maximal repeat, not along an arc of the
   support.

This is evidence, not proof: the completeness of the search is not established in
the kernel. No `sorry`, no `admit`, no new axiom.