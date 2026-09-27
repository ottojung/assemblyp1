# #89: the rematch / ladder layer for genuine `EulerianCycle`s

_This note supersedes §4 of `docs/bbt-unique-eulerian-89.md` (Lemma 2) and
§5--§6 of `docs/bbt-chord-rematch-89.md` in the light of the audit `e89b1d42`.
Kernel-checked on branch `agent/issue89-rematch-final2`, commits `c822b2a`
(adopting the R1/R2 layer of `1c67a14`) and `b8659f0` (the present module).
`AssemblyP1/BBTRematch`/`BBTLadder` contain no `sorry`, no `admit` and no new
axiom; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`
for every theorem named below.  Full `lake build` passes._

## 1. What the audit changed

`docs/bbt-unique-eulerian-89.md` §4 **Lemma 2** asked for:

> Two *doubled* pairs that interleave force two interleaved maximal repeats
> both of length `≥ K = L-1`.

**This is false**, and the audit `e89b1d42` pins down exactly why the first
attempt at the crossing step fails: on a *genuine* `EulerianCycle` of a
primitive `P2` word, two crossing raw pairs can have maximal extensions that
**coalesce** onto one and the same maximal repeat.  The smallest instance is
`S = 00101` at `G = 5`, `L = 3` (so `K = 2`), the crossing pairs
`{1,3}` (`01`) and `{2,4}` (`10`): the two-sided maximal extension of *both* is
the single maximal repeat `{1,3}` of length `3`.  `S = 0001001` at `G = 7`,
`K = 3` is the second instance.

So a crossing of two doubled chords is **not** a counterexample to
`thm:BBT`: it has to be *discharged*, not refuted.  The correct target, and the
one proved-to-be-the-right-shape statement in this packet, is

```text
LadderRotationGap:  a genuine EulerianCycle whose crossing transposition
                     pairs coalesce onto one maximal repeat still has the
                     vertex cycle of a rotation of the truth's.
```

equivalently: *non-`VertexCycleEq` forces a crossing pair with **interleaving**
extensions*.  The present module proves everything around that statement and
leaves it, precisely and in the corrected form, as §5 below.

## 2. What is proved (kernel-checked)

`AssemblyP1/BBTLadder.lean`, on top of `AssemblyP1.P2RepeatResidual` (the
`1c67a14` layer: `pairBack`/`pairFwd`/`maxPairStart`/`maxPairLen`,
`maxPair_isRepeat`, `P2.imp_nodeCount_le_two`, `P2.imp_ExtCrossing`) and
`AssemblyP1.BBTUniqueEulerian` (`EulerianCycle`, `AltF`, `VertexCycleEq`, the
innermost-chord step `not_visitsAll_of_innermost_chord`).

### 2.1 The support chords of `AltF` are involution orbits (§2 of the module)

| theorem | content |
| --- | --- |
| `sh_rotAdd` | the shift coordinate is invariant under a common rotation of the two starts, so *the maximal extension of a pair is a property of the pair* |
| `maxPairStart_eq`, `maxPairStart_rotAdd` | the deterministic extension start is the pair rotated back by its maximal backward agreement `pairBack`, and by the **same** `pairBack` at both ends (`pairBack_comm`) |
| `AltF_vtx'` | the `traverses` clause of `EulerianCycle`, read on the alternative traversal: `vtx (f q) = vtx q` |
| **`AltF_sq`** | **in the genuine Eulerian setting, under `P2` and primitivity, `f = AltF hG σ` is an involution** |
| `orbit_is_doubledPair`, `AltF_support_swap` | a two-element orbit of `f` is a *transposition of a doubled `(L-1)`-mer pair*: the two realisations of one branch object of the condensed multigraph, exchanged by `f` |

`AltF_sq` is the input the chord route was missing: the map induced by an
alternative traversal is a permutation, and `1c67a14` deliberately did not use
the Eulerian structure, so it could not observe that this permutation is an
**involution** whose orbits are *doubled* pairs.  The proof is the fibre
argument: `x`, `f x` and `f (f x)` all lie in the fibre of `vtx x`
(`AltF_vtx'`), injectivity of `f` (`AltF_bijective`) makes them pairwise
distinct unless `f (f x) = x`, and `P2.imp_nodeCount_le_two` bounds that fibre
by two.  Consequently the support of `f` is a set of genuine **chords** of
`BBTChords`, each chord being the two occurrences of one branch object.

### 2.2 A maximal repeat determines its own length (§3)

`isRepeat_len_unique`: two `SourceFaithfulIs.Genome.IsRepeat` at the *same* pair
of starts have the same length.  So "the two deterministic maximal extensions
coincide" is a statement about *one* maximal repeat, and
`ladder_len` (below) can conclude that the two `maxPairLen` values agree.

### 2.3 The rematch structure: a collapse is a **ladder** (§4)

`ladder_of_coalescing`:

> Let `a b c d p q : Fin G` with `a ≠ c`, and suppose two pairs of starts of
> the alternative traversal have the *same* deterministic maximal extension:
> `maxPairStart hG S a b = maxPairStart hG S c d = p` and
> `maxPairStart hG S b a = maxPairStart hG S d c = q`.  Then there are
> `ℓ ≠ ℓ'` with `a = p + ℓ`, `b = q + ℓ`, `c = p + ℓ'`, `d = q + ℓ'`.

together with

* `ladder_chord_identities`: `sh a b = sh c d = sh p q`, i.e. the two chords are
  **parallel** --- they have the same length, the length of the maximal repeat
  they both sit in;
* `ladder_len`: the two pairs have the same `maxPairLen`, and it is `≥ L-1`.

This is the "rematch" of the Ukkonen/P2 vocabulary, in the form the `#89`
route needs: the two chords of the alternative traversal are two **distinct
offsets of the same maximal repeat**, and the traversal moves both ends of each
chord by the same amount, so the two ends carry the same `(L-1)`-mer.

### 2.4 Why a ladder is benign (§5)

`repeat_copies_vtx` and `ladder_arc_eq`: if `(e, p, q)` is a maximal repeat of
the truth, i.e. the two occurrences agree over its whole length, and
`L-1 ≤ e`, then

```text
vtx (p + i) = vtx (q + i)      for every i with i + (L-1) ≤ e
```

so inside one maximal repeat the two copies --- and all their common shifts ---
spell the *same* vertices.  Combined with `AltF_vtx'` (each jump of `f` reads
the same vertex as staying put), a ladder is **invisible at the level of the
vertex cycle**.  This is the local content of the audited claim; what is missing
is the *global* statement, §5.

## 3. The picture, and where the global step bites

Write `f = AltF hG σ`, `J = f ∘ nextPos` (so `J` is the successor permutation of
the alternative traversal, and the `single` clause of `EulerianCycle` is that
`J` is a `G`-cycle).  Because `f` preserves the `(L-1)`-mer, a jump
`x-1 ↦ f x` reads the same vertex as the step `x-1 ↦ x`.  Hence:

* the alternative traversal is the truth's traversal with the steps
  `z ↦ z+1` *at the support points* replaced by `z ↦ f (z+1)`;
* cutting the circle at the support of `f` gives **blocks** (maximal runs of
  positions between consecutive support points), and the walk visits the blocks
  in the order of the permutation `Φ = f ∘ nextSupport` of the support;
* the vertex cycle read is therefore the truth's vertex sequence with those
  **blocks rearranged**.

`VertexCycleEq` therefore says: *that block rearrangement is vertex-compatible*.
§2.3--§2.4 supply the local reason a collapse is compatible; the global reason
that the rearrangement produced by `Φ` is compatible is the missing step.

The two known routes to it, both still open here:

1. **non-crossing + innermost chord** (`BBTUniqueEulerian.not_visitsAll_of_innermost_chord`):
   if the support chords were pairwise non-interleaved, there would be an
   innermost chord and the `single` clause would fail.  This is why
   `docs/bbt-unique-eulerian-89.md` §5 step 2 wanted a non-interleaving clause;
2. **the ladder is the whole support**: if all support chords lie in *one*
   maximal repeat (a single ladder), the block structure of the two copies is
   the same by `ladder_arc_eq`, and the rearrangement only permutes *equal*
   vertex blocks.

Note also that a "chord crossing" in `f` is *not* a counterexample to
`BBTChords.chord_lemma`-style non-crossing either: the two chords of a ladder
*do* cross (`{1,3}` and `{2,4}` in the `00101` instance), and they are
compatible with `P2` because their maximal extension is a single repeat.

## 4. Evidence

`scripts/verify_ladder_rematch_89.py` searches exhaustively over all primitive
circular words with `G ≤ 9` and alphabet `≤ 3`, all `2 ≤ L ≤ G`, and every
window-preserving **involution** of the starts whose `f ∘ nextPos` is a
`G`-cycle, i.e. every genuine alternative traversal in the sense of
`AssemblyP1.BBTEulerian`.  Reported output:

```text
maxG = 9, alphabet <= 3
  genuine-traversals                       192260
  identity-support                         174500
  nontrivial-support                         17760
  crossing-chords                           17760
  crossing-with-COLLAPSING-extensions       14130
  crossing-with-OTHER-extensions             5832
  crossing-with-INTERLEAVED-extensions          0
  ladders-1                                 12500
  ladders-2                                  5200
  ladders-3                                    60
  extension-len->=K                         36612
violations of the audited claim (COLLAPSE-NOT-ROTATION / NOT-ROTATION): 0
first instance of each crossing/collapse pattern:
  (no collapse, crossing)   ('01011', 5, 3, pairs (0,2),(1,4))
  (collapse, crossing)      ('00101', 5, 3, pairs (1,3),(2,4))
```

Reading of the census:

* **0** genuine traversals have crossing chords with *interleaving* extensions
  --- which is exactly `P2.imp_ExtCrossing` (`1c67a14`), now confirmed
  exhaustively on the genuine-Eulerian object rather than on arbitrary pairs;
* **14130** crossing chord pairs *coalesce* (§2.3, the ladder), and **5832**
  have extensions that are neither interleaved nor equal (disjoint or nested);
* **0** violations of the audited claim: in every one of the 192260 genuine
  traversals, including all 12908 with crossing *and* collapsing chords, the
  vertex cycle is a rotation of the truth's;
* the support of a genuine traversal with crossing chords lives in **one**
  maximal repeat in 12500 cases, in **two** in 5200 and in **three** in 60.  So
  the "single ladder" case is the generic one, but not the only one: a
  completion of `LadderRotationGap` in the single-ladder form alone would leave
  5260 instances untreated.

This is evidence, not a proof: the completeness of the search is not itself
proved.  The script is a check of the *statement* `LadderRotationGap` and of
§2.3--§2.5 on a large class, not a proof of either.

## 5. The remaining gap, in one place

`AssemblyP1.BBTLadder.LadderRotationGap` is a `Prop` with **no inhabitant**:

```text
LadderRotationGap L :=
  for every primitive P2 truth S, every read length L, every presentation σ of
  an alternative EulerianCycle of the (L-1)-mer multigraph of S, and every
  a b c d with f a = b, f b = a, f c = d, f d = c, a ≠ c, and
  maxPairStart a b = maxPairStart c d, maxPairStart b a = maxPairStart d c:
    VertexCycleEq S σ (refl)
```

With `P2.imp_ExtCrossing` (§4) and §2 of this note, this is the whole of the
uniqueness step: by §2.1 the support of `f` is a set of doubled-pair chords;
by §2.3 a crossing pair that does not coalesce is a *ladder* and its two ends
carry the same `(L-1)`-mer; `LadderRotationGap` then says the vertex cycle is a
rotation; and in the non-crossing case
`BBTUniqueEulerian.not_visitsAll_of_innermost_chord` rules out the alternative
cycle outright.

What has to be added to close it is the global block argument of §3: that the
block permutation `Φ = f ∘ nextSupport` moves only whole ladder pairs, or
equivalently that the two copies of each ladder offset cut off *equal* vertex
blocks.  The naive replacement --- "a crossing gives two *interleaved* maximal
extensions" --- is refuted (§1) and must not be used.

## 6. Two further corrections recorded here

* **`f = id` is false.**  `docs/bbt-unique-eulerian-89.md` §5 step 4 concludes
  `f = id` from "an innermost chord breaks the cycle".  On `S = 00101`,
  `G = 5`, `K = 2` the alternative traversal with `f = (1 3)(2 4)` is a genuine
  `EulerianCycle` (`f ∘ nextPos` is a `5`-cycle) and `f ≠ id`, yet its vertex
  cycle *is* a rotation of the truth's.  The correct conclusion of the whole
  argument is `VertexCycleEq`, not `f = id`; the non-identity is exactly the
  collapse phenomenon this note is about.
* **"support chords are non-interleaved" is false**, and cannot be the step 2
  of §5: a ladder's two chords cross by construction (§2.3), and the `00101`
  instance is a `P2` word.  Step 2 has to be the *global* statement of §3.
