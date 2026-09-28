# `#89`: the word-level crossing/coalescence route, and the exact residual

This note records the current state of the **word-level** coalescence route for
issue `#89`: what is proved in the kernel, what the finite evidence says, and
precisely which statement is still missing.

Everything here is about a single circular word `S` of length `K`, read at
length `L` with `2 ≤ L ≤ K`, its `(L-1)`-mers, and the *deterministic maximal
extension* of a pair of starts

```text
  β := pairBack S a b                (maximal backward agreement of the pair)
  maxPairStart S a b := a - β        (the extension start of `a`)
  maxPairStart S b a := b - β        (the extension start of `b`)
  maxPairLen   S a b := pairFwd of the shifted pair
```

together with the two actual clauses of `P2` (`AssemblyP1/P2.lean`):

* **clause 1** — no maximal triple repeat of length `≥ L - 1`, which under
  primitivity gives node multiplicity `≤ 2`
  (`P2.imp_nodeCount_le_two`), i.e. every `(L-1)`-mer is spelled **at most
  twice**;
* **clause 2** — every interleaved maximal-repeat pair has a constituent of
  length `≤ L - 2`, which forbids two interleaved maximal repeats both of
  length `≥ L - 1` (`P2.imp_ExtCrossing`).

Both clauses are load-bearing, and neither is decoration.  Dropping clause 1
while keeping primitivity makes 1320 of 2304 binary crossing instances of
`CrossingPairsCoalesce` fail; dropping clause 2 while keeping clause 1 makes
**all** 72 ternary instances fail (`docs/bbt-ladder-blocks-89.md` §1).

## 1. The statement

`BBTCrossingCoalesce.CrossingPairsCoalesce` (`AssemblyP1/BBTCrossingCoalesce.lean`)
is the word-level target: for two pairs of distinct starts, each pair carrying
a common `(L-1)`-mer, whose four starts **interleave**, the two deterministic
maximal extensions coincide **as unordered pairs of starts**:

```text
  {maxPairStart a b, maxPairStart b a}  =  {maxPairStart c d, maxPairStart d c}
```

The unordered form is forced.  `Interleaved` is symmetric in `c, d`
(`SourceFaithfulIs.Interleaved` is `FourDistinct a b c d ∧ (InOpenArc a b c ↔
¬ InOpenArc a b d)`), so a hypothesis about `(a, b, c, d)` is a hypothesis
about `(a, b, d, c)`; the ordered conclusion
`maxPairStart a b = maxPairStart c d ∧ maxPairStart b a = maxPairStart d c` is
refuted by `S = 00101`, `G = 5`, `L = 3` at `a = 1, b = 3, c = 4, d = 2`.  The
unordered conclusion is `BBTLadder.SameExtension`, a shared abbreviation used
by both gaps, not a third gap.

`BBTLadder.CrossingChordsCoalesce` is the Eulerian-level restatement: in the
genuine `EulerianCycle` setting, two **crossing support chords** of
`f = AltF` carry the same extension.  It is an immediate corollary of the
word-level statement, because `BBTLadder.AltF_vtx'` gives `vtx a = vtx b` and
`vtx c = vtx d` for the two chords.

## 2. The two interfaces, in their corrected form

The earlier draft of this packet (`d6966a5`) reduced the target to two `Prop`s
with no inhabitant.  **Both of those `Prop`s are false as stated**, and both
are refuted here; the corrected forms are what the proof uses.

### 2.1 Backward chord persistence must be conditioned by `pairBack`

The earlier `ShiftLeftPersistence` quantified over **all** `t ≤ K`:

```text
  vtx a = vtx b  ∧  t ≤ K   ⟹   vtx (a - t) = vtx (b - t)          -- FALSE
```

**Refuted** by `S = 001`, `K = 3`, `L = 2`, `a = 0`, `b = 1`, `t = 1`: both
starts read the `1`-mer `0`, but `vtx 2 = 1 ≠ 0 = vtx 0`.  The predicate "the
shifted pair is still a chord" is *not* monotone in `t`, and the shift must be
bounded by the pair's own maximal backward agreement.

The corrected statement, and the one the proof uses, is

```text
  (C1)  vtx a = vtx b  ∧  t ≤ pairBack a b   ⟹   vtx (a - t) = vtx (b - t)
  (C2)  vtx (a - pairBack a b - 1) ≠ vtx (b - pairBack a b - 1)   (a ≠ b)
```

`(C1)` is a word-level consequence of `pairBack_spec` (a backward agreement of
length `pairBack` covers `[a - t, a)` for every `t ≤ pairBack`, and the original
`(L-1)`-mer covers the rest of the window).  `(C2)` is `pairBack_succ`: the two
copies are preceded by different symbols, so the pair cannot be slid one step
further.  Together they say that the **backward chain of a chord is exactly**
`{a - j, b - j}` for `0 ≤ j ≤ pairBack a b`, and that its head is precisely the
deterministic maximal extension `{maxPairStart a b, maxPairStart b a}`.

`(C1)` must be stated in `AssemblyP1/P2RepeatResidual.lean`, next to
`pairBack`: the predicate `backAgree` behind `pairBack`, `pairBack_ge` and
`pairBack_spec` is `private` to that file, so from `BBTCrossingCoalesce` the
`pairBack` can be *applied* but its defining condition cannot be *named*.

### 2.2 The slide lemma slides `c, d`, and the earlier one slid `a, b`

The earlier `SlidePreservesInterleaved` had its four hypotheses about the
predecessors of `c, d` while its conclusion slid `a, b` — the two were
mismatched, and the statement is **refuted** (take `a = 0, b = 6, c = 9, d = 3`
on a circle of ten: the hypotheses hold, the conclusion has `a' = c`).

The corrected interface slides the pair `c, d` and keeps `a, b` fixed, which is
the direction the shift-left induction actually runs in:

```text
  (S1)  Interleaved a b c d  ∧  c - 1, d - 1 ∉ {a, b}  ⟹  Interleaved a b (c-1) (d-1)
```

`(S1)` is a **purely cyclic-order** statement: it mentions no word.  The
open arc `(a, b)` and the open arc `(a-1, b-1)` have symmetric difference
exactly `{a-1, b-1}`, and the hypotheses exclude the two points in question;
so the alternation of `c, d` between the arcs — hence `Interleaved` — is
preserved.  It is iterated along the backward chain of `{c, d}` until that
chain's head is reached, and then, symmetrically, along the backward chain of
`{a, b}`.

## 3. The induction, and what it terminates in

Fix crossing chords `{a, b}` and `{c, d}`, and put `β = pairBack a b`,
`δ = pairBack c d`.  Run:

1. slide `c, d` left one step at a time for at most `δ` steps, using `(S1)`;
   by `(C1)` each intermediate pair is a chord;
2. if some shifted endpoint meets `a` or `b`, we are in the **collision**
   case: both pairs are then chords of the same `(L-1)`-mer sharing an
   endpoint, and clause 1 (multiplicity `≤ 2`) identifies them, so the two
   backward chains are the same chain and the heads coincide;
3. otherwise the head `C* = {c - δ, d - δ}` of the `c, d` chain is reached
   with `Interleaved a b C*` still holding; now slide `a, b` left, and again
   either collide (same conclusion) or reach the head `A* = {a - β, b - β}`
   with `Interleaved A* C*`;
4. but `A*` and `C*` are the two deterministic maximal extensions, each a
   maximal repeat of length `≥ L - 1 > L - 2` (`maxPair_isRepeat`), and they
   interleave, which clause 2 of `P2` forbids (`P2.imp_ExtCrossing`).

So the induction terminates in the collision case, and the collision case is
exactly the coalescence.

The finite evidence (`scripts/verify_coalesce_induction_89.py`, over all
primitive binary words of length `≤ 8` and primitive ternary words of length
`≤ 5`, all `2 ≤ L ≤ K`, all crossing doubled pairs) is that the replay of this
induction **always** terminates in step 2 or 3, i.e. never reaches step 4, and
that the collision step always yields `SameExtension`
(`scripts/verify_collision_head_89.py`: 3584 collisions, 0 non-coalescing).
`(C1)`, `(C2)`, `(S1)` and the target itself are checked by
`scripts/verify_crossing_coalesce_89.py`.

**This is evidence, not a proof: the completeness of the search is not itself
established in the kernel.**  The kernel content is the list in §4.

## 4. What is proved in the kernel

* `BBTCrossingCoalesce.vtx_eq_iff`, `three_starts_ne`, `collision_forces_pair`,
  `vtx_maxPairStart` — the four ingredients of §1--§4 of that module, all
  proved, none of them the target;
* `P2RepeatResidual.chord_shift_left` — the corrected `(C1)`, at the level of
  the `pairBack` where `backAgree` can be named;
* `P2RepeatResidual.not_chord_of_pairBack_succ` — the corrected `(C2)`;
* `P2RepeatResidual.pairBack_shift` — the head of a chord is reached at the
  shift predicted by `pairBack`, so the head is a function of the *chain* and
  not of the entry point; this is what makes the collision case conclude
  `SameExtension`;
* `BBTCrossingCoalesce.slide_Interleaved` — the corrected `(S1)`, a purely
  cyclic-order lemma;
* `BBTCrossingCoalesce.CrossingPairsCoalesce` — the target;
* `BBTLadder.CrossingChordsCoalesce` — the Eulerian corollary.

## 5. The residual

After the above, the remaining `#89` statement is **only** the global block
lemma `BBTLadder.LadderVertexCycle`: that a support which is a laminar family
of ladder blocks, each block vertex-invisible (`ladder_of_coalescing`,
`ladder_arc_eq`, `AltF_vtx'`), forces the vertex listing of the traversal to be
a rotation of the truth's.  It is *not* a repeat-theoretic statement: it needs
the geometric fact that the traversal walks the laminar blocks in the
geometric order, and it is the only thing standing between the coalescence
theorem and `VertexCycleEq`.  It is deliberately **not** attacked here, and it
remains a `Prop` with no inhabitant.
