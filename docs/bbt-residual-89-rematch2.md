# #89, branch `agent/issue89-rematch-final2`: the exact rematch residual

This note records (a) why the residual is **not** a tautology, with a
refuted shortcut and an exhaustive counterexample, (b) the new computational
evidence on where the `P2` hypothesis is load-bearing, and (c) the exact
combinatorial step that the maximal-repeat ladder route still has to prove.

## 0. Status of this branch

`AssemblyP1/BBTLadder.lean` (carried over from the WIP commit `8f61ad9`,
repaired and kernel-checked here) supplies the ladder layer:

* §1 the deterministic maximal extension of a pair of starts is the pair
  rotated back by its maximal backward agreement (`sh_rotAdd`,
  `maxPairStart_eq`, `maxPairStart_rotAdd`), so "two pairs have the same
  maximal extension" is a statement about two rotations of *one* pair;
* §2 under `P2` and primitivity the alternative traversal
  `f = AltF hG σ` is an **involution** whose orbits are transpositions of
  doubled `(L-1)`-mer pairs (`AltF_sq`, `orbit_is_doubledPair`,
  `AltF_support_swap`); this is the object the rematch step needs, and it is
  the step that justifies reading the support of `f` as a set of *chords*;
* §3 a maximal repeat determines its own length (`isRepeat_len_unique`);
* §4 **the ladder theorem** (`ladder_of_coalescing`,
  `ladder_chord_identities`, `ladder_len`): two pairs with the same
  deterministic maximal extension are two *distinct* rotations of the one
  pair `{p, q}`, and their chords are parallel;
* §5 **why a ladder is benign** (`ladder_arc_eq`): inside one maximal repeat
  the two shifted copies spell the same `(L-1)`-mers, so a ladder is
  invisible at the level of the vertex cycle.

## 1. A refuted shortcut, and why it matters

It is very tempting to read the `traverses` clause of
`BBTEulerian.EulerianCycle`

```lean
∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))
```

as already saying that the alternative traversal reads the `(L-1)`-mers in
the truth's cyclic order, i.e. as making
`BBTEulerian.VertexCycleEq` a tautology and hence discharging
`hPevzner` in `AssemblyP1.PopulationUniqueness` for free.

**That is false, and it was refuted before being used.**  Inducting on `i`
the step one needs is `σ (ρ (σ i)) = σ (ρ i)`, i.e. `σ i = i`, which is
precisely what is *not* known.  Concrete check: with `S = 001101`,
`E = 001011`, `G = 6`, `L = 3` (both words spell each of the six binary
3-mers exactly once, so they have the same complete `L`-spectrum) and the
matching `μ = [0, 4, 3, 1, 2, 5]` pairing equal 3-mers, the `traverses`
clause holds at every `i`, while the vertex cycles differ:

```text
truth    : 00 01 11 10 01 10
alternative (vtx ∘ μ): 00 01 10 01 11 10
```

which is not a rotation of the truth's cycle.  So `EulerianCycle` is a real
hypothesis and `VertexCycleEq` is a real conclusion.  (Concretely, the
"honest" version of the induction would need `σ ∘ ρ = Succ`, i.e. the
start-level successor of the alternative traversal to be the rotation —
which is the whole content of `thm:BBT` and is not a consequence of
`traverses`.)

## 2. The `P2` hypothesis is load-bearing, and the interleaved clause carries it

`scripts/verify_p2_spectrum_injective_89.py` (added in this branch) checks
exhaustively, for the binary alphabet and `G = 6, 7, 8, 9` and every
`2 ≤ L ≤ G`:

* **62** rotation classes share a complete `L`-spectrum with another
  rotation class, and **0** of those classes consist only of `P2` words: every
  collision is excluded by the repeat hypothesis.  So the theorem is *not*
  true without `Ukkonen`/`P2`, and the `EulerianCycleObstruction` residual
  cannot be discharged by any argument that drops the repeat clause;
* on the `P2` class the `L`-spectrum **is** injective up to rotation in
  every one of the 25 `(G, L)` pairs (e.g. `G = 9`: 512 `P2` word instances,
  60 spectrum classes, 0 collisions);
* the sample collision above is excluded by the **interleaved** clause of
  `P2`, not by the triple-repeat clause: `S = 001101` has interleaved
  maximal repeats `(e, a, b) = (2, 1, 4)` and `(2, 3, 5)`, and
  `E = 001011` has `(2, 1, 3)` and `(2, 2, 5)`.

This is evidence, not a proof: the completeness of the search is not itself
proved and `G ≤ 9` is small.  Its use is (i) to rule out the
"discharge the residual by weakening the hypothesis" direction, and (ii) to
predict that any completion must go through
`P2.interleaved`, i.e. through the *interleaving* side of the ladder
dichotomy rather than through the triple-repeat side.

## 3. The exact remaining step

Write `f = AltF hG σ`.  Under `P2` and primitivity, `BBTLadder.AltF_sq`
makes `f` an involution and `BBTLadder.orbit_is_doubledPair` makes every
orbit a transposition of a doubled `(L-1)`-mer pair, so the support of `f`
is a genuine chord system of the circle.  `BBTUniqueEulerian` has already
kernel-checked that a chord whose open arc is free breaks the cycle
(`EulerianCycle_no_innermost_chord`), so any remaining chord system must
have *crossing* chords.  The step still to be proved is therefore exactly:

> **Ladder/normalisation step.**  For two crossing transposition orbits of
> `f`, the deterministic maximal extensions of the two pairs either
> interleave --- which contradicts `P2.interleaved`, since both extension
> lengths are `≥ L - 1` by `P2RepeatResidual.maxPair_isRepeat` --- or
> coalesce into one maximal repeat, in which case
> `BBTLadder.ladder_of_coalescing` gives two parallel chords and
> `BBTLadder.ladder_arc_eq` shows the two copies spell the same
> `(L-1)`-mers, so the collapse is invisible at the level of the vertex
> cycle and cannot change `VertexCycleEq`.

What is *not* yet proved is the block-structure statement behind the second
alternative: that the chords of one coalescing group move whole
equal-vertex blocks, i.e. that the block permutation `f ∘ nextSupport` acts
on the set of ladder pairs rather than cutting across them.  The
exhaustive search `scripts/verify_ladder_rematch_89.py` (192260 genuine
traversals, `G ≤ 9`) found no counterexample and found the crossing chords
coalescing into one maximal repeat in 17628 cases and into two ladders in
118; the completeness of that search is not proved either.

Note the two independent axes that must be preserved in any completion:
* **doubling** (`P2.imp_nodeCount_le_two`, via `BBTLadder.AltF_sq`) is what
  makes `f` an involution, and
* **the Eulerian/single-circuit hypothesis** is what makes the traversal a
  single `G`-cycle (`Succ`),

so a statement about *raw* crossing pairs of an arbitrary involution is not
enough — the two benign "collapse" families recorded in
`docs/bbt-ladder-rematch-89.md` (`S = 00101`, `G = 5`, `K = 2`; and
`S = 0001001`, `G = 7`, `K = 3`) are exactly the instances where the naive
"crossing gives two interleaved maximal extensions" claim is false.
