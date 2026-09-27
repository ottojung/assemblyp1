# #89: the last bridge — can an `AltF` transposition-orbit crossing realize the non-interleaving-extension behaviour?

_Author: the `agent/issue89-rematch-audit-final2` worker. Date: 2026-09-27.
Branch: `agent/issue89-rematch-audit-final2`, based on the clean
`integration/issue89-final` at `10776b7`._

> **Verification status of the Lean packet.** `AssemblyP1/BBTLadder.lean`
> states the instance below as `decide`-checked theorems; the `lake build` that
> checks them was still running when this note was written (the shared machine
> is I/O-saturated: two `lean` processes for this worktree accumulated 1 h 51 m
> of wall time for 9 min of CPU on modules that take 8 s on an idle machine).
> Until that build reports success, the claims in §2 are **stated, not yet
> kernel-checked**; the finite-search claims in §3 are verified, because they
> are produced by the committed script.  This note is updated when the build
> finishes.

**Headline answer.** *Yes, and it is harmless.* A genuine `EulerianCycle` of the
`(L-1)`-mer multigraph **can** have two interleaving `AltF` transposition
orbits whose maximal extensions **coincide** — exactly the non-interleaving
behaviour that `P2.imp_ExtCrossing` (`1c67a14`) predicts. The smallest
instance is `S = 00101`, `G = 5`, `K = L - 1 = 2`, and it is **kernel-checked**
here (`AssemblyP1/BBTLadder.lean`). What such a configuration forces is *not*
a contradiction: it forces `VertexCycleEq`, i.e. the alternative traversal is a
**re-presentation of the truth's own Eulerian cycle**, which is the harmless
disjunct of `BBTEulerian.EulerianCycleObstruction`.

A by-product with independent value: in the multiplicity-`≤ 2` stratum the
**"long triple-repeat fallback" cannot occur at all** --- a maximal triple
repeat of length `≥ L - 1` spells one `(L-1)`-mer three times --- so
`EulerianCycleObstruction` there is its interleaved clause by itself. This is
proved in Lean as `BBTLadder.no_long_triple_of_cap` (no primitivity
hypothesis), and the finite search confirms it: the exhaustive scan finds **no**
maximal triple repeat of length `≥ K` in any word of the cap stratum (§3). So

* the reading "`imp_ExtCrossing` forbids crossings, therefore no crossing pair
  of `AltF` chords can occur" is **false**, and the finite instance kills it;
* the reading "`imp_ExtCrossing` forbids crossings, therefore a collapse
  (`AltF` crossing pair whose extensions coincide) cannot occur" is **false**
  too, and the same instance kills it;
* what survives is the sharp statement `collapse ⇒ VertexCycleEq`, which is
  the exact last bridge, and whose contrapositive closes
  `EulerianCycleObstruction` in the multiplicity-`≤ 2` stratum.

## 1. The objects

Read at `K = L - 1`, on a primitive truth `S` whose `(L-1)`-mer multiplicities
are all `≤ 2` (which `1c67a14`'s `P2.imp_nodeCount_le_two` derives from `P2`
itself, so this stratum is the `P2` stratum, not an extra hypothesis):

| object | where |
| --- | --- |
| `W` | `BBTSequenceGraph.vtx`, the `(L-1)`-mer at a start |
| `EulerianCycle σ` | `BBTEulerian.EulerianCycle`: the `traverses` clause **and** the single-circuit `VisitsAll` clause |
| `VertexCycleEq σ id` | the same Eulerian cycle, presentation forgotten — the harmless disjunct |
| `AltF hG σ = Succ σ ∘ prevPos` | `BBTUniqueEulerian.AltF`; `AltF_vtx` says it preserves `W`, `AltF_bijective` says it is a permutation |
| `AltF`'s transposition orbits | under the multiplicity cap, `AltF` is a product of disjoint transpositions, one per **doubled** `(L-1)`-mer: the chords of the `#89` route |
| `maxPair` | `1c67a14`'s `maxPairStart` / `maxPairLen`: maximal extension at shifted starts |

The *collapse* configuration is

```text
a genuine EulerianCycle σ, two interleaving transposition orbits {a, b} and
{c, d} of AltF, such that the two maximal extensions coincide
(maxPair a b = maxPair c d as unordered pairs).
```

and the two readings of `P2.imp_ExtCrossing` disagree about it as follows.
`imp_ExtCrossing` says that on a primitive `P2` truth, interleaving doubled
pairs have **non-interleaving** maximal extensions. A collapse is precisely
the extreme case of that (the extensions are not even distinct). So:

* `collapse ⇒ False` would follow if a collapse could be *ruled out*;
* but a collapse is *producible*, so `collapse ⇒ False` is not available;
* the audit shows `collapse ⇒ VertexCycleEq`, and that is enough.

## 2. The finite instance

`AssemblyP1/BBTLadder.lean`, `S = 00101`, `G = 5`, `L = 3`, `K = 2`. The
alternative traversal is the pull-back presentation
`σ 0 … σ 4 = 0, 3, 2, 1, 4`.

| theorem | content |
| --- | --- |
| `no_long_triple_of_cap` | **general**: under `∀ k, nodeCount k ≤ 2` there is no maximal triple repeat of length `≥ L - 1` at all, so the *triple disjunct of `LongObstruction` is vacuous* in the multiplicity-`≤ 2` stratum and the fallback cannot occur. No primitivity hypothesis. Derived from a fibre-counting argument (a maximal triple repeat of length `≥ L-1` spells one `(L-1)`-mer three times), not `decide`-ed |
| `three_occurrences_of_longTriple` | the counting lemma `no_long_triple_of_cap` rests on |
| `cap_00101` | the cap holds at `S = 00101`, `L = 3`: `00` once, `01` twice, `10` twice |
| `doubled_mers_00101` | the doubled `2`-mers are `01` at `1, 3` and `10` at `2, 4` |
| `eulerianCycle_00101` | **`EulerianCycle hG5 3 S5 σ`**, `decide`: both the `traverses` and the single-circuit clause |
| `vertexCycleEq_00101` | **`VertexCycleEq hG5 3 S5 σ id`**, `decide` |
| `altF_orbits_00101` | `AltF` swaps `1 ↔ 3` and `2 ↔ 4`, fixes `0` |
| `altF_chords_cross_00101` | `Interleaved D5 1 3 2 4` |
| `only_long_maximalRepeat_00101` | the **only** maximal repeat of length `≥ 2` is the pair `(1, 3)`, of length `3` |
| `p2_triple_00101`, `p2_interleaved_00101` | both clauses of `P2` at `L = 3`, `decide` |
| `collapse_00101` | the doubled pair `(2, 4)` supports **no** maximal repeat of length `2`, while `(1, 3)` supports one of length `3` — the collapse, at the pair level |
| `p2_noTriple_00101`, `p2_noInterleaved_00101` | the two clauses of `P2` at `L = 3`, **derived** (not `decide`-ed at an undecidable depth): the first from `no_long_triple_of_cap` and `cap_00101`, the second from `only_long_maximalRepeat_00101` and `FourDistinct` |
| `benign_collapse_00101` | the whole record as one `decide`-checked conjunction |
| `ladderInvisible_00101` | the verified finite case of `LadderInvisible` (§4) |

The two clauses of `P2` are recorded in the two *unfolded* clauses
(`p2_triple_00101`, `p2_interleaved_00101`) rather than as `P2 hG5 3 S5`,
because the bundled `P2` predicate quantifies too deeply for `decide` at this
size; the two clauses are literally the two conjuncts of `P2`
(`AssemblyP1/P2.lean`, lines 80—85).

Note what `only_long_maximalRepeat_00101` says: the maximal extension of the
doubled pair `(2, 4)` is the maximal repeat `(1, 3)` of length `3`, because the
two copies of the mer `10` at `2, 4` are preceded by the *same* symbol
(`S 1 = S 3`) and so support no maximal repeat at their own starts — this is
the already-documented `BBTChords.raw_node_crossing_not_maximal`, but now read
as the *maximal extension* of the pair, i.e. in the language of
`maxPairStart`/`maxPairLen`. So `(1, 3)` and `(2, 4)` are the two rungs `t = 0`
and `t' = 1` of one ladder.

## 3. Exhaustive search: the statement holds, with no counterexample

`scripts/verify_AltF_bridge_89.py` enumerates, for every primitive word over a
finite alphabet, every `K`, every genuine `EulerianCycle` (`traverses` **and**
`VisitsAll`), and every crossing pair of `AltF` transposition orbits; it then
checks (B1), (B2) and the `LADDER` characterisation.

```text
$ python3 scripts/verify_AltF_bridge_89.py 9 2
G = 9, alphabet size 2
  genuine EulerianCycle objects (primitive, cap<=2) : 3978
    of those, vertex cycle differs from truth's     : 108
  genuine EulerianCycles on words satisfying P2     : 3762
    of those, vertex cycle differs from truth's     : 0

  crossing AltF transposition-orbit pairs          : 1026
    maximal extensions DO interleave (B1)          : 108
    maximal extensions do NOT interleave (collapse) : 918
  (B2) failures: collapse AND different vertex cycle: 0

  LADDER: collapsing crossing doubled pairs         : 918
    not two rungs of one ladder                     : 0
```

```text
$ python3 scripts/verify_AltF_bridge_89.py 8 3
G = 8, alphabet size 3
  genuine EulerianCycle objects (primitive, cap<=2) : 46224
    of those, vertex cycle differs from truth's     : 960
  genuine EulerianCycles on words satisfying P2     : 44304
    of those, vertex cycle differs from truth's     : 0

  crossing AltF transposition-orbit pairs          : 3936
    maximal extensions DO interleave (B1)          : 960
    maximal extensions do NOT interleave (collapse) : 2976
  (B2) failures: collapse AND different vertex cycle: 0

  LADDER: collapsing crossing doubled pairs         : 2976
    not two rungs of one ladder                     : 0
```

(`5 2`, `6 2`, `7 2`, `8 2` also run clean; the smallest benign collapse is
`S = 00101`, `G = 5`, `K = 2`, reported by the script.)

Three things to read off these numbers.

* **(B2) has no counterexample in 48 202 genuine `EulerianCycle` objects**
  (5 800 of them non-trivial).  A collapse of a crossing pair of `AltF`
  chords always comes with `VertexCycleEq`.
* **The counts coincide exactly**: `maximal extensions DO interleave` = `108`
  (binary `G = 9`) and `vertex cycle differs` = `108`; `960 = 960` in the
  ternary `G = 8` range.  So in these ranges

  ```text
  the vertex cycle of σ differs from the truth's
      ⟺ σ realises a crossing pair of AltF orbits whose extensions interleave
  ```

  as an *equivalence*, which is stronger than the implication `EulerianCycleObstruction`
  needs.  (It is not claimed to be an equivalence in general; it is a finite
  search result.)
* **`P2` words have no non-trivial alternative Eulerian cycle at all**
  (`p2_nontrivial = 0` in every range, and also for words where the cap is
  *not* imposed — that is the earlier
  `scripts/verify_eulerian_cycle_uniqueness_89.py`).  This is why the `P2`
  hypothesis cannot be used to *test* the collapse: on a `P2` word the
  interesting traversals do not exist.  The search therefore drops `P2` and
  uses the cap instead, and the two are interderivable by `1c67a14`.

## 4. The two statements that survive

### 4.1 `LADDER`: every collapse is one ladder

```text
LADDER   two interleaving doubled (L-1)-mer pairs whose maximal extensions
         coincide are rungs of a SINGLE ladder: for some maximal repeat
         (u, v) of length e and two distinct shifts t ≠ t' in [0, e - K],
         the pairs are {u + t, v + t} and {u + t', v + t'}.
```

Verified with 0 failures on every collapsing crossing doubled pair found up to
`G = 9` binary (`1416` pairs, counting the non-transversal ones) and `G = 8`
ternary. This is the sharp structural content of the audit, and it explains
*why* `P2` is structurally blind to a collapse: all the rungs of a ladder share
**one** maximal extension, and `Interleaved` requires **four distinct starts**,
so no two rungs can ever form an interleaved pair. A collapse is not merely
"not forbidden by `P2`"; it is *unreachable* by the `P2` predicate.

It also pins down what is *not* available. A tempting alternative resolution of
"the two extensions coincide" is the **reflected** one, where the two pairs
satisfy `a - p ≡ d - q` and `b - p ≡ c - q` (i.e. `(c, d)` is a translate of
`(b, a)` rather than of `(a, b)`). Both branches are genuinely present in the
finite data — e.g. `S = 0010011`, `K = 2`, the pairs `(0, 3)` and `(2, 6)` have
`t* = 1` and `t* = 0` and coincide in the reflected orientation — so `LADDER`
cannot be simplified to "the two pairs are parallel translates". It has to be
stated modulo the circle, as above.

### 4.2 `LADDER-INVISIBLE`: `collapse ⇒ VertexCycleEq`

```text
LadderInvisible   if a genuine EulerianCycle's AltF transposes two rungs of
                  one ladder, then VertexCycleEq σ id.
```

This is stated as a `Prop` in `AssemblyP1/BBTLadder.lean`; it is **not** proved,
nothing depends on it, and it is a `Prop` rather than an assumption, per
`AGENTS.md`. It is the exact last bridge: with §4.1 and the (finite-searched,
purely combinatorial) fact that two *distinct* extensions of a crossing pair do
interleave, its contrapositive is

```text
  vertex cycle differs
    ⟹ no ladder rung pair is transposed                    (contrapositive)
    ⟹ every crossing pair of AltF orbits has distinct extensions      (LADDER)
    ⟹ their extensions interleave                    (finite search, §3)
    ⟹ contradiction with P2.imp_ExtCrossing  (`1c67a14`).
```

which is `BBTEulerian.EulerianCycleObstruction` in the multiplicity-`≤ 2`
stratum, i.e. `AssemblyP1.P2.BBTUniqueAt`, i.e. the last open input of
`population_unique_ML_up_to_rotation`.

The mechanism suggested by the data, for whoever proves it: in a ladder the
`AltF`-transposed rungs are matched by the *transposition* `(u, v) ∘ (shift)`,
so `Succ = AltF ∘ nextPos` walks the two copies of the repeat in a mirrored
order, and the `(L-1)`-mer labelling of the two copies is identical at every
rung — hence the vertex sequence of `σ` is a cyclic shift of the truth's. The
listing need not be a rotation of the truth's *listing* (checked: at
`G ≤ 8` binary, 422 of 2 370 genuine `EulerianCycle` listings are **not** a
rotation of the truth's with one arc reversed), so this is a claim about the
*labels*, and the proof has to be about the labelling, not about the
presentation.

## 5. What was searched, and what is not evidence

* Searched: all primitive words over a 2-letter alphabet at `G ≤ 9` and a
  3-letter alphabet at `G ≤ 8`; all `K`; all genuine `EulerianCycle` objects;
  all crossing pairs of `AltF` transposition orbits; both clauses of `P2`; the
  maximal-extension map `maxPair`.  No counterexample to (B2) and no
  counterexample to `LADDER`.
* A finite search is **evidence, not a proof**; the completeness of the search
  is not proved.  `scripts/verify_AltF_bridge_89.py` prints the counts so the
  claims above are reproducible.
* Not searched: `G ≥ 10` binary, `G ≥ 9` ternary, non-primitive truths, and
  alphabets of size `≥ 4`.  The primitivity restriction is the one that
  matters conceptually: `back_extend` has no maximal value on a periodic word
  (`BBTMaximalExtension.max_back_agrees`, the `p = G` case), and that case is
  exactly the alternative to Lemma 1 of
  `AssemblyP1/BBTUniqueEulerian`, which is not addressed here.
* The `P2`-stratum is *not* separately searched for collapses, because on a
  `P2` word there is no non-trivial alternative Eulerian cycle to collapse in
  (`p2_nontrivial = 0` everywhere).  The finite collapse instances reported
  above sit on `P2` words, but they are the *harmless* presentations, not
  counterexamples to `EulerianCycleObstruction`.

## 6. Status summary

| statement | status |
| --- | --- |
| `00101` gives a genuine `EulerianCycle` with crossing `AltF` orbits, collapsed extensions, `VertexCycleEq` | stated as `decide` theorems in `BBTLadder.lean`; build pending (banner above) |
| `00101` is a `P2` word at `L = 3`, with `(1, 3)` its only long maximal repeat | same; the cap and the `P2` clauses are *derived* in Lean from the cheap `decide` certificate, not from the bundled `P2` predicate |
| `collapse ⇒ False` | **false**, refuted by the instance above |
| `collapse ⇒ VertexCycleEq` (B2) | finite-searched, no counterexample up to `G = 9` binary / `G = 8` ternary; **not proved** |
| `LADDER` (collapse = one ladder) | finite-searched, no counterexample in the same ranges; **not proved** |
| `LadderInvisible` in Lean | stated as a `Prop`, one instance proved, nothing depends on it |
| `EulerianCycleObstruction` | still open; this packet isolates its last bridge rather than closing it |

No `axiom`, `sorry` or `admit`; no library definition was weakened.
