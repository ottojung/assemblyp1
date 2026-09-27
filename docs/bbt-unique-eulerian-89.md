# #89: `thm:BBT` — uniqueness of the condensed Eulerian cycle

_Status (2026-09-27, branch `agent/issue89-direct-final`, commits `640135e`,
`082768a`, and the checkpoint after it): **the combinatorial half of `thm:BBT`
is proved in the kernel; the two repeat-theoretic lemmas it needs are not.**
`AssemblyP1.BBTEulerian.UniqueEulerianCycle` is *not* proved, `P2.BBTUniqueAt`
is *not* closed, and `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
still takes `(hBBT : BBTUniqueAt L)` as a hypothesis. No `sorry`, no `admit`, no
new axiom; `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound` for everything listed below. Full `lake build` passes.*

## 1. The statement to be proved

`AssemblyP1.BBTEulerian.UniqueEulerianCycle L`: for every `K`, every
`S : Fin K → α` with `Ukkonen hK L S`, and every traversal
`σ : Fin K ≃ Fin K` satisfying `EulerianCycle hK L S σ`, the vertex cycle of
`σ` is the truth's vertex cycle, i.e. `VertexCycleEq hK L S σ id`.

`EulerianCycle` has two clauses. The `single` clause
(`VisitsAll (fun x => σ (nextPos (σ.symm x))) (origin hK)`) is **automatic**:
the successor of a pull-back presentation is the conjugate
`σ ∘ rot₁ ∘ σ⁻¹` of the one-step rotation, hence a `G`-cycle, and
`pullback_isEulerianCycle` already proves it. So the hypothesis reduces to

```text
traverses  ∀ i, vtx (σ (nextPos i)) = vtx (nextPos (σ i))          (T)
```

and the whole content is: (T) forces the vertex cycle to be a rotation of the
truth's, under `Ukkonen`.

## 2. The master reformulation (kernel-checked, §2 of the module)

Write `ρ = nextPos`, `W = vtx` (the `(L-1)`-mer at a start), `K = L - 1`, and
let `Succ σ = σ ρ σ⁻¹` be the successor permutation *of the listing*
`σ 0, σ 1, …` (i.e. `Succ σ (σ i) = σ (i+1)`). Then (T) is exactly

```text
∀ x, W (Succ σ x) = W (ρ x)                                     (T')
```

Proved: `AssemblyP1.BBTUniqueEulerian.AltF_vtx`. Putting
`f := AltF hG σ = Succ σ ∘ prevPos`, (T') is `W (f q) = W q`; proved:
`AltF_bijective` (so `f` is a permutation). And `Succ_eq_altF` says
`f ρ = Succ σ`, so the alternative traversal is the `f ρ`-cycle and the `single`
clause is "`f ρ` is a `G`-cycle". This is the classical reformulation: `f`
chooses, at every step, *which occurrence* of the next `(L-1)`-mer to visit.

The listing lemmas (`succ_listing'`, `listing_surj`) are re-derived from the
reduction's own `altSucc_iterate`, so no new word semantics is introduced.

## 3. The combinatorial core: an innermost chord breaks the cycle (§4)

`AssemblyP1.BBTUniqueEulerian.not_visitsAll_of_innermost_chord`:

> Let `f : Fin G → Fin G` be a bijection, and let `a, b` satisfy
> `1 ≤ sh a b < G`, `f b = a`, and `f x = x` for every `x` on the open arc
> from `a` to `b`. Then `x ↦ f (ρ x)` is **not** a `G`-cycle, i.e.
> `¬ VisitsAll (fun x => f (nextPos x)) (origin hG)`.

This is **strictly sharper** than the "minimal gap" version sketched below in
§5: it assumes neither that `f` is an involution nor that its chords are
globally non-crossing. A single chord whose open arc contains no support point
already breaks the cycle. Proof: read the orbit of `a` in the shift coordinate;
it is the sub-cycle `0, 1, …, sh a b − 1, 0`, of length `sh a b < G`. The
orbit of the origin meets `a` (surjectivity of the iterate map), so that length
is a period of the circle, contradiction. Two ingredients are needed to land
this in the form `EulerianCycle` uses — "being a single `G`-cycle does not
depend on the base point" — and are proved separately in §4.1 of the module:

```text
iterate_G_eq : VisitsAll J (origin hG) → Bijective J → J^[G] (origin hG) = origin hG
iterate_mod   : J^[G] x = x → ∀ m, J^[m] x = J^[m % G] x
```

The shift coordinate makes the arc combinatorics elementary (§3 of the module):
`sh a (rotAdd t a) = t % G`, and

```text
inArc_iff : InArc hG a b x ↔ 0 < sh hG a x ∧ sh hG a x < sh hG a b
```

*definitionally*, because `BBTChords.InArc` is already stated with the
coordinate `sh`. So the "chords of a non-crossing configuration" of §5 are
intervals of `sh`, and no separate chord theory is needed.

The identification with the repository's own object is §5 of the module:
`EulerianCycle_no_innermost_chord` — *an alternative Eulerian cycle cannot
have an innermost chord of `f`*. So the combinatorial content of `thm:BBT` is
now in the kernel, with the two repeat-theoretic inputs below removed.

## 4. The two remaining lemmas

**Lemma 1 (multiplicity; the triple-repeat clause of `Ukkonen`).** Three
distinct starts spelling the same `(L-1)`-mer, not congruent modulo the least
period `p` of `S`, extend to a maximal triple repeat of length `≥ K`. Hence
under `Ukkonen` every `(L-1)`-mer occurs **at most twice** in the primitive
case, and starts congruent modulo `p` spell the same `(L-1)`-mer.

**Status update (2026-09-27): the primitive half of Lemma 1 is now proved in
the kernel**, and it is not a re-derivation: the two-sided extension engine is
`RepeatAdapter.extend_triple` (reached only through
`¬ RepeatAdapter.HasLongTripleRepeat`), the conversion to the source-faithful
predicate is `AssemblyP1.P2.noLongTripleRepeat` (`7794603`) and
`BridgingBridge.isTripleRepeat_of_maximalTriple`, and the multiplicity
conclusion is `RepeatAdapter.primitive_nodeCount_le_two`. The module
`AssemblyP1/P2Multiplicity.lean` composes them and adds only the primitivity
bridge `IsPrimitive.shiftPrimitive` (ported from `1c67a14`), so that the
hypothesis is the paper's own:

```text
PopulationReduction.IsPrimitive S + P2 hG L S + 2 ≤ L ≤ G
  ⟹  ∀ k : Fin (L-1) → α, nodeCount (L := L) hG S k ≤ 2
```

(`P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive`, axiom-clean.)
The **periodic** alternative of Lemma 1 --- the `p`-congruence clause --- is
outside the population target and is not proved here. The period-arithmetic
input for it is in place and kernel-checked
(`period_of_agree_all`, `agree_all_of_period`, `least_period_dvd`,
`leastPeriod_dvd_period`, `leastPeriod_dvd_G`, `sh_add`, `sh_dvd_trans`,
`cyc_of_period`, `vtx_eq_of_sh`).

The one-sided version is **false**, and the counterexample is worth recording
because it dictates the shape of the correct statement: for
`S = 012012012`, `G = 9`, `K = 3`, the three starts `0, 3, 6` all spell `012`,
and *all three preceding symbols* (2, 2, 2) and *all three following symbols*
(0, 0, 0) are equal, so there is no maximal triple repeat at that triple at
all. This is the `p = 3` case, and it is precisely the second alternative of
Lemma 1: `sh 0 3 = 3` and `leastPeriod = 3`. Both maximality clauses of
`IsTripleRepeat` must be handled by a *joint* two-sided extension, not one
after the other.

**Lemma 2 (the crossing clause, a.k.a. the "rematch" step).** ~~Two *doubled*
pairs that interleave force two interleaved maximal repeats both of length
`≥ K`.~~ **FALSE; see `docs/bbt-ladder-rematch-89.md`.**

The correct statement is the *rematch* one, and it is a **discharge** rather
than a refutation.  On a genuine `EulerianCycle` of a primitive `P2` word two
crossing doubled pairs can have maximal extensions that **coalesce** onto one
and the same maximal repeat --- the instance is `S = 00101`, `G = 5`, `L = 3`,
crossing pairs `{1,3}` and `{2,4}`, both extending to the single maximal repeat
`{1,3}` of length `3` --- and in every such instance the vertex cycle is still a
rotation of the truth's (exhaustively checked in
`docs/bbt-ladder-rematch-89.md` §4: 192260 genuine traversals, 0 violations).
A crossing of doubled chords is therefore not a counterexample to `thm:BBT`; it
is the *ladder* configuration, and it has to be shown benign.

What is kernel-checked in `AssemblyP1.BBTLadder.lean`, on top of the
deterministic pair-extension layer of `1c67a14` (`maxPairStart`, `maxPairLen`,
`P2.imp_ExtCrossing`):

* `AltF_sq`: in the genuine Eulerian setting under `P2` and primitivity the
  alternative traversal `f = AltF hG σ` is an **involution**, and
  `orbit_is_doubledPair`: its two-element orbits are *doubled* `(L-1)`-mer
  pairs, i.e. the two realisations of one branch object;
* `ladder_of_coalescing`, `ladder_chord_identities`, `ladder_len`: two such
  orbits with the *same* deterministic maximal extension are two **distinct
  rotations of the one pair** `{p, q}` (`a = p + ℓ`, `b = q + ℓ`,
  `c = p + ℓ'`, `d = q + ℓ'`, `ℓ ≠ ℓ'`), with equal chord length
  `sh a b = sh c d = sh p q` and a common extension length: a collapse of two
  chords onto one maximal repeat is exactly a **ladder**;
* `ladder_arc_eq`: inside one maximal repeat the two (and their common) shifted
  copies spell the *same* `(L-1)`-mers, so a ladder is invisible at the level
  of the vertex cycle.

The remaining step is `AssemblyP1.BBTLadder.LadderRotationGap`, a `Prop` with
no inhabitant: a genuine `EulerianCycle` whose crossing transposition pairs
coalesce has the vertex cycle of a rotation of the truth's.  Its local content
is what is listed above; its global content --- that the block permutation
`Φ = f ∘ nextSupport` of the support is vertex-compatible --- is open.  Two
consequences for §5 of this file are recorded in
`docs/bbt-ladder-rematch-89.md` §6: step 2 ("the support chords are pairwise
non-interleaved") is **false**, and step 4 ("hence `f = id`") is **false** --- on
`S = 00101` the genuine traversal `f = (1 3)(2 4)` is not the identity while its
vertex cycle is a rotation of the truth's.  The correct conclusion of the whole
argument is `VertexCycleEq`.

Note that Lemma 2 is a statement about *node* pairs while §3 is a statement
about *block* pairs, and it is exactly this mismatch that the refutation
exploits: the blocks of two crossing node pairs need not interleave. This is
why the chord route was abandoned and the innermost-chord form of §3 adopted.

## 5. Why these two lemmas are the whole remainder

With §3 in hand the argument is four lines:

1. Under `Ukkonen` + Lemma 1, every `(L-1)`-mer occurs at most twice, so `f`
   (a label-preserving permutation) is a product of disjoint transpositions,
   one per doubled pair.  In the genuine Eulerian setting this is
   `BBTLadder.AltF_sq`, which gives the involution directly.
2. ~~Under `Ukkonen` + Lemma 2, the support chords of `f` are pairwise
   non-interleaved.~~ **FALSE**: a ladder's two chords cross by construction
   (`docs/bbt-ladder-rematch-89.md` §6).  The correct step 2 is the global block
   statement `BBTLadder.LadderRotationGap` (a collapse forces the vertex cycle
   to be a rotation), which is open.
3. A non-crossing configuration of chords on a circle has an *innermost* chord:
   a chord `(a, b)` whose open arc contains no support point. (Equivalently,
   take the chord minimising the number of support points on one of its arcs.)
4. §3 says an innermost chord makes `f ρ` not a `G`-cycle, contradicting the
   `single` clause of `EulerianCycle`. Hence `f = id`, i.e. `Succ σ = ρ`, i.e.
   `σ i = rotAdd (σ 0) i`, and therefore `W (σ i) = W (rotAdd (σ 0) i)`, which
   is `VertexCycleEq hK L S σ id` with `k = σ 0`.
   **Correction** (`docs/bbt-ladder-rematch-89.md` §6): `f = id` is **false**.
   On `S = 00101`, `G = 5`, `K = 2`, the genuine `EulerianCycle` with
   `f = (1 3)(2 4)` has `f ρ` a `G`-cycle, `f ≠ id`, and its vertex cycle *is* a
   rotation of the truth's.  Steps 2--3 apply only in the non-crossing case; the
   crossing case is the ladder case and has to be discharged, not refuted.

Because `W` is `p`-periodic and `f` preserves `W`, the non-primitive case only
requires the weaker conclusion `σ i ≡ σ 0 + i (mod p)`, which the same four
steps give once Lemma 1 is read in its `p`-congruence form. `L ≤ 1` is
vacuous (`vtx` has empty domain, so all `vtx` agree).

## 6. What this file does and does not do

**Does:** §1 (window + period arithmetic, with the WIP's broken `leastPeriod`
repaired), §2 (the master reformulation, kernel-checked), §3 (the shift
coordinate and the arc), §4 (the innermost-chord cycle-breaking step, in the
form `EulerianCycle` uses), §5 (the identification with `EulerianCycle`).

**Does not:** Lemma 1 and Lemma 2 above, hence
`BBTEulerian.UniqueEulerianCycle`, hence `EulerianCycleObstruction`, hence
`P2.BBTUniqueAt`. No `sorry`, no `admit`, no new axiom.

## 7. Evidence for the unproved part

`scripts/verify_eulerian_cycle_uniqueness_89.py` searches exhaustively over all
circular words, all read lengths, and all traversals of the multigraph,
filtered by Ukkonen's condition. Its traversal notion is the *multigraph*
one (consecutive `(K)`-mers are shifts of one another, and the successor is a
`G`-cycle), which is the condensed-graph reading of `thm:BBT`; it is **not**
the pull-back presentation `σ` of `AssemblyP1.BBTEulerian`, so it explores
strictly more traversals than the formalized statement and is correspondingly
stronger evidence. Reported output:

```text
G = 2 … 10, alphabet size 2, K = 1 … 4, all words satisfying Ukkonen,
all label-preserving permutations f with f ∘ ρ a G-cycle:
no traversal whose vertex cycle is not a rotation of the truth's.
```

The same search **without** the `Ukkonen` filter does produce failures — e.g.
`S = 001001`, `G = 6`, `K = 1`, listing `0 3 1 2 4 5`, whose label sequence
`000011` is not a rotation of `001001` — so the hypotheses are load-bearing.
This is evidence, not a proof: completeness of the search is not itself proved.
