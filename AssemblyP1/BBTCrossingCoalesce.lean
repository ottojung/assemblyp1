import AssemblyP1.BBTLadder

/-!
# The word-level crossing/coalescence theorem of `#89`

This module isolates the **word-level** core of the ladder route: no
`EulerianCycle`, no `AltF`, no pull-back presentation.  Everything here is a
statement about a single circular word `S`, its `(L-1)`-mers, and the
*deterministic maximal extension* `maxPairStart` / `maxPairLen` of a pair of
starts.

## The theorem being reduced to

> **Crossing pairs coalesce.**  Let `S` be a primitive `P2` circular word read
> at length `L`, with `2 ≤ L ≤ G`.  Let `a ≠ b` and `c ≠ d` be two pairs of
> starts, each pair carrying a common `(L-1)`-mer, and suppose the four starts
> **interleave**.  Then the two deterministic maximal extensions **coincide**:
> the unordered pairs of extension starts
> `{maxPairStart a b, maxPairStart b a}` and
> `{maxPairStart c d, maxPairStart d c}` are equal.

This is `CrossingPairsCoalesce` below.  It is a `Prop` with **no inhabitant**;
§5 states the two ingredients it is reduced to --- beyond `SameExtension`,
which `AssemblyP1.BBTLadder` provides --- and keeps them clearly separate from
the theorems of §1--§4, which *are* proved.

It is the right target because it is *word-level* and *sufficient*:

* it applies to the support of any alternative traversal, since
  `AltF_vtx'` says the two ends of every support chord carry a common
  `(L-1)`-mer --- so `BBTLadder.CrossingChordsCoalesce` is an immediate
  corollary;
* the conclusion is about the **support block structure only**, and
  `BBTLadder.LadderVertexCycle` then turns blocks into `VertexCycleEq`.

It is also the *corrected* form of the statement refuted at `e89b1d42`.  What
is false is that crossing `(L-1)`-mer pairs have *interleaved* maximal
extensions (`BBTChords.raw_node_crossing_not_maximal`, `S = 00101`); what is
true is the opposite --- their maximal extensions **coalesce**.

## Why `P2` is load-bearing

Exhaustive search (`scripts/verify_ladder_blocks_89.py`, and the wider sweep
recorded in `docs/bbt-ladder-blocks-89.md` §1): over all primitive binary words
of length `≤ 10` there are 2534 crossing doubled-pair instances on `P2` words
and **zero** failures, and over all primitive ternary words of length `≤ 6`,
168 instances and **zero** failures.  Dropping `P2` while keeping primitivity,
1320 of 2304 binary instances and **all** 72 ternary instances fail.  So neither
hypothesis is decoration.  This is evidence; the completeness of the search is
not itself proved.

## What is proved here

* **§1** (`vtx_eq_iff`) read a `(L-1)`-mer equality as an agreement statement.
* **§2** (`three_starts_ne`) under `P2` and primitivity, three distinct starts
  cannot carry one `(L-1)`-mer.  This is the multiplicity cap
  (`P2.imp_nodeCount_le_two`, i.e. `R1`/`Lemma 1`) in the form the collision
  step needs.
* **§3** (`collision_forces_pair`) the collision step: if two doubled pairs meet
  at a common start, then they are the *same* unordered pair.  Combined with §2
  this is the load-bearing half of the "collision" case of
  `docs/arratia-shift-left-invariant-89.md` §1.
* **§4** (`vtx_maxPairStart`) the two extension starts of a repeated pair carry
  a common `(L-1)`-mer --- i.e. the head of a chord's backward list is again a
  chord, which is what lets the coalescence proof slide down to it.
* **§5** three `Prop`s with **no inhabitant**, and no others:
  - `CrossingPairsCoalesce` --- the target;
  - `SlidePreservesInterleaved` --- the one new cyclic-order fact, a statement
    about the shift coordinate alone (2490 instances checked, no failure);
  - `ShiftLeftPersistence` --- word-level; see its docstring for why it is not
    proved here.

  The docstring of `SlidePreservesInterleaved` records the full five-step
  coalescence proof and shows these three `Prop`s are the *whole* of what is
  missing.  Nothing in §1--§4 is unproved.

Two remarks on §5, added when this module was first compiled (it had been
excluded from `AssemblyP1.lean`, so nothing checked it).  The prose block
below introduces itself as the docstring of `InterleaveUntilCollision`; no
such name exists in the library, and the block is deliberately kept as a plain
comment rather than attached to a declaration.  The five-step reduction it
records is a **plan in prose**: no Lean term discharges it, and the two
`Prop`s it needs (`ShiftLeftPersistence`, `SlidePreservesInterleaved`) have no
inhabitant.  See `docs/` for the open status.

No `sorry`, no `admit`, no new `axiom`.
-/

namespace AssemblyP1.BBTCrossingCoalesce

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder

set_option maxHeartbeats 800000
-- Repository convention (cf. `BBTEulerian`): the auto-included
-- `[DecidableEq α]` section variable is not needed by every lemma here.  This
-- is a diagnostic about an unused name, not about a proof obligation.
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

/-! ## 1. A `(L-1)`-mer equality is an agreement statement -/

/-- **Two starts carry the same `(L-1)`-mer exactly when they agree on the
`L - 1` positions from their starts.**  This is `vtx` read off
`OrientedRigidity.nodeWindow`, and it is the form every step below uses. -/
theorem vtx_eq_iff {a b : Fin G} :
    vtx hG L S a = vtx hG L S b ↔
      ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) := by
  constructor
  · intro h d
    exact congrFun h d
  · intro h
    funext d
    exact h d

/-- **A start whose `(L-1)`-mer is `k` is one of the starts realising `k`.** -/
theorem mem_nodeStartsOf_vtx {k : Fin (L - 1) → α} {x : Fin G}
    (h : vtx hG L S x = k) : x ∈ nodeStartsOf hG S k := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact h

/-! ## 2. The multiplicity cap: three starts never share one `(L-1)`-mer -/

/-- **Three pairwise distinct starts cannot carry one `(L-1)`-mer.**  Under
`P2` and primitivity every `(L-1)`-mer is spelled at most twice
(`P2.imp_nodeCount_le_two`, i.e. `R1`/`Lemma 1` of
`docs/bbt-unique-eulerian-89.md` §4), and this is the form the collision step
of the shift-left argument needs. -/
theorem three_starts_ne {a b c : Fin G} (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S)
    (hab : vtx hG L S a = vtx hG L S b) (hac : vtx hG L S a = vtx hG L S c)
    (hne : a ≠ b) (hne' : a ≠ c) : b = c := by
  by_contra hcon
  have hbc : b ≠ c := by omega
  have hmem : ({a, b, c} : Finset (Fin G)) ⊆
      nodeStartsOf hG S (vtx hG L S a) := by
    intro x hx
    have hx3 : x = a ∨ x = b ∨ x = c := by simpa using hx
    rcases hx3 with h1 | h1 | h1
    · rw [h1]; exact mem_nodeStartsOf_vtx hG S rfl
    · rw [h1, hab]; exact mem_nodeStartsOf_vtx hG S rfl
    · rw [h1, hac]; exact mem_nodeStartsOf_vtx hG S rfl
  have hcard : ({a, b, c} : Finset (Fin G)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hne, hne', hbc, rfl⟩
  have hthree : 3 ≤ (nodeStartsOf hG S (vtx hG L S a)).card :=
    le_trans hcard.ge (Finset.card_le_card hmem)
  have hcap := P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 (vtx hG L S a)
  rw [card_nodeStartsOf] at hthree
  exact absurd hthree (by omega)

/-! ## 3. The collision step -/

/-- **A collision forces the two pairs to coincide.**  Suppose `a, b` and
`c, d` are pairs of *distinct* starts, each pair carrying a common
`(L-1)`-mer, and `c` coincides with `a`.  Then `d = b`, i.e. the two unordered
pairs are equal.

This is the "collision" alternative of the shift-left lemma
(`docs/arratia-shift-left-invariant-89.md` §1, case 2): at a collision the two
realisations of the repeated `(L-1)`-mer meet, and the multiplicity cap of §2
leaves no room for a *third* realisation, so the collision identifies the pairs
rather than producing a triple repeat.  Note what this does **not** need: it is
purely a statement about the fibre of one `(L-1)`-mer, and in particular it does
not need the two pairs to lie in different components. -/
theorem collision_forces_pair {a b c d : Fin G} (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hG L S a = vtx hG L S b) (hvcd : vtx hG L S c = vtx hG L S d)
    (hcoll : c = a) : b = d := by
  have hcad : vtx hG L S a = vtx hG L S d := by rw [← hcoll]; exact hvcd
  have had : a ≠ d := by simpa [hcoll] using hcd
  by_cases hbd : b = d
  · exact hbd
  · exact (three_starts_ne (a := a) (b := b) (c := d) hG S hL hLG hprim hP2
      hvab hcad hab had)

/-! ## 4. The extension starts carry a common `(L-1)`-mer -/

/-- **The two extension starts of a pair carry a common `(L-1)`-mer.**  The
deterministic maximal extension of a pair of distinct starts that agree on
`L - 1` positions is a maximal repeat of length `≥ L - 1`
(`maxPair_isRepeat`, i.e. `R1` at `n = 2`), and two copies of a repeat of length
`≥ L - 1` agree on their first `L - 1` positions --- which is exactly the
`(L-1)`-mer statement.  So the head of a chord's backward list is again a
chord, and the chord structure is what the coalescence proof slides along. -/
theorem vtx_maxPairStart {a b : Fin G} (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hab : a ≠ b)
    (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    vtx hG L S (maxPairStart hG S a b) = vtx hG L S (maxPairStart hG S b a) := by
  obtain ⟨hR, hℓ'⟩ := maxPair_isRepeat hG S hprim hab (by omega) (by omega) hag
  refine (vtx_eq_iff hG S).mpr fun d => ?_
  exact hR.2.2.2.1 ⟨d.val, lt_of_lt_of_le d.isLt hℓ'⟩

/-! ## 5. The target, and the one ingredient it is reduced to -/

/-- **The word-level crossing/coalescence theorem of `#89`**
(`CrossingPairsCoalesce`): two pairs of distinct starts of a primitive `P2`
word, each pair carrying a common `(L-1)`-mer, whose four starts interleave,
have the **same** deterministic maximal extension --- as an unordered pair of
extension starts.

This is a `Prop`; it is **not** an inhabitant.  See the module docstring for why
this, and not "`AltF = id`" and not start-level equality, is the target. -/
def CrossingPairsCoalesce (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), 2 ≤ L → L ≤ K →
    P2 hK L S → RepeatAdapter.IsPrimitive hK S →
    ∀ (a b c d : Fin K),
      a ≠ b → c ≠ d →
      vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
      Interleaved (mkGenome hK S) a b c d →
      SameExtension K hK S a b c d

/- **The combinatorial core of `CrossingPairsCoalesce`
(`InterleaveUntilCollision`): shift the pair `c, d` left, keeping `a, b` fixed.
As long as the shift causes no **collision** --- no endpoint of `c, d` meeting
`a` or `b` --- the four starts keep interleaving.

Why this is the whole remaining content.  Write `β = pairBack c d` and shift
`c, d` left by `t ≤ β`.  The `(L-1)`-mer equality of the pair survives the
shift, because a backward agreement of length `β` covers every position in
`[c - β, c)`.  Now measure interleaving by the shift coordinate: with `a` at
`0` and `b` at `s = sh a b`, the statement "`c - t` lies on the open arc from
`a` to `b`" is `0 < (sh a c - t) mod K < s`, which as a function of `t` is the
membership of `t` in the cyclic interval `[sh a c - s + 1, sh a c - 1]`, and
its two boundary points are `t ≡ sh a c` (that is `c - t = a`) and
`t ≡ sh a c - s` (that is `c - t = b`).  So the predicate is **constant on
every interval of `t` avoiding collisions**, and in particular

```text
  Interleaved a b c d   ∧   no collision in [0, t]   ⟹   Interleaved a b (c-t) (d-t).
```

This is a statement about the shift coordinate only; it mentions no word.  It
is what the shift-left iteration of
`docs/arratia-shift-left-invariant-89.md` §1 needs, and it is where the
`#89` proof is stuck.

Given `ShiftLeftPersistence`, `SlidePreservesInterleaved` and
`SameExtension` (and nothing else), `CrossingPairsCoalesce` follows.  The proof
is short, and it is worth writing out because it shows that **no further repeat
theory is needed** and that the *only* new cyclic-order ingredient is a
one-step slide lemma.

Let `k = L - 1 ≥ 1`, let `w = vtx hK L S` be the `(L-1)`-window labelling, and
call `{a, b}` with `a ≠ b` and `w a = w b` a **chord**.

1. **Fibres have size two.**  `P2` and primitivity give `w`'s fibres size `≤ 2`
   (`P2.imp_nodeCount_le_two`), so two chords sharing an endpoint are *equal*.
2. **The canonical extension is constant along a component.**  Form a graph on
   chords by joining `{a, b}` to `ρ {a, b} = {ρ a, ρ b}` whenever the latter is
   also a chord.  The `ρ`-orbit of a chord is a finite list
   `C_j = {a - j, b - j}`, `j ≤ β`, where `β` is the maximal backward agreement
   of the pair (`ShiftLeftPersistence` keeps `C_j` a chord, and `β` is where it
   stops), and the head of the list is exactly the chord
   `{maxPairStart a b, maxPairStart b a}` (`vtx_maxPairStart` plus
   `maxPairStart_eq`).  The canonical unordered extension is constant on the
   list, so it is constant on each connected component.  `Primitive` rules out a
   cyclic component, since a cycle would propagate `S x = S (x + (b - a))` round
   the whole circle, a nontrivial period.  So the components are paths, and the
   head of `C`'s component carries `C`'s canonical extension.
3. **Slides do not meet a chord of another component.**  If some `C_j` shared an
   endpoint with `D`, then by (1) `C_j = D`, so `D` is in `C`'s component.
4. **A slide preserves interleaving.**  `SlidePreservesInterleaved` says a
   one-step backward slide of one chord preserves `Interleaved` with the other,
   as long as neither the old nor the new endpoints meet the other chord.  By
   (3) that condition holds all the way down, so sliding `C` down to the head
   of its component gives a chord that still crosses `D`; sliding `D` down
   likewise gives a chord that still crosses that one.
5. **Contradiction.**  The two heads are `C`'s and `D`'s canonical extensions,
   which are maximal repeats of length `≥ L - 1` (`maxPair_isRepeat`).  They
   cross, so `P2`'s clause 2 --- read as `P2.imp_ExtCrossing` --- is violated.
   Hence `C` and `D` are in the same component, and by (2) they have the same
   canonical unordered extension: `SameExtension`.

So the two `Prop`s below plus `SameExtension` are the whole of what is missing.
`SlidePreservesInterleaved` is the one genuinely new cyclic-order fact, and it
is a statement about the shift coordinate only.
-/

/-- **The word-level half of what is missing** (`ShiftLeftPersistence`):
shifting a pair of starts left, as far as the two copies keep agreeing, keeps
the `(L-1)`-mer equality.

Stated for a plain shift amount `t` rather than for `pairBack c d`, because the
maximal backward agreement is the largest such `t` and the statement is monotone
in `t`; taking `t` to be that maximal backward agreement is exactly what makes
the shifted pair the pair of *extension starts* (`maxPairStart_eq`).

The obstacle to proving this here is a *visibility* one, not a mathematical one:
the predicate `P2RepeatResidual.backAgree` behind `pairBack`, `pairBack_ge` and
`pairBack_spec` is `private` to `AssemblyP1/P2RepeatResidual.lean`, so from this
module `pairBack` can be applied but its defining predicate cannot be named, and
`pairBack_ge` therefore cannot be applied.  The lemma belongs next to
`pairBack`, in that file.  This is a `Prop`; it is **not** an inhabitant. -/
def ShiftLeftPersistence (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) {a b : Fin K} (t : ℕ),
    t ≤ K →
    vtx hK L S a = vtx hK L S b →
    vtx hK L S (rotAdd hK (K - t) a) = vtx hK L S (rotAdd hK (K - t) b)

/-- **The one new cyclic-order fact** (`SlidePreservesInterleaved`): sliding one
chord one step backward preserves its interleaving with the other chord, as long
as neither the old nor the new endpoints meets an endpoint of the other chord.

This is a statement about the shift coordinate alone --- no word, no repeat.  It
is the only genuinely new combinatorial ingredient of the coalescence proof, and
step 4 of the plan above is exactly it, applied repeatedly along the backward
list.  Exhaustive search over all primitive binary words of length `≤ 9` and all
primitive ternary words of length `≤ 7` finds 2490 instances and no failure.

This is a `Prop`; it is **not** an inhabitant. -/
def SlidePreservesInterleaved (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (a b c d : Fin K),
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    rotAdd hK (K - 1) c ≠ a → rotAdd hK (K - 1) c ≠ b →
    rotAdd hK (K - 1) d ≠ a → rotAdd hK (K - 1) d ≠ b →
    Interleaved (mkGenome hK S) (rotAdd hK (K - 1) a) (rotAdd hK (K - 1) b)
      c d

end AssemblyP1.BBTCrossingCoalesce
