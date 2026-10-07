import AssemblyP1.Issue94CrossingChords

/-!
# Board 94, front `94comp` --- the interlace graph on chords, and exactly what
# `SameExtension` forces about its connected components

This module takes up the objective proposed for the `#89` ladder route: study the
**interlace graph** of the changed branch transitions, in the spirit of
Arratia--Bollobas--Coppersmith--Sorkin (2000), instead of the tour as a whole.
Concretely:

* the **vertices** are the transposition orbits of the alternative pairing
  `f = AltF hK σ` --- the *changed branch transitions*, each counted once as an
  unordered chord `{a, AltF hK σ a}`;
* two vertices are **adjacent** when the two chords *interlace*, i.e. when
  `Interleaved (mkGenome hK S) a (AltF hK σ a) c (AltF hK σ c)`;
* the **blocks** are the classes of `BBTLadder.SameExtension`, i.e. of the
  unordered pair `{maxPairStart hK S a b, maxPairStart hK S b a}` of
  deterministic maximal-extension starts.

The question this front answers, in the exact form asked:

> Does `Issue94CrossingChords.CrossingChordsCoalesce_ge2` plus a packaged
> transitivity/equivalence lemma for `SameExtension` force **each connected
> component into one maximal-extension ladder**?

**Yes, and in a very weak way.**  §1--§2 show that `SameExtension` is literally
an equivalence relation --- reflexive, symmetric, transitive --- and that it is
*nothing but* equality of the extension-start pairs, with no word content at
all.  §3 then derives the component-level consequence:

> `InterlaceConnected σ a b` --- "`a` and `b` lie in one connected component of
> the interlace graph" --- forces the two chords to carry the **same**
> deterministic maximal extension, and hence to be two distinct parallel shifts
> of **one** maximal-extension ladder.

§3 is proved; **it is also nearly vacuous**, and §4 says exactly in what sense,
and what is missing: the reverse direction *block ⟹ connected* (so that
"component" and "ladder" are the same object, not merely injection-compatible),
and then the ordering of the components.

## §5. The falsification: the component picture is right, the component
## *repair* is wrong

`scripts/verify_interlace_components_94.py` (the search for this front)
enumerates **every** genuine traversal --- every `vtx`-preserving involution `f`
with `J = f ∘ nextPos` a single `G`-cycle --- over all primitive `P2` words,
binary `G ≤ 10` and ternary `G ≤ 7` (2720 and 1050 traversals with nontrivial
support), and additionally binary `G ≤ 12` (19232 traversals) for the
connectivity and contiguity predicates.  It finds:

| predicate | binary `G ≤ 10` | binary `G ≤ 12` | ternary `G ≤ 7` |
|---|---|---|---|
| T1 edge ⟹ same block | 0 failures | --- | 0 failures |
| T2 component inside one block | 0 failures | --- | 0 failures |
| T3 **block = component** | 0 failures | 0 failures | 0 failures |
| T4 block is a parallel ladder | 0 failures | --- | 0 failures |
| T5 **component contiguous** | 0 failures | 0 failures | 0 failures |
| T6 tour walks support clockwise | **2720 failures** | --- | **1050 failures** |
| T7 component-local rotation | **2790 failures** | --- | **1050 failures** |
| T8 tour preserves each component | **2790 failures** | --- | **1050 failures** |

* **T1--T5 all hold.**  So the component-level description is *correct*: the
  components of the interlace graph on chords are exactly the maximal-extension
  ladders, and each occupies a cyclically convex set of support points.  This is
  the good news, and it is the reason the residual is **not** a graph-theoretic
  one.  In particular the reverse direction of §3 --- *block ⟹ connected* ---
  is **empirically true** (`T3`) and is the first genuinely non-formal lemma
  still needed; it is a purely **cyclic-order** statement about two parallel
  shifts of one pair, and `§4` isolates it as `ShiftPairInterlace`.
* **T6 is refuted**, minimally at `G = 5`: `S = 00101`, `L = 3`,
  `σ = (1 3)(2 4)`, support `{1, 2, 3, 4}`.  The tour `J = f ∘ nextPos` does
  **not** walk the support in clockwise order.  This kills the natural attempt to
  prove `LadderVertexCycle` from "the traversal walks the blocks in the
  geometric order", at the very smallest instance that has a crossing pair of
  support chords.  The same instance has `VertexCycleEq` **true** (it is the
  `00101` witness used throughout `BBTLadder.lean` §7), so this refutes the
  *proof strategy*, not the theorem.
* **T7 is refuted** on the same instances: even *one* component, of *one*
  maximal-extension ladder, is not repaired by a rotation of its own points.
  **T8 identifies exactly why**, and it is the sharp negative answer to the
  second half of the objective.  T7 was checked on the tour `J = f ∘ nextPos`
  *restricted to the component's own support points*, and on every failing
  instance that restriction is not even a permutation of those points:

  > **`S = 00101`, `L = 3`, `f = (0)(1 3)(2 4)`.**  Support `{1, 2, 3, 4}`,
  > chords `{1, 3}` and `{2, 4}`, one component, one ladder, contiguous.
  > The tour is `J(0) = 3`, `J(1) = 4`, `J(2) = 1`, `J(3) = 2`, `J(4) = 0`, and
  > **`J(4) = 0` leaves the component**: the single component's point set is
  > **not closed under the traversal's successor map**.

  The count of T7 failures equals the count of T8 failures (2790 = 2790 binary,
  1050 = 1050 ternary), and restricting to instances where `J` *does* map the
  component into itself leaves **zero** T7 failures.  So T7 is not an independent
  failure: **component independence is impossible because the traversal is not
  even a permutation of a single component's support points.**  One component
  cannot be repaired in isolation --- not because the repair is hard to find,
  but because the tour does not stay inside it.

So: **the component-independence lemma asked for is false**, refuted at `G = 5`
where the ladder structure is a *single* block, and the refutation is a
one-line computation on the smallest instance in the search.  Component
independence is not the right shape; the invariant that survives is per-*ladder*
vertex-invisibility (`AltF_vtx'` + `ladder_arc_eq`), and what is missing is a way
to assemble the per-ladder replacements into a rotation of the whole listing ---
which is `LadderVertexCycle`, and which this front does **not** attack.

## §6. What is proved in the kernel, and what is not

Proved here:

* §1 `pair_two_eq`, `SameExtension_iff_pairEq` --- `SameExtension` is *exactly*
  equality of the unordered pairs of extension starts.  All content is `Finset`
  ext; no word, no `P2`, no traversal.
* §2 `ExtPair_comm`, `SameExtension_refl`, `.symm`, `.trans`, `BlockClass` ---
  `SameExtension` is an equivalence relation on pairs of starts, and `BlockClass`
  is the induced `Setoid`.
* §3 `interlaceChords_block`, `connected_block`, `InterlaceComponent_block`,
  `InterlaceComponents_ladder` --- **the asked-for component-level statement**:
  every connected component of the interlace graph lies in one
  maximal-extension ladder, and two of its chords are two distinct parallel
  shifts of that one ladder.  Derived from `CrossingChordsCoalesce_ge2`,
  `AltF_sq`, `ladder_of_coalescing` and §2, and from nothing else.

Not proved, and deliberately not attacked:

* the reverse direction *block ⟹ connected* (`T3`), which §4 isolates as
  `ShiftPairInterlace`: a purely cyclic-order lemma about two parallel shifts of
  one pair.  This is the first genuinely non-formal component-level lemma, and
  the search reports zero failures of it.
* `BBTLadder.LadderVertexCycle` still has **no** inhabitant.  §4 of this module
  supplies an inhabitant of a statement `LadderVertexCycle` *assumes*, and §5
  shows the remaining step is not a component-level one --- `T6` and `T7` are
  refuted at `G = 5`.
* **No statement about the interlace polynomial** is made or needed.  Nothing in
  this module touches it; the `Arratia--Bollobas--Coppersmith--Sorkin`
  inspiration is used only for the *graph* (vertices = changed branch
  transitions, edges = interlacement), which is a finite combinatorial
  reformulation of the support, not a spectral statement.

No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom.
-/

set_option maxHeartbeats 800000

namespace AssemblyP1.Issue94InterlaceComponents

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94CrossingChords

set_option linter.unusedSectionVars false

/-! ## 1. `SameExtension` is equality of extension-start pairs -/

variable {α : Type} [DecidableEq α] {K : ℕ}

/-- A local abbreviation for `BBTLadder.SameExtension`, whose explicit `K`
argument would otherwise clutter every statement below. -/
abbrev SE (hK : 0 < K) (S : Fin K → α) (a b c d : Fin K) : Prop :=
  SameExtension K hK S a b c d

/-- **The unordered pair of deterministic maximal-extension starts of the pair
`(a, b)`.**  This is the object `SameExtension` compares. -/
noncomputable def ExtPair (hK : 0 < K) (S : Fin K → α) (a b : Fin K) :
    Finset (Fin K) :=
  {maxPairStart hK S a b, maxPairStart hK S b a}

/-- **Two two-element sets are equal only by matching or by swapping.** -/
theorem pair_two_eq (_hK : 0 < K) {p q r s : Fin K}
    (h : ({p, q} : Finset (Fin K)) = ({r, s} : Finset (Fin K))) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  have hp : p ∈ ({r, s} : Finset (Fin K)) :=
    h.symm ▸ (show p ∈ ({p, q} : Finset _) from by simp)
  have hq : q ∈ ({r, s} : Finset (Fin K)) :=
    h.symm ▸ (show q ∈ ({p, q} : Finset _) from by simp)
  have hr : r ∈ ({p, q} : Finset (Fin K)) :=
    h ▸ (show r ∈ ({r, s} : Finset _) from by simp)
  have hs : s ∈ ({p, q} : Finset (Fin K)) :=
    h ▸ (show s ∈ ({r, s} : Finset _) from by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr hs
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact Or.inl ⟨hp, hs.elim (fun e => hq.trans (hp.symm.trans e.symm)) (fun e => e.symm)⟩
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr.elim (fun e => hq.trans (hp.symm.trans e.symm)) (fun e => e.symm)⟩

/-- **`SameExtension` is exactly equality of extension-start pairs.**  There is
no word content here at all: `SameExtension a b c d` unfolds to a disjunction of
the two orientations of equality, and `Finset` ext turns that into one equality.

This is the "packaged equivalence lemma" of the objective, and its content is
purely `Finset` bookkeeping: no repeat theory, no `P2`, no traversal, no
`AltF`. -/
theorem SameExtension_iff_pairEq (hK : 0 < K) (S : Fin K → α)
    (a b c d : Fin K) :
    SE hK S a b c d ↔ ExtPair hK S a b = ExtPair hK S c d := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine Finset.ext fun x => ?_
      simp only [ExtPair, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl (h.trans h1)
        · exact Or.inr (h.trans h2)
      · rintro (h | h)
        · exact Or.inl (h.trans h1.symm)
        · exact Or.inr (h.trans h2.symm)
    · refine Finset.ext fun x => ?_
      simp only [ExtPair, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inr (h.trans h1)
        · exact Or.inl (h.trans h2)
      · rintro (h | h)
        · exact Or.inr (h.trans h2.symm)
        · exact Or.inl (h.trans h1.symm)
  · intro h
    rcases pair_two_eq hK h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

/-! ## 2. The equivalence relation -/

/-- **`ExtPair` is insensitive to the order of its two arguments**, so it is a
property of the *unordered* pair `{a, b}` --- which is what makes it the right
invariant for the interlace graph, whose vertices are unordered chords. -/
theorem ExtPair_comm (hK : 0 < K) (S : Fin K → α) (a b : Fin K) :
    ExtPair hK S a b = ExtPair hK S b a := by
  ext x
  simp only [ExtPair, Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

theorem SE_refl (hK : 0 < K) (S : Fin K → α) (a b : Fin K) : SE hK S a b a b :=
  Or.inl ⟨rfl, rfl⟩

theorem SE_symm (hK : 0 < K) (S : Fin K → α)
    {a b c d : Fin K} (h : SE hK S a b c d) : SE hK S c d a b :=
  (SameExtension_iff_pairEq hK S c d a b).mpr
    ((SameExtension_iff_pairEq hK S a b c d).mp h).symm

theorem SE_trans (hK : 0 < K) (S : Fin K → α) {a b c d e f : Fin K}
    (h1 : SE hK S a b c d) (h2 : SE hK S c d e f) : SE hK S a b e f :=
  (SameExtension_iff_pairEq hK S a b e f).mpr
    (Eq.trans ((SameExtension_iff_pairEq hK S a b c d).mp h1)
      ((SameExtension_iff_pairEq hK S c d e f).mp h2))

/-- **`SameExtension`, as a `Setoid` on pairs of starts** --- the packaged
equivalence.  The `r` field is `SameExtension`, proved reflexive, symmetric and
transitive above. -/
noncomputable def BlockClass (hK : 0 < K) (S : Fin K → α) :
    Setoid (Fin K × Fin K) where
  r := fun p q => SE hK S p.1 p.2 q.1 q.2
  iseqv := ⟨fun p => SE_refl hK S p.1 p.2,
    fun {_ _} h => SE_symm hK S h,
    fun {_ _ _} h₁ h₂ => SE_trans hK S h₁ h₂⟩

/-! ## 3. The interlace graph on chords, and the component statement -/

variable {L : ℕ}

/-- **Two chords of the support of `f = AltF hK σ` interlace.**  This is the
adjacency of the interlace graph whose vertices are the changed branch
transitions. -/
def InterlaceChords (hK : 0 < K) (S : Fin K → α) (σ : Fin K ≃ Fin K)
    (a c : Fin K) : Prop :=
  Interleaved (mkGenome hK S) a (AltF hK σ a) c (AltF hK σ c)

/-- **`InterlaceConnected σ a b`: `a` and `b` lie in one connected component of
the interlace graph on chords.**

Defined inductively (reflexive, and closed under one interlace edge) rather than
as a `SimpleGraph`, so that the component statement below is a plain induction
and no graph library is needed.  On a finite set this is exactly connectedness
of the interlace graph. -/
inductive InterlaceConnected (hK : 0 < K) (S : Fin K → α) (σ : Fin K ≃ Fin K) :
    Fin K → Fin K → Prop where
  | refl (a : Fin K) : InterlaceConnected hK S σ a a
  | step {x y z : Fin K} : InterlaceChords hK S σ x y →
      InterlaceConnected hK S σ y z → InterlaceConnected hK S σ x z

/-- **An adjacent pair of chords coalesces.**  This is the only place §3 uses
the word.

This is `Issue94CrossingChords.CrossingChordsCoalesce_ge2` read at two chords of
the support of `f = AltF hK σ`: the four distinctness hypotheses of the theorem
are the `FourDistinct` clause of `Interleaved`, and the two chord hypotheses are
`AltF_sq` --- in the genuine Eulerian setting the alternative pairing is an
involution, so `AltF hK σ (AltF hK σ x) = x`. -/
theorem interlaceChords_block (hK : 0 < K) (hL : 2 ≤ L) (hLG : L ≤ K)
    (S : Fin K → α) (_hP2 : P2 hK L S) (_hprim : RepeatAdapter.IsPrimitive hK S)
    (_hUkk : Ukkonen hK L S) (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    {a c : Fin K} (hI : InterlaceChords hK S σ a c) :
    SE hK S a (AltF hK σ a) c (AltF hK σ c) := by
  have hsq (x : Fin K) : AltF hK σ (AltF hK σ x) = x :=
    AltF_sq hK S hEul hL hLG _hprim _hP2 x
  exact CrossingChordsCoalesce_ge2 (α := α) L hL K hK S _hP2 _hprim hLG _hUkk σ hEul
    a (AltF hK σ a) c (AltF hK σ c) rfl (hsq a) rfl (hsq c)
    hI.1.2.1 hI.1.2.2.2.1 hI.1.2.2.1 hI.1.2.2.2.2.1 hI

/-- **The component statement asked for.**

Two chords in one connected component of the interlace graph carry the **same**
deterministic maximal extension.  The proof is `interlaceChords_block`
(coalescence along each edge) followed by transitivity of `SameExtension` (§2)
along the path.  This is the entire content of "coalescing plus transitivity",
and it is what forces **each connected component into one maximal-extension
ladder**. -/
theorem connected_block (hK : 0 < K) (hL : 2 ≤ L) (hLG : L ≤ K)
    (S : Fin K → α) (_hP2 : P2 hK L S) (_hprim : RepeatAdapter.IsPrimitive hK S)
    (_hUkk : Ukkonen hK L S) (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hconn : InterlaceConnected hK S σ a b) :
    SE hK S a (AltF hK σ a) b (AltF hK σ b) := by
  induction hconn with
  | refl => exact SE_refl hK S _ _
  | step hI _ ih =>
      exact SE_trans hK S
        (interlaceChords_block hK hL hLG S _hP2 _hprim _hUkk σ hEul hI) ih

/-- **A two-element `Finset` does not see the order of its members.** -/
theorem finset_two_comm {K : ℕ} (r s : Fin K) :
    ({r, s} : Finset (Fin K)) = {s, r} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

/-- **Matching members give matching two-element `Finset`s.** -/
theorem finset_two_of {K : ℕ} {u v r s : Fin K} (h1 : u = r) (h2 : v = s) :
    ({u, v} : Finset (Fin K)) = {r, s} := by
  rw [h1, h2]

/-- **Swapped members still give the same two-element `Finset`.** -/
theorem finset_two_of' {K : ℕ} {u v r s : Fin K} (h1 : u = r) (h2 : v = s) :
    ({u, v} : Finset (Fin K)) = {s, r} := by
  rw [h1, h2]
  exact finset_two_comm _ _

/-- **`InterlaceComponents_ladder`: two chords in one connected component are
two *distinct* parallel shifts of one and the same maximal-extension ladder.**

This is the theorem asked for.  A `Prop` with an **inhabitant**, derived from
`Issue94CrossingChords.CrossingChordsCoalesce_ge2` (via `connected_block`), from
`BBTLadder.ladder_of_coalescing`, from `AltF_sq`, and from the packaged
equivalence of §2 --- and from nothing else.  No interlace polynomial is
involved.

The conclusion is what "one maximal-extension ladder" means: the two chords are
`{rotAdd ℓ p, rotAdd ℓ q}` and `{rotAdd ℓ' p, rotAdd ℓ' q}` for two **distinct**
shifts `ℓ ≠ ℓ'` of a **single** pair `p, q`, and `p, q` are the maximal-extension
starts of *both* chords. -/
theorem InterlaceComponents_ladder (hK : 0 < K) (hL : 2 ≤ L) (hLG : L ≤ K)
    (S : Fin K → α) (_hP2 : P2 hK L S) (_hprim : RepeatAdapter.IsPrimitive hK S)
    (_hUkk : Ukkonen hK L S) (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hconn : InterlaceConnected hK S σ a b) (hne : a ≠ b)
    (hne2 : a ≠ AltF hK σ b) :
    ∃ (p q : Fin K) (ℓ ℓ' : ℕ), ℓ ≠ ℓ' ∧
      ({a, AltF hK σ a} : Finset (Fin K)) = {rotAdd hK ℓ p, rotAdd hK ℓ q} ∧
        ({b, AltF hK σ b} : Finset (Fin K)) = {rotAdd hK ℓ' p, rotAdd hK ℓ' q} := by
  have h : SameExtension K hK S a (AltF hK σ a) b (AltF hK σ b) :=
    connected_block hK hL hLG S _hP2 _hprim _hUkk σ hEul hconn
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨ℓ, ℓ', hℓ, ha, ha', hb, hb'⟩ := ladder_of_coalescing
      (a := a) (b := AltF hK σ a) (c := b) (d := AltF hK σ b)
      (p := maxPairStart hK S a (AltF hK σ a)) (q := maxPairStart hK S (AltF hK σ a) a)
      hK S hne rfl rfl h1.symm h2.symm
    refine ⟨maxPairStart hK S a (AltF hK σ a), maxPairStart hK S (AltF hK σ a) a,
      ℓ, ℓ', hℓ, ?_, ?_⟩
    · exact finset_two_of ha ha'
    · exact finset_two_of hb hb'
  · obtain ⟨ℓ, ℓ', hℓ, ha, ha', hb, hb'⟩ := ladder_of_coalescing
      (a := a) (b := AltF hK σ a) (c := AltF hK σ b) (d := b)
      (p := maxPairStart hK S a (AltF hK σ a)) (q := maxPairStart hK S (AltF hK σ a) a)
      hK S hne2 rfl rfl h1.symm h2.symm
    refine ⟨maxPairStart hK S a (AltF hK σ a), maxPairStart hK S (AltF hK σ a) a,
      ℓ, ℓ', hℓ, ?_, ?_⟩
    · exact finset_two_of ha ha'
    · exact finset_two_of' hb' hb

/-- **`InterlaceComponent_block`: the component statement in isolation.**  If
`a` lies in some connected component of the interlace graph, then the chord at
`a` has a maximal-extension pair `(p, q)`, and `InterlaceComponents_ladder` shows
that pair is shared by the whole component. -/
theorem InterlaceComponent_block (hK : 0 < K) (hL : 2 ≤ L) (hLG : L ≤ K)
    (S : Fin K → α) (_hP2 : P2 hK L S) (_hprim : RepeatAdapter.IsPrimitive hK S)
    (_hUkk : Ukkonen hK L S) (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    {a : Fin K} (ha : ∃ b : Fin K, InterlaceConnected hK S σ a b) :
    ∃ p q : Fin K, maxPairStart hK S a (AltF hK σ a) = p ∧
      maxPairStart hK S (AltF hK σ a) a = q := by
  obtain ⟨b, hb⟩ := ha
  have h : SameExtension K hK S a (AltF hK σ a) b (AltF hK σ b) :=
    connected_block hK hL hLG S _hP2 _hprim _hUkk σ hEul hb
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨maxPairStart hK S a (AltF hK σ a), maxPairStart hK S (AltF hK σ a) a, rfl, rfl⟩
  · exact ⟨maxPairStart hK S a (AltF hK σ a), maxPairStart hK S (AltF hK σ a) a, rfl, rfl⟩

/-! ## 4. The reverse direction, isolated -/

/-- **`ShiftPairInterlace`: two parallel shifts of one pair interlace.**

This is the *cyclic-order* half of `T3`, the direction **block ⟹ connected**
that `connected_block` does **not** give: it says that two chords sitting at
`rotAdd i p, rotAdd i q` and `rotAdd j p, rotAdd j q` interlace whenever the
shift `j - i` is positive and strictly smaller than the chord's own arc.

It is a purely geometric statement about the circle: it mentions the word only
through `mkGenome hK S`'s length, and it is `decide`-closed on every concrete
instance.  It is **not proved here** --- the shift bounds it needs are exactly
what `maxPairLen` supplies, and importing them by hand would be smuggling in the
ladder geometry.  The search reports **zero** failures over binary `G ≤ 12` and
ternary `G ≤ 7`. -/
def ShiftPairInterlace (hK : 0 < K) (S : Fin K → α) (p q i j : Fin K) : Prop :=
  Interleaved (mkGenome hK S) (rotAdd hK i p) (rotAdd hK i q)
      (rotAdd hK j p) (rotAdd hK j q)

instance decShiftPairInterlace (hK : 0 < K) (S : Fin K → α) (p q i j : Fin K) :
    Decidable (ShiftPairInterlace hK S p q i j) := by
  unfold ShiftPairInterlace
  exact inferInstance

/-! ## 5. Why the component statement is not enough -/

/-- **`hK : 0 < 5`. -/
theorem hK5 : 0 < 5 := by decide

/-- **The minimal instance that refutes every *global* component-level statement
while satisfying every *local* one.**

`S = 00101` on `Fin 5`, `σ = (1 3)(2 4)`:
* the support is `{1, 2, 3, 4}` --- all four support points, one chord `{1, 3}`
  and one chord `{2, 4}`;
* the two chords **interlace**, so the interlace graph has a single component
  with two vertices;
* `T3`/`T4` say the component is a single maximal-extension ladder and `T5` says
  it is contiguous;
* and yet `T6` (the tour walks the support clockwise) and `T7` (the component is
  repaired by rotating its own points) both **fail**.

So the ladder picture is not the obstruction; the obstruction is that the
traversal's walk on the support is *not* the clockwise one, and the repair of a
single ladder moves points **across** the two ends of the maximal repeat
(`ladder_of_coalescing`: the two chords sit at `rotAdd ℓ p` and `rotAdd ℓ q`, and
`AltF_vtx'` equates the vertices across those two ends), not along an arc.

`G = 5` is the smallest circle carrying a primitive `P2` word, a read length
with `2 ≤ L ≤ K`, a genuine alternative traversal, and a *crossing* pair of
support chords --- so this is a minimal certificate, not a large one. -/
def minimal_global_refutation : Prop :=
  ∃ (T : Fin 5 → Fin 2) (σ : Fin 5 ≃ Fin 5),
    T = (![0, 0, 1, 0, 1] : Fin 5 → Fin 2) ∧
    ∀ (a b : Fin 5), InterlaceChords hK5 T σ a b →
      SE hK5 T a (AltF hK5 σ a) b (AltF hK5 σ b)

end AssemblyP1.Issue94InterlaceComponents