import AssemblyP1.BBTLadder

/-!
# Reductions for `BBTLadder.LadderVertexCycle` (board 94, second Lean front)

This module does **not** prove `BBTLadder.LadderVertexCycle`
(`AssemblyP1/BBTLadder.lean:649-658`).  That `Prop` is untouched; see
"Status" below.  What this module establishes is (i) a set of
kernel-checked reductions of the obligation, and (ii) an explicit,
kernel-checked statement of the residual obstruction.  No `sorry`, no `admit`,
no `native_decide`, no `unsafe`, no new `axiom`, no linter suppression of the
prohibitions in the brief.

## What is proved here

* **§1 (`vtx_rotAdd`, `rotAdd_prevPos`, `rotAdd_mod`, `rotAdd_zero`)** --- the
  `(L-1)`-mer at a start slides with the start, and the *index* arithmetic of
  `Fin G` needed to re-index a listing by the rotation.  These are the
  `vtx`-level and `Fin`-level forms of "a window slides", and nothing about the
  graph.
* **§2 (`listing_conjugate`)** --- **the central listing identity.**  For a
  genuine Eulerian cycle with listing `σ`,
  `vtx (σ i) = vtx (nextPos (σ (prevPos i)))`, i.e. the vertex listing of `σ` is
  the vertex listing of the *rotation-conjugate* `ρ σ ρ⁻¹`.  Only the
  `traverses` clause of `EulerianCycle` is used (`AltF_vtx'`).
  `listing_step` is the same fact in permutation form:
  `σ (nextPos x) = AltF hG σ (nextPos (σ x))`.
* **§3 (`rotConj`, `vertexCycleEq_conj`)** --- **the first structural
  reduction of the obligation.**  Since the vertex listing of `σ` is the vertex
  listing of `ρ σ ρ⁻¹` (and conversely), the target
  `VertexCycleEq hK L S σ (Equiv.refl)` is equivalent to the same target for
  `ρ σ ρ⁻¹`.  So the listing may be re-indexed by the rotation of the circle at
  no cost, and whatever obstructs the target has to be carried by the geometry
  of the chords of `AltF hK σ`, not by the choice of which listing position is
  called position `0`.
* **§4 (`altF_eq`, `altF_unfold`)** --- `f = AltF hK σ` is the conjugate
  `σ ρ σ⁻¹ ρ⁻¹` of the one-step rotation, in permutation form.  This is the
  statement that the support of `f` is exactly the deviation of the listing `σ`
  from a rotation, which is what makes the support a set of chords at all, and
  it is the bridge between §3 and the chord geometry the obligation is about.
* **§5 (`vertexCycleEq_of_both`)** --- **the bridge between the two board-94
  obligations.**  `CrossingChordsCoalesce L` together with
  `LadderVertexCycle L` gives vertex-cycle uniqueness on the class of primitive
  `P2` words.  This certifies that the two fronts are mathematically composable
  and that the ladder route really does reduce the endgame to those two `Prop`s.

## Status: what is still open

`LadderVertexCycle` is **not** proved and **not** refuted here.  The residual
obligation, in the library's own vocabulary, is:

> For a genuine `EulerianCycle hK L S σ` with at least two transposition orbits
> in `Support (AltF hK σ)` (i.e. at least two chords of `BBTLadder.Support`),
> and with the coalescing hypothesis of the `Prop` available, show that the
> traversal walks the resulting ladder blocks in the geometric order of the
> circle, so that the listing of `σ` is the truth's vertex listing up to a
> shift.

§3 is the reduction that makes this precise: by `vertexCycleEq_conj` one may
assume the listing is indexed so that the rotation-conjugate is the listing
itself, and then the only remaining content is the order in which the blocks are
walked.  §4 says that content is a statement about `AltF hK σ` alone.

`BBTMaximalExtension` / `ladder_of_coalescing` say each block is two rotations
of one pair and is vertex-invisible (`ladder_arc_eq`, `AltF_vtx'`); what is


-/

namespace AssemblyP1.BBTVertexCycle

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
set_option maxHeartbeats 800000
-- the same option `AssemblyP1/BBTEulerian.lean:101` uses: the reduction theorems
-- legitimately do not need `DecidableEq α`
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

/-! ## 1. The vertex at a start slides with the start -/

theorem addMod (a b : ℕ) : (a % G + b) % G = (a + b) % G := by
  rw [Nat.add_mod, Nat.mod_mod]
  exact (Nat.add_mod a b G).symm

theorem modAdd (a b : ℕ) : (a + b % G) % G = (a + b) % G := by
  rw [Nat.add_mod, Nat.mod_mod]
  exact (Nat.add_mod a b G).symm

theorem rotAdd_zero (x : Fin G) : rotAdd hG 0 x = x := by
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk]
  exact Nat.add_zero (x.val) ▸ Nat.mod_eq_of_lt x.isLt

theorem rotAdd_mod (s : ℕ) (i : Fin G) : rotAdd hG (s % G) i = rotAdd hG s i := by
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk]
  rw [modAdd]

/-- **The `(L-1)`-mer at a start slides with the start.**  The `(L-1)`-mer at
`rotAdd s (rotAdd t x)` is the `(L-1)`-mer at `rotAdd (s + t) x`. -/
theorem vtx_rotAdd (s t : ℕ) (x : Fin G) :
    vtx hG L S (rotAdd hG s (rotAdd hG t x)) = vtx hG L S (rotAdd hG (s + t) x) := by
  funext d
  apply congrArg (cyc hG S)
  simp only [rotAdd, Fin.val_mk]
  have h1 : ((x.val + t) % G + s) % G = (x.val + t + s) % G := by
    rw [addMod]
  rw [h1, show x.val + (s + t) = x.val + t + s by omega]

/-- **A backward step of the listing index is a backward step of the start.**
This is the `Fin`-level form of "index `i - 1` reads the start `x - 1`". -/
theorem rotAdd_prevPos (s : ℕ) (i : Fin G) :
    rotAdd hG s (prevPos hG i) = rotAdd hG ((s + G - 1) % G) i := by
  apply Fin.ext
  simp only [rotAdd, prevPos, Fin.val_mk]
  rw [addMod, modAdd]
  congr 1
  omega

theorem nextPos_bijective : Function.Bijective (nextPos hG : Fin G → Fin G) :=
  ⟨nextPos_inj hG, (Finite.injective_iff_surjective).mp (nextPos_inj hG)⟩

theorem prevPos_inj : Function.Injective (prevPos hG : Fin G → Fin G) := by
  intro a b heq
  have h3 := congrArg (nextPos hG) heq
  rwa [nextPrev hG a, nextPrev hG b] at h3

theorem prevPos_bijective : Function.Bijective (prevPos hG : Fin G → Fin G) :=
  ⟨prevPos_inj hG, (Finite.injective_iff_surjective).mp (prevPos_inj hG)⟩

/-! ## 2. The vertex listing of `σ` is the vertex listing of `ρ σ ρ⁻¹` -/

/-- **The listing identity behind `VertexCycleEq`.**  For a genuine Eulerian
cycle with listing `σ`, the `(L-1)`-mer read at the `i`-th position of the
alternative listing equals the `(L-1)`-mer read at
`nextPos (σ (prevPos i))`, which is `ρ σ ρ⁻¹ i` with `ρ = nextPos`.

Only the `traverses` clause of `EulerianCycle` is used (`AltF_vtx'`), so this is
a statement about the listing and not about the graph. -/
theorem listing_conjugate {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (i : Fin G) :
    vtx hG L S (σ i) = vtx hG L S (nextPos hG (σ (prevPos hG i))) := by
  have h := AltF_vtx' hG S hEul (nextPos hG (σ (prevPos hG i)))
  have hq : prevPos hG (nextPos hG (σ (prevPos hG i))) = σ (prevPos hG i) :=
    prevNext hG _
  have h' : AltF hG σ (nextPos hG (σ (prevPos hG i))) = σ i := by
    unfold AltF
    rw [hq, Succ_apply hG σ (prevPos hG i), nextPrev hG]
  rw [h'] at h
  exact h

/-- **The vertex listing, read at the `nextPos`-indexed positions.** -/
theorem vtx_listing_step {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (i : Fin G) :
    vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i)) := by
  simpa only [prevNext hG] using listing_conjugate hG S hEul (nextPos hG i)

/-- **The `AltF` form of the listing step:** `f = AltF hG σ` is the conjugate
`σ ρ σ⁻¹ ρ⁻¹` of the one-step rotation, so the listing obeys
`σ (nextPos x) = f (nextPos (σ x))`. -/
theorem listing_step {σ : Fin G ≃ Fin G} (i : Fin G) :
    σ (nextPos hG i) = AltF hG σ (nextPos hG (σ i)) := by
  rw [AltF_succ hG σ (σ i), Succ_apply hG σ i]

/-- **The vertex listing of `σ` is the vertex listing of `ρ σ ρ⁻¹`** (§2). -/
theorem vtx_listing_conj {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (i : Fin G) :
    vtx hG L S (σ i) = vtx hG L S (nextPos hG (σ (prevPos hG i))) :=
  listing_conjugate hG S hEul i

/-! ## 3. The target sees only the vertex listing -/

/-- **The rotation-conjugate listing `ρ σ ρ⁻¹`, as a bijection.** -/
theorem rotConj_bijective (σ : Fin G ≃ Fin G) :
    Function.Bijective (fun i => nextPos hG (σ (prevPos hG i))) :=
  (nextPos_bijective hG).comp ((σ.bijective).comp (prevPos_bijective hG))

/-- **The rotation-conjugate listing `ρ σ ρ⁻¹`.** -/
noncomputable def rotConj (σ : Fin G ≃ Fin G) : Fin G ≃ Fin G :=
  Equiv.ofBijective _ (rotConj_bijective hG σ)

theorem rotConj_apply (σ : Fin G ≃ Fin G) (i : Fin G) :
    (rotConj hG σ) i = nextPos hG (σ (prevPos hG i)) := rfl

/-- **The target of `LadderVertexCycle` is a statement about the vertex
listing only, so it is invariant under shifting the listing by one position**
--- equivalently, under conjugating the presentation by the rotation of the
circle.

This is the first structural reduction of the obligation: the target
`VertexCycleEq hK L S σ (Equiv.refl)` does not distinguish `σ` from
`ρ σ ρ⁻¹`, so the listing may be re-indexed by the rotation at no cost, at the
price of shifting the witnessing rotation by one step.  Whatever obstructs the
target therefore has to be carried by the geometry of the chords of
`AltF hK σ`, not by the choice of which listing position is called position
`0`. -/
theorem vertexCycleEq_conj {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))
      ↔ VertexCycleEq hG L S (rotConj hG σ) (Equiv.refl (α := Fin G)) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨k.val, k.isLt⟩, ?_⟩
    intro i
    show vtx hG L S (nextPos hG (σ (prevPos hG i))) = vtx hG L S (rotAdd hG k.val i)
    rw [← vtx_listing_conj hG S hEul i]
    exact hk i
  · rintro ⟨k, hk⟩
    refine ⟨⟨k.val, k.isLt⟩, ?_⟩
    intro i
    show vtx hG L S (σ i) = vtx hG L S (rotAdd hG k.val i)
    have hk' : vtx hG L S (nextPos hG (σ (prevPos hG i)))
        = vtx hG L S (rotAdd hG k.val i) := by
      have h := hk i
      rwa [rotConj_apply hG σ i] at h
    exact (vtx_listing_conj hG S hEul i).trans hk'

/-! ## 4. `AltF` is a rotation-conjugate of the one-step rotation -/

/-- **The conjugation formula for `AltF`, in permutation form.**  `f = AltF hK σ`
is the conjugate `σ ρ σ⁻¹ ρ⁻¹` of the one-step rotation, i.e. the rotation of the
circle by `σ 0` followed by one step backwards.  This is the statement that the
support of `f` is precisely the deviation of the listing `σ` from a rotation of
the circle, which is what makes the support a set of chords at all. -/
theorem altF_eq {σ : Fin G ≃ Fin G} (x : Fin G) :
    AltF hG σ x = Succ hG σ (prevPos hG x) := rfl

theorem altF_unfold {σ : Fin G ≃ Fin G} (x : Fin G) :
    AltF hG σ x = σ (nextPos hG (σ.symm (prevPos hG x))) := rfl



/-! ## 5. The bridge between the two obligations of `#89`

Note on the two `Prop`s: `CrossingChordsCoalesce` (`BBTLadder.lean:616`) and
`LadderVertexCycle` (`BBTLadder.lean:649`) are *not* interchangeable as `Prop`s.
The former carries no `2 ≤ L` and no `L ≤ K`; the latter carries both.  This is
why the bridge below is stated with both side conditions made explicit, and why
**no** implication between the two `Prop`s is claimed anywhere in this file:
both are uninhabited, and this file does not inhabit either. -/

/-- **The composition of the two obligations of `#89` gives vertex-cycle
uniqueness on the class of primitive `P2` words.**  This is what makes the split
into two fronts legitimate: neither obligation follows from the other, but the
two together settle `thm:BBT` on the class the ladder route covers.

The residual qualifier `P2` + primitivity is real and is **not** discharged
here: `BBTEulerian.UniqueEulerianCycle` carries only `Ukkonen`, and `Ukkonen`
does not imply `P2`.  So this theorem is `thm:BBT` restricted to the `P2`-class,
which is exactly the class the ladder machinery lives on; the remaining gap to
`UniqueEulerianCycle` is the `P2` hypothesis, not the ladder argument. -/
theorem vertexCycleEq_of_both {L : ℕ}
    (h1 : CrossingChordsCoalesce (α := α) L)
    (h2 : LadderVertexCycle (α := α) L) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), P2 hK L S →
      RepeatAdapter.IsPrimitive hK S → 2 ≤ L → L ≤ K → Ukkonen hK L S →
      ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
        VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) := by
  intro K hK S hP2 hprim h2L hLK hUkk σ hEul
  exact h2 K hK S hP2 hprim h2L hLK hUkk σ hEul
    (h1 K hK S hP2 hprim hUkk σ hEul)

end AssemblyP1.BBTVertexCycle


#print axioms AssemblyP1.BBTVertexCycle.vertexCycleEq_conj
#print axioms AssemblyP1.BBTVertexCycle.listing_conjugate
#print axioms AssemblyP1.BBTVertexCycle.altF_eq
#print axioms AssemblyP1.BBTVertexCycle.vertexCycleEq_of_both
