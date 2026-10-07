import AssemblyP1.BBTCrossingCoalesce
import AssemblyP1.Issue94Step5Heads

/-!
# `Issue94HeadCollision`: a **cross-chord head collision forces `SameExtension`**

Board issue 94, front G1.  Work order: the human pointer at 21:33:57Z on
board issue 94.

## The pointer being implemented

The pointer reads:

> I think the current B2 formulation is aiming at the wrong conclusion.  A
> cross-head collision does not need to be ruled out; it looks like it should
> immediately prove `SameExtension`.  Write
>
> - `A = maxPairStart hK S a b`
> - `B = maxPairStart hK S b a`
> - `C = maxPairStart hK S c d`
> - `D = maxPairStart hK S d c`.
>
> Existing machinery appears to give exactly what is needed:
>
> 1. `vtx_maxPairStart` gives `vtx A = vtx B` and `vtx C = vtx D`.
> 2. `heads_of_one_chord_ne` gives `A ≠ B` and `C ≠ D`.
> 3. `collision_forces_pair` says that two distinct `vtx`-equal pairs sharing
>    one endpoint have the same other endpoint, using primitive P2 /
>    fibre ≤ 2.
>
> Therefore, for example, if `A = C`, apply `collision_forces_pair` to head
> pairs `(A,B)` and `(C,D)` to get `B = D`, yielding the first disjunct of
> `SameExtension`. ...
>
> This suggests a helper of the shape
> `head_collision_implies_sameExtension : (A=C ∨ A=D ∨ B=C ∨ B=D) → SameExtension ...`
> rather than a lemma excluding head collisions.

This module proves exactly that helper, in the shape the pointer gives, for
an arbitrary alphabet `α` with `[DecidableEq α]`, and derives the head
distinctness (`A ≠ B`, `C ≠ D`) internally rather than taking it as a
hypothesis.

## What this does and does not give

This is a **helper**, not `CrossingPairsCoalesce` itself.  It settles the
*collision* case of the intended case split, and it settles it in the strong
sense the pointer asks for: a single cross-head equality, with no further
guard, delivers the full unordered `SameExtension`.  It says nothing about the
case of four pairwise-distinct heads, which is the other half of the split.

No hypothesis here is stronger than the pointer's.  In particular the two
`(L-1)`-mer agreements `hagab`/`hagcd` are exactly the chord hypotheses that
`BBTCrossingCoalesce.CrossingPairsCoalesce` already demands of its `a b c d`,
and the head distinctness the pointer obtains from `heads_of_one_chord_ne` is
re-derived here by the same argument for general `α`, since
`Issue94Step5Heads.heads_of_one_chord_ne` is stated only over
`PopulationReduction.Bin`.
-/

namespace AssemblyP1.Issue94HeadCollision

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTCrossingCoalesce

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-- **The two extension starts of one chord are distinct** (`heads_of_one_chord_ne`
of the pointer, step 2, for general `α`).  This is the argument of
`Issue94Step5Heads.heads_of_one_chord_ne`, which is stated only over
`PopulationReduction.Bin`; it is repeated here so that this helper is
self-contained and does not depend on the `Bin` specialisation. -/
theorem heads_ne_of_chord {G L : ℕ} {α : Type} [DecidableEq α] (hG : 0 < G)
    (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G}
    (hab : a ≠ b) (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    maxPairStart hG S a b ≠ maxPairStart hG S b a := by
  obtain ⟨hR, _hℓ⟩ := maxPair_isRepeat hG S hprim hab (by omega) (by omega) hag
  exact hR.2.2.1

/-- **A cross-head collision forces `SameExtension`** --- the helper of the
21:33:57Z pointer.

With `A = maxPairStart hK S a b`, `B = maxPairStart hK S b a`,
`C = maxPairStart hK S c d`, `D = maxPairStart hK S d c`, the conclusion is
`SameExtension K hK S a b c d`, i.e. the unordered pair `{A, B}` of extension
starts equals the unordered pair `{C, D}`.

The only extra assumption beyond `P2` and primitivity is the **collision**
`hcoll`: at least one of the four cross-head equalities `A = C`, `A = D`,
`B = C`, `B = D` holds.  There is no guard against the collision, and the
`Bin` restriction of `heads_of_one_chord_ne` is avoided --- the head
distinctness is `heads_ne_of_chord` above.

The proof is exactly the pointer's four cases, each one application of
`BBTCrossingCoalesce.collision_forces_pair` to the two *head* pairs (which are
themselves chords, by `BBTCrossingCoalesce.vtx_maxPairStart`). -/
theorem head_collision_implies_sameExtension {K L : ℕ} {α : Type} [DecidableEq α]
    (hK : 0 < K) (S : Fin K → α) (hL : 2 ≤ L) (hLG : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hagab : ∀ d : Fin (L - 1), cyc hK S (a.val + d.val) = cyc hK S (b.val + d.val))
    (hagcd : ∀ e : Fin (L - 1), cyc hK S (c.val + e.val) = cyc hK S (d.val + e.val))
    (hcoll : maxPairStart hK S a b = maxPairStart hK S c d ∨
      maxPairStart hK S a b = maxPairStart hK S d c ∨
      maxPairStart hK S b a = maxPairStart hK S c d ∨
      maxPairStart hK S b a = maxPairStart hK S d c) :
    SameExtension K hK S a b c d := by
  -- Pointer step 1: the heads of each chord are themselves a chord.
  have hA' : vtx hK L S (maxPairStart hK S a b) = vtx hK L S (maxPairStart hK S b a) :=
    vtx_maxPairStart hK S hL hLG hprim hab hagab
  have hC' : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S hL hLG hprim hcd hagcd
  -- Pointer step 2: the two heads of each chord are distinct.
  have hA : maxPairStart hK S a b ≠ maxPairStart hK S b a :=
    heads_ne_of_chord hK S hL hLG hprim hab hagab
  have hC : maxPairStart hK S c d ≠ maxPairStart hK S d c :=
    heads_ne_of_chord hK S hL hLG hprim hcd hagcd
  -- Pointer step 3, one case per disjunct of `hcoll`.
  rcases hcoll with h | h | h | h
  · refine Or.inl ⟨h, ?_⟩
    exact collision_forces_pair hK S hL hLG hprim hP2 hA hC hA' hC' h.symm
  · refine Or.inr ⟨h, ?_⟩
    exact collision_forces_pair hK S hL hLG hprim hP2 hA hC.symm hA' hC'.symm h.symm
  · refine Or.inr ⟨?_, h⟩
    exact collision_forces_pair hK S hL hLG hprim hP2 hA.symm hC hA'.symm hC' h.symm
  · refine Or.inl ⟨?_, h⟩
    exact collision_forces_pair hK S hL hLG hprim hP2 hA.symm hC.symm hA'.symm hC'.symm h.symm

end AssemblyP1.Issue94HeadCollision
