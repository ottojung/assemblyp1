import AssemblyP1.BBTCrossingCoalesce
import AssemblyP1.Issue94Step5Heads

/-!
# `Issue94HeadCollision`: a **cross-chord head collision forces `SameExtension`**

Board issue 94, front G1.

## The pointer being tested

`Issue94Step5Heads.Step5_heads_interleave` (and the related §5 step-5 line) is
false because the four **heads** of two interleaving chords need not be pairwise
distinct: the two chords can share a head (`maxPairStart a b = maxPairStart c d`).
`Issue94Step5Heads` already records that the only way this happens is by a
cross-chord collision between the two head-pairs, and that the *unguarded*
formulation is refuted by a kernel-checked witness.

This module tests the **positive** form of that observation: a cross-head
collision is not something to be excluded --- it should *immediately deliver*
the target conclusion `SameExtension`.  Namely:

> If the head-pair `{A, B}` of the first chord and the head-pair `{C, D}` of the
> second chord share a point, then the two chords have the same deterministic
> maximal extension as unordered pairs.

The proof is the collision step `BBTCrossingCoalesce.collision_forces_pair`
(§3) applied at the head level: two distinct starts that carry a common
`(L-1)`-mer and share an endpoint have the same other endpoint, because the
fibre of that `(L-1)`-mer has size at most two (`P2`).  Each of the four
cross-head equalities gives one of the two disjuncts of `SameExtension` directly.

## What this does and does not give

This is a **helper**, not the step-5 theorem.  It says nothing about the case
where the four heads are pairwise distinct; that case is exactly the remaining
second disjunct of `Issue94Step5Heads.head_dichotomy`.  The point of this module
is that the collision case of that dichotomy is *free*, and in particular that a
cross-head collision is a proof device rather than a counterexample.
-/

namespace AssemblyP1.Issue94HeadCollision

open BBTLadder BBTCrossingCoalesce

/-- **A cross-head collision forces `SameExtension`.**  If the head-pair
`{A, B}` of the chord `a b` and the head-pair `{C, D}` of the chord `c d`
share a point, then the two chords carry the **same** deterministic maximal
extension, as unordered pairs of starts.

Hypotheses: the two chords are genuine (`a ≠ b`, `c ≠ d`) and each carries a
common `(L-1)`-mer; `hA`, `hB`, `hC`, `hD` are the four head-distinctness
facts, i.e. the two heads *of each individual chord* are distinct.  This is the
hypothesis set that `Issue94Step5Heads.heads_of_one_chord_ne` supplies from
`a ≠ b` and the `(L-1)`-mer equality, so at the intended call site none of them
is extra; the corollary below discharges them.

The conclusion `SameExtension` carries **no hypotheses of its own** beyond `hK`
and `S` (`BBTLadder.lean`:604): it is the unordered-pair equality of
`maxPairStart`.  So nothing is smuggled in on the conclusion side.
-/
theorem head_collision_implies_sameExtension {K L : ℕ} (hK : 0 < K) (S : Fin K → α)
    (hL : 2 ≤ L) (hLG : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hA : maxPairStart hK S a b ≠ maxPairStart hK S b a)
    (hC : maxPairStart hK S c d ≠ maxPairStart hK S d c)
    (hcoll : maxPairStart hK S a b = maxPairStart hK S c d ∨
      maxPairStart hK S a b = maxPairStart hK S d c ∨
      maxPairStart hK S b a = maxPairStart hK S c d ∨
      maxPairStart hK S b a = maxPairStart hK S d c) :
    SameExtension K hK S a b c d := by
  -- The two heads of the first chord are a chord in their own right
  -- (`vtx_maxPairStart`, §4), and likewise for the second.
  have hA' : vtx hK L S (maxPairStart hK S a b) = vtx hK L S (maxPairStart hK S b a) :=
    vtx_maxPairStart hL hLG hprim hab hvab
  have hC' : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hL hLG hprim hcd hvcd
  rcases hcoll with h | h | h | h
  · refine Or.inl ⟨h, ?_⟩
    exact collision_forces_pair hL hLG hprim hP2 hA hC hA' hC' h.symm
  · refine Or.inr ⟨h, ?_⟩
    refine collision_forces_pair hL hLG hprim hP2 hA hC.symm hA' hC'.symm h.symm
  · refine Or.inr ⟨?_, h.symm⟩
    refine collision_forces_pair hL hLG hprim hP2 hA.symm hC hA'.symm hC' h
  · refine Or.inl ⟨?_, h⟩
    refine collision_forces_pair hL hLG hprim hP2 hA.symm hC.symm hA'.symm hC'.symm h.symm

/-- **The same statement with the head-distinctness discharged**, in the
`Bin` setting that the step-5 reduction actually lives in.  The four hypotheses
`hagA`/`hagC` are exactly the chord hypotheses of
`Issue94Step5Heads.heads_of_one_chord_ne`, so this is the form to use at the
`head_dichotomy` call site. -/
theorem head_collision_implies_sameExtension_Bin {K L : ℕ} (hK : 0 < K)
    (S : Fin K → PopulationReduction.Bin) (hL : 2 ≤ L) (hLG : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hagA : ∀ d : Fin (L - 1), cyc hK S (a.val + d.val) = cyc hK S (b.val + d.val))
    (hagC : ∀ d : Fin (L - 1), cyc hK S (c.val + d.val) = cyc hK S (d.val + d.val))
    (hcoll : maxPairStart hK S a b = maxPairStart hK S c d ∨
      maxPairStart hK S a b = maxPairStart hK S d c ∨
      maxPairStart hK S b a = maxPairStart hK S c d ∨
      maxPairStart hK S b a = maxPairStart hK S d c) :
    SameExtension K hK S a b c d :=
  head_collision_implies_sameExtension hK S hL hLG hP2 hprim hab hcd hvab hvcd
    (Issue94Step5Heads.heads_of_one_chord_ne hK S hL hLG hprim hab hagA)
    (Issue94Step5Heads.heads_of_one_chord_ne hK S hL hLG hprim hcd hagC) hcoll

end AssemblyP1.Issue94HeadCollision
