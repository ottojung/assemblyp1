import AssemblyP1.BBTLadder

/-!
# Board 94: valid ladder interval

A support chord at starts `a,b` is `pairBack a b` rungs from the canonical
maximal-repeat head.  The strengthened maximal-extension bound in
`P2RepeatResidual.pairBack_add_window_le_maxPairLen` shows that the complete
`(L-1)`-window still fits at every aligned rung up to that chord.  Hence every
such aligned swap is vertex-invisible.

This is the local geometric input for deleting two support chords from one
maximal-repeat ladder.
-/

set_option autoImplicit false

namespace AssemblyP1.Issue94LadderInterval

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-- Every aligned rung from the maximal-repeat head through a support chord
spells the same vertex on the two copies. -/
theorem aligned_vtx_through_pairBack (hG : 0 < G) (S : Fin G → α)
    (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S)
    {a b : Fin G} (hab : a ≠ b)
    (hv : vtx hG L S a = vtx hG L S b)
    {i : ℕ} (hi : i ≤ pairBack hG S a.val b.val) :
    vtx hG L S (rotAdd hG i (maxPairStart hG S a b)) =
      vtx hG L S (rotAdd hG i (maxPairStart hG S b a)) := by
  have hag : ∀ d : Fin (L - 1),
      cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) :=
    BBTUniqueEulerian.vtx_agr hG S hv
  obtain ⟨hR, hLen⟩ :=
    maxPair_isRepeat hG S hprim hab (by omega) (by omega) hag
  have hfull :=
    pairBack_add_window_le_maxPairLen hG S hprim hab (by omega) hag
  have hiFull : i + (L - 1) ≤ maxPairLen hG S a b := by omega
  have hAgree : ∀ d : Fin (maxPairLen hG S a b),
      cyc hG S ((maxPairStart hG S a b).val + d.val) =
        cyc hG S ((maxPairStart hG S b a).val + d.val) := by
    intro d
    exact hR.2.2.2.1 d
  exact BBTLadder.ladder_arc_eq (hG := hG) (L := L) (S := S) hL hAgree hLen hiFull

end AssemblyP1.Issue94LadderInterval

