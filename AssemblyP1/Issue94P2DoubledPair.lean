import AssemblyP1.BBTCrossingCoalesce
import AssemblyP1.Issue94FibreCommute

/-!
# Board 94: primitive P2 turns every distinct equal-vtx pair into a doubled fibre

In the long-window range, `P2.imp_nodeCount_le_two` bounds every `(L-1)`-mer
fibre by two. If two distinct starts already carry the same `vtx`, that fibre
has at least two members, hence exactly those two members. This packages the
fact as `BBTLadder.DoubledPair`, so `Issue94FibreCommute` can be applied to
aligned maximal-repeat ladder swaps.
-/

namespace AssemblyP1.Issue94P2DoubledPair

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTCrossingCoalesce
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual

variable {α : Type} [DecidableEq α] {K L : ℕ}
  (hK : 0 < K) (S : Fin K → α)

theorem doubledPair_of_vtx_eq (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b : Fin K} (hab : a ≠ b)
    (hv : vtx hK L S a = vtx hK L S b) :
    DoubledPair (L := L) hK S a b := by
  have ha : a ∈ nodeStartsOf hK S (vtx hK L S a) :=
    mem_nodeStartsOf_vtx hK S rfl
  have hb : b ∈ nodeStartsOf hK S (vtx hK L S a) :=
    mem_nodeStartsOf_vtx hK S hv.symm
  have hsub : ({a, b} : Finset (Fin K)) ⊆
      nodeStartsOf hK S (vtx hK L S a) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have htwo : 2 ≤ (nodeStartsOf hK S (vtx hK L S a)).card := by
    have hcard : ({a, b} : Finset (Fin K)).card = 2 := by simp [hab]
    exact hcard ▸ Finset.card_le_card hsub
  have hcap := P2.imp_nodeCount_le_two hK hL hLK S hprim hP2 (vtx hK L S a)
  have hcapCard : (nodeStartsOf hK S (vtx hK L S a)).card ≤ 2 := by
    rw [card_nodeStartsOf]
    exact hcap
  have hcardEq : (nodeStartsOf hK S (vtx hK L S a)).card = 2 :=
    Nat.le_antisymm hcapCard htwo
  have hcount : OrientedRigidity.nodeCount (L := L) hK S (vtx hK L S a) = 2 := by
    rw [← card_nodeStartsOf]
    exact hcardEq
  refine ⟨hcount, ?_, hv.symm⟩
  intro x hx
  change vtx hK L S x = vtx hK L S a at hx
  by_cases hxa : x = a
  · exact Or.inl hxa
  · have hax : a ≠ x := fun h => hxa h.symm
    exact Or.inr ((three_starts_ne hK S hL hLK hprim hP2 hv hx.symm hab hax).symm)

/-- The exact corollary consumed by the antiderivative route: an aligned
equal-vtx swap commutes with any residual label-preserving permutation. -/
theorem swap_commutes_of_vtx_eq (hL : LE.le 2 L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b : Fin K} (hab : a ≠ b)
    (hv : vtx hK L S a = vtx hK L S b)
    (g : Fin K ≃ Fin K)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    g.trans (Equiv.swap a b) = (Equiv.swap a b).trans g := by
  apply Equiv.ext
  intro x
  exact congrFun
    (Issue94FibreCommute.swap_comm_of_vtxPreserving_equiv
      hK S hL hLK hprim hP2 hab hv g hg) x

#print axioms AssemblyP1.Issue94P2DoubledPair.doubledPair_of_vtx_eq
#print axioms AssemblyP1.Issue94P2DoubledPair.swap_commutes_of_vtx_eq

end AssemblyP1.Issue94P2DoubledPair
