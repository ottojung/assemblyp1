import AssemblyP1.Issue94P2DoubledPair
import AssemblyP1.BBTLadder

namespace AssemblyP1.Issue94LadderAligned

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94P2DoubledPair

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem aligned_vtx_of_support_chord
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK σ a = b)
    {i : ℕ} (hi : i + (L - 1) ≤ maxPairLen hK S a b) :
    vtx hK L S (rotAdd hK i (maxPairStart hK S a b)) =
      vtx hK L S (rotAdd hK i (maxPairStart hK S b a)) := by
  obtain ⟨hR, he⟩ :=
    orbit_maxPair_isRepeat hK S hEul hL hLK hprim hP2 hab hfx
  rcases hR with ⟨_, _, _, hag, _, _⟩
  exact ladder_arc_eq hK S hL hag he hi

theorem aligned_doubledPair_of_support_chord
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK σ a = b)
    {i : ℕ} (hi : i + (L - 1) ≤ maxPairLen hK S a b)
    (hne : rotAdd hK i (maxPairStart hK S a b) ≠
      rotAdd hK i (maxPairStart hK S b a)) :
    DoubledPair (L := L) hK S
      (rotAdd hK i (maxPairStart hK S a b))
      (rotAdd hK i (maxPairStart hK S b a)) := by
  apply doubledPair_of_vtx_eq hK S hL hLK hprim hP2 hne
  exact aligned_vtx_of_support_chord hK hL hLK S hprim hP2 hEul hab hfx hi

theorem aligned_swap_commutes
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK σ a = b)
    {i : ℕ} (hi : i + (L - 1) ≤ maxPairLen hK S a b)
    (hne : rotAdd hK i (maxPairStart hK S a b) ≠
      rotAdd hK i (maxPairStart hK S b a))
    (g : Fin K ≃ Fin K)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    g.trans (Equiv.swap
      (rotAdd hK i (maxPairStart hK S a b))
      (rotAdd hK i (maxPairStart hK S b a))) =
    (Equiv.swap
      (rotAdd hK i (maxPairStart hK S a b))
      (rotAdd hK i (maxPairStart hK S b a))).trans g := by
  exact Issue94FibreCommute.swap_commutes_vtxPreserving hK S hne g
    (aligned_doubledPair_of_support_chord hK hL hLK S hprim hP2 hEul hab hfx hi hne)
    hg

#print axioms AssemblyP1.Issue94LadderAligned.aligned_vtx_of_support_chord
#print axioms AssemblyP1.Issue94LadderAligned.aligned_doubledPair_of_support_chord
#print axioms AssemblyP1.Issue94LadderAligned.aligned_swap_commutes

end AssemblyP1.Issue94LadderAligned
