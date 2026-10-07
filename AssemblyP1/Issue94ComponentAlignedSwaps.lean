import AssemblyP1.Issue94ComponentResidual
import AssemblyP1.Issue94ComponentCoordinates

/-!
# Board 94, front `94comp`: the component switch in terms of aligned swaps

This module exposes the canonical `componentSwitch` of
`Issue94ComponentResidual` in terms of the component coordinate aligned swaps:
for each coordinate `ell` in `componentCoordinates hK S sigma c`, the switch
exchanges the aligned pair `rotAdd hK ell p` and `rotAdd hK ell q`, where `p, q`
are the maximal-extension starts of the base chord `c`.

This is `componentCoordinate_mem_data` read through the pointwise
characterization of `onSet`: the switch acts as `AltF` on the endpoint set, and
`AltF` swaps the two endpoints of each chord.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentAlignedSwaps

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94PhysicalComponent
open AssemblyP1.Issue94InterlaceComponents
open AssemblyP1.Issue94CoordinateValidity
open AssemblyP1.Issue94ComponentCoordinate
open AssemblyP1.Issue94ComponentCoordinates
open AssemblyP1.Issue94CLEDeletion
open AssemblyP1.Issue94InterlaceKernel
open AssemblyP1.Issue94SupportDescent
open AssemblyP1.Issue94ComponentEndpoints
open AssemblyP1.Issue94InvolutionSplit
open AssemblyP1.Issue94ComponentResidual

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- **The component switch swaps each aligned pair.**  For every coordinate
`ell` in `componentCoordinates hK S sigma c`, the switch exchanges
`rotAdd hK ell p` and `rotAdd hK ell q`, where `p, q` are the maximal-extension
starts of the base chord `c`.

This is the aligned-pairs characterization of the component switch: the switch
is the product of the aligned swaps `alignedSwap hK p q ell` over all `ell` in
the component coordinate set. -/
theorem componentSwitch_swap_aligned (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (hUkk : Ukkonen hK L S) (c : AltFChord hK sigma) {ell : ℕ}
    (hell : ell ∈ componentCoordinates hK S sigma c) :
    componentSwitch hK S sigma hEul hL hLK hprim hP2 c
        (rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)))
      = rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1) ∧
    componentSwitch hK S sigma hEul hL hLK hprim hP2 c
        (rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1))
      = rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)) := by
  obtain ⟨hvalid, ⟨d, hd, hcoord, hpair⟩⟩ :=
    componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hell
  have hdmem : d ∈ componentFinset (altFInterlaceGraph hK S sigma) c := hd
  have hsq := AltF_sq hK S hEul hL hLK hprim hP2 d.1
  have hp : rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1))
      ∈ componentEndpoints hK S sigma c := by
    rcases pair_two_eq hK hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hdmem, by simp [h1]⟩
    · apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hdmem, by simp [h2]⟩
  have hq : rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1)
      ∈ componentEndpoints hK S sigma c := by
    rcases pair_two_eq hK hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hdmem, by simp [h2]⟩
    · apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hdmem, by simp [h1]⟩
  have hAltF_p : AltF hK sigma (rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)))
      = rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1) := by
    rcases pair_two_eq hK hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, h2]
    · rw [← h2, hsq, h1]
  have hAltF_q : AltF hK sigma (rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1))
      = rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)) := by
    rcases pair_two_eq hK hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2, hsq, h1]
    · rw [← h1, h2]
  refine ⟨?_, ?_⟩
  · simp only [componentSwitch, onSetEquiv_apply, onSet, hp, if_true]
    exact hAltF_p
  · simp only [componentSwitch, onSetEquiv_apply, onSet, hq, if_true]
    exact hAltF_q

#print axioms AssemblyP1.Issue94ComponentAlignedSwaps.componentSwitch_swap_aligned

end AssemblyP1.Issue94ComponentAlignedSwaps
