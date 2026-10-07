import AssemblyP1.Issue94ComponentCoordinates
import AssemblyP1.Issue94InterlaceComponents
import AssemblyP1.Issue94Antiderivative
import AssemblyP1.Issue94PhysicalChord

/-!
# Board 94: the swap bridge across one interlace component

For two physical AltF chords `c` and `d` in the same connected component of
`altFInterlaceGraph`, the transposition of `d`'s endpoints is exactly the
aligned swap on `c`'s maximal-extension ladder at `d`'s chord coordinate.
-/

namespace AssemblyP1.Issue94SwapBridge

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTEulerian
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94InterlaceComponents
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94ComponentCoordinates

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- **The swap bridge.**  For physical AltF chords `c` and `d` in one connected
component of the interlace graph, the endpoint transposition of `d` is the
aligned swap on `c`'s `maxPairStart` ladder at `chordCoordinate d`.

The endpoint two-element `Finset` equality of
`component_chord_coordinate_exact` splits, by `pair_two_eq`, into the same and
the swapped endpoint orientation; the swapped case is the same aligned swap by
`Equiv.swap_comm`. -/
theorem swap_bridge_of_component
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    {c d : AltFChord hK sigma}
    (hcomp :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d) :
    Equiv.swap d.1 (AltF hK sigma d.1) =
      alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1)
        (chordCoordinate hK S sigma d) := by
  obtain ⟨hpair, _⟩ :=
    component_chord_coordinate_exact hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
  rcases pair_two_eq hK hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [congrArg₂ Equiv.swap h1 h2]
    unfold alignedSwap
    rfl
  · rw [congrArg₂ Equiv.swap h1 h2]
    unfold alignedSwap
    exact Equiv.swap_comm _ _

end AssemblyP1.Issue94SwapBridge
