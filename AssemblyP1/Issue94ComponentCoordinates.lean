import AssemblyP1.Issue94ComponentCoordinatesExact
import AssemblyP1.Issue94InterlaceKernel

namespace AssemblyP1.Issue94ComponentCoordinates

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94PhysicalComponent
open AssemblyP1.Issue94InterlaceComponents
open AssemblyP1.Issue94CoordinateValidity
open AssemblyP1.Issue94ComponentCoordinate
open AssemblyP1.Issue94CLEDeletion
open AssemblyP1.Issue94InterlaceKernel

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem chordCoordinate_injective_on_component
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    {c d e : AltFChord hK sigma}
    (hdc :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d)
    (hec :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk e)
    (hcoord :
      chordCoordinate hK S sigma d = chordCoordinate hK S sigma e) :
    d = e := by
  have hd := (component_chord_coordinate_exact hK hL hLK S hP2 hprim hUkk
    sigma hEul hdc).1
  have he := (component_chord_coordinate_exact hK hL hLK S hP2 hprim hUkk
    sigma hEul hec).1
  rw [hcoord] at hd
  exact physical_chord_eq_of_pair_eq hK sigma (hd.trans he.symm)

noncomputable def componentCoordinates
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) : Finset ℕ :=
  (componentFinset (altFInterlaceGraph hK S sigma) c).image
    (chordCoordinate hK S sigma)

theorem componentCoordinates_card
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    (componentCoordinates hK S sigma c).card =
      (componentFinset (altFInterlaceGraph hK S sigma) c).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro d hd e he hcoord
  have hdc :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
    have hd' := (Finset.mem_filter.mp hd).2
    exact hd'.symm
  have hec :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk e := by
    have he' := (Finset.mem_filter.mp he).2
    exact he'.symm
  exact chordCoordinate_injective_on_component hK hL hLK S hP2 hprim hUkk
    sigma hEul hdc hec hcoord

theorem componentCoordinates_even
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    Even (componentCoordinates hK S sigma c).card := by
  rw [componentCoordinates_card hK hL hLK S hP2 hprim hUkk sigma hEul c]
  exact physicalInterlace_component_even_card hK S sigma hEul hL hLK hprim hP2 c

theorem componentCoordinate_mem_data
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) {ell : ℕ}
    (hell : ell ∈ componentCoordinates hK S sigma c) :
    ell + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1) ∧
      ∃ d : AltFChord hK sigma,
        d ∈ componentFinset (altFInterlaceGraph hK S sigma) c ∧
        chordCoordinate hK S sigma d = ell ∧
        ({d.1, AltF hK sigma d.1} : Finset (Fin K)) =
          {rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)),
            rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1)} := by
  classical
  rcases Finset.mem_image.mp hell with ⟨d, hd, hdeq⟩
  have hcomp :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
    exact ((Finset.mem_filter.mp hd).2).symm
  have hdata :=
    component_chord_coordinate_exact hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
  constructor
  · simpa [hdeq] using hdata.2
  · refine ⟨d, hd, hdeq, ?_⟩
    simpa [hdeq] using hdata.1

#print axioms AssemblyP1.Issue94ComponentCoordinates.chordCoordinate_injective_on_component
#print axioms AssemblyP1.Issue94ComponentCoordinates.componentCoordinates_even
#print axioms AssemblyP1.Issue94ComponentCoordinates.componentCoordinate_mem_data

end AssemblyP1.Issue94ComponentCoordinates
