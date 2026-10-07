import AssemblyP1.Issue94ComponentCoordinate
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

noncomputable def chordCoordinate (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (d : AltFChord hK sigma) : ℕ :=
  pairBack hK S d.1.val (AltF hK sigma d.1).val

theorem physical_chord_eq_of_pair_eq
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    {d e : AltFChord hK sigma}
    (hpair :
      ({d.1, AltF hK sigma d.1} : Finset (Fin K)) =
        {e.1, AltF hK sigma e.1}) :
    d = e := by
  apply Subtype.ext
  have hdmem :
      d.1 ∈ ({e.1, AltF hK sigma e.1} : Finset (Fin K)) := by
    rw [← hpair]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
  rcases hdmem with hde | hdi
  · exact hde
  · have hemem :
        e.1 ∈ ({d.1, AltF hK sigma d.1} : Finset (Fin K)) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hemem
    rcases hemem with hed | hei
    · exact hed.symm
    · have hdlt := chord_lower hK sigma d
      have helt := chord_lower hK sigma e
      have h1 := congrArg Fin.val hdi
      have h2 := congrArg Fin.val hei
      omega

theorem component_chord_coordinate_exact
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    {c d : AltFChord hK sigma}
    (hcomp :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d) :
    ({d.1, AltF hK sigma d.1} : Finset (Fin K)) =
        {rotAdd hK (chordCoordinate hK S sigma d)
            (maxPairStart hK S c.1 (AltF hK sigma c.1)),
          rotAdd hK (chordCoordinate hK S sigma d)
            (maxPairStart hK S (AltF hK sigma c.1) c.1)} ∧
      chordCoordinate hK S sigma d + (L - 1) ≤
        maxPairLen hK S c.1 (AltF hK sigma c.1) := by
  let fd := AltF hK sigma d.1
  let fc := AltF hK sigma c.1
  let ell := chordCoordinate hK S sigma d
  have hd : rotAdd hK ell (maxPairStart hK S d.1 fd) = d.1 := by
    exact rotAdd_pairBack_maxPairStart hK S d.1 fd
  have hfd0 :
      rotAdd hK (pairBack hK S fd.val d.1.val)
        (maxPairStart hK S fd d.1) = fd := by
    exact rotAdd_pairBack_maxPairStart hK S fd d.1
  have hfd : rotAdd hK ell (maxPairStart hK S fd d.1) = fd := by
    dsimp [ell, chordCoordinate]
    rw [pairBack_comm hK S d.1.val fd.val] at hfd0
    exact hfd0
  have hvalid :
      ell + (L - 1) ≤ maxPairLen hK S d.1 fd := by
    exact support_chord_coordinate_valid hK L S hprim hEul
      (chord_ne_image hK sigma d) rfl
  have hse :=
    component_same_extension hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
  rcases hse with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · have hdc :
          d.1 = rotAdd hK ell (maxPairStart hK S c.1 fc) := by
        rw [h1]
        exact hd.symm
      have hfc :
          fd = rotAdd hK ell (maxPairStart hK S fc c.1) := by
        rw [h2]
        exact hfd.symm
      simpa [fd, fc, ell] using
        (finset_two_of (u := d.1) (v := fd)
          (r := rotAdd hK ell (maxPairStart hK S c.1 fc))
          (s := rotAdd hK ell (maxPairStart hK S fc c.1)) hdc hfc)
    · have hvc : vtx hK L S c.1 = vtx hK L S fc :=
        (AltF_vtx' hK S hEul c.1).symm
      have hvd : vtx hK L S d.1 = vtx hK L S fd :=
        (AltF_vtx' hK S hEul d.1).symm
      have hlen := ladder_len (L := L) hK S hprim h1 h2 hL hLK
        (chord_ne_image hK sigma c) (chord_ne_image hK sigma d) hvc hvd
      rw [← hlen.1] at hvalid
      simpa [fd, fc, ell] using hvalid
  · constructor
    · have hdc :
          d.1 = rotAdd hK ell (maxPairStart hK S fc c.1) := by
        rw [h2]
        exact hd.symm
      have hfc :
          fd = rotAdd hK ell (maxPairStart hK S c.1 fc) := by
        rw [h1]
        exact hfd.symm
      change ({d.1, fd} : Finset (Fin K)) =
        {rotAdd hK ell (maxPairStart hK S c.1 fc),
          rotAdd hK ell (maxPairStart hK S fc c.1)}
      calc
        ({d.1, fd} : Finset (Fin K)) =
            {rotAdd hK ell (maxPairStart hK S fc c.1),
              rotAdd hK ell (maxPairStart hK S c.1 fc)} := by
                exact finset_two_of hdc hfc
        _ = {rotAdd hK ell (maxPairStart hK S c.1 fc),
              rotAdd hK ell (maxPairStart hK S fc c.1)} :=
                finset_two_comm _ _
    · have hvc : vtx hK L S c.1 = vtx hK L S fc :=
        (AltF_vtx' hK S hEul c.1).symm
      have hvd : vtx hK L S fd = vtx hK L S d.1 :=
        AltF_vtx' hK S hEul d.1
      have hlen := ladder_len (L := L) hK S hprim h1 h2 hL hLK
        (chord_ne_image hK sigma c) (chord_ne_image hK sigma d).symm hvc hvd
      have hsym :
          maxPairLen hK S d.1 fd = maxPairLen hK S fd d.1 :=
        (maxPairLen_comm hK S d.1 fd).symm
      rw [hsym, ← hlen.1] at hvalid
      simpa [fd, fc, ell] using hvalid

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
