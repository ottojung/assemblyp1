import AssemblyP1.Issue94PhysicalComponent
import AssemblyP1.Issue94CoordinateValidity

namespace AssemblyP1.Issue94ComponentCoordinate

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94PhysicalComponent
open AssemblyP1.Issue94InterlaceComponents
open AssemblyP1.Issue94CoordinateValidity

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem rotAdd_pairBack_maxPairStart
    (hK : 0 < K) (S : Fin K → α) (a b : Fin K) :
    rotAdd hK (pairBack hK S a.val b.val) (maxPairStart hK S a b) = a := by
  rw [maxPairStart_eq]
  rw [rotAdd_add]
  have hle : pairBack hK S a.val b.val ≤ K :=
    (pairBack_spec hK S a.val b.val).2
  have hsum :
      pairBack hK S a.val b.val + (K - pairBack hK S a.val b.val) = K :=
    Nat.add_sub_of_le hle
  rw [hsum, rotAdd_full]

theorem component_chord_coordinate
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    {c d : AltFChord hK sigma}
    (hcomp :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d) :
    ∃ ell : ℕ,
      ({d.1, AltF hK sigma d.1} : Finset (Fin K)) =
        {rotAdd hK ell (maxPairStart hK S c.1 (AltF hK sigma c.1)),
          rotAdd hK ell (maxPairStart hK S (AltF hK sigma c.1) c.1)} ∧
      ell + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1) := by
  let fd := AltF hK sigma d.1
  let fc := AltF hK sigma c.1
  let ell := pairBack hK S d.1.val fd.val
  have hd : rotAdd hK ell (maxPairStart hK S d.1 fd) = d.1 := by
    exact rotAdd_pairBack_maxPairStart hK S d.1 fd
  have hfd0 :
      rotAdd hK (pairBack hK S fd.val d.1.val) (maxPairStart hK S fd d.1) = fd := by
    exact rotAdd_pairBack_maxPairStart hK S fd d.1
  have hfd : rotAdd hK ell (maxPairStart hK S fd d.1) = fd := by
    rw [pairBack_comm hK S d.1.val fd.val] at hfd0
    exact hfd0
  have hvalid :
      ell + (L - 1) ≤ maxPairLen hK S d.1 fd := by
    exact support_chord_coordinate_valid hK L S hprim hEul
      (chord_ne_image hK sigma d) rfl
  have hse :=
    component_same_extension hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
  rcases hse with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨ell, ?_, ?_⟩
    · have hdc :
          d.1 = rotAdd hK ell (maxPairStart hK S c.1 fc) := by
        rw [h1]
        exact hd.symm
      have hfc :
          fd = rotAdd hK ell (maxPairStart hK S fc c.1) := by
        rw [h2]
        exact hfd.symm
      simpa [fd, fc] using
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
      simpa [fd, fc] using hvalid
  · refine ⟨ell, ?_, ?_⟩
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
              rotAdd hK ell (maxPairStart hK S fc c.1)} := finset_two_comm _ _
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
      simpa [fd, fc] using hvalid

end AssemblyP1.Issue94ComponentCoordinate

#print axioms AssemblyP1.Issue94ComponentCoordinate.rotAdd_pairBack_maxPairStart
#print axioms AssemblyP1.Issue94ComponentCoordinate.component_chord_coordinate
