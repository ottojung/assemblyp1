import AssemblyP1.Issue94ComponentCoordinate

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


end AssemblyP1.Issue94ComponentCoordinates
