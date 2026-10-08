import AssemblyP1.Issue94InterlaceKernelColor

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem physicalInterlace_kerZero
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S) :
    kerZero (interlaceMatrix (altFInterlaceGraph hK S sigma)) := by
  intro z hker
  funext c
  by_contra hzc
  have hconst :=
    color_constant_of_kernel hK S sigma hEul hL hLK hprim hP2 z hker
  have hb := color_boundary_of_endpoint
    hK S sigma hEul hL hLK hprim hP2 z c c.1 (Or.inl rfl)
  have hp := hconst (AssemblyP1.BBTChords.prevPos hK c.1)
  have hc := hconst c.1
  rw [hp, hc] at hb
  have hz :
      color hK sigma z (AssemblyP1.BBTEulerian.origin hK) +
        color hK sigma z (AssemblyP1.BBTEulerian.origin hK) = 0 :=
    zmod2_add_self _
  have hzc0 : z c = 0 := by
    rw [← hb]
    exact hz
  exact hzc hzc0

#print axioms AssemblyP1.Issue94InterlaceKernel.color_constant_of_kernel
#print axioms AssemblyP1.Issue94InterlaceKernel.physicalInterlace_kerZero


theorem physicalInterlace_component_even_card
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    Even
      (componentFinset (altFInterlaceGraph hK S sigma) c).card := by
  exact AssemblyP1.Issue94InterlaceParity.interlaceComponent_even_card
    (altFInterlaceGraph hK S sigma) c
    (physicalInterlace_kerZero hK S sigma hEul hL hLK hprim hP2)

#print axioms AssemblyP1.Issue94InterlaceKernel.physicalInterlace_component_even_card


#print axioms AssemblyP1.Issue94InterlaceKernel.physical_four_distinct
#print axioms AssemblyP1.Issue94InterlaceKernel.arcBit_pair_eq_interlace

#print axioms AssemblyP1.Issue94InterlaceKernel.intervalBit_boundary_nat
#print axioms AssemblyP1.Issue94InterlaceKernel.arcBit_boundary_val

end AssemblyP1.Issue94InterlaceKernel
