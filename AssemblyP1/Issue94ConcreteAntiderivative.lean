import AssemblyP1.Issue94ComponentCoboundary
import AssemblyP1.Issue94ComponentSwitchProduct
import AssemblyP1.Issue94ComponentResidualCommute
import AssemblyP1.Issue94ComponentAntiderivativeVtx
import AssemblyP1.Issue94P2SupportDescent
import AssemblyP1.Issue94SupportDescentAdapter
import AssemblyP1.P2RepeatResidual

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ConcreteAntiderivative

open SourceFaithfulIs
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94IntervalCore
open AssemblyP1.Issue94EvenPairing
open AssemblyP1.Issue94ComponentCoordinates
open AssemblyP1.Issue94ComponentCoboundary
open AssemblyP1.Issue94ComponentSwitchProduct
open AssemblyP1.Issue94ComponentResidual
open AssemblyP1.Issue94ComponentResidualCommute
open AssemblyP1.Issue94ComponentAntiderivativeVtx
open AssemblyP1.Issue94CommutatorProduct
open AssemblyP1.Issue94P2SupportDescent
open AssemblyP1.Issue94SupportDescentAdapter

variable {α : Type} [DecidableEq α] [Fintype α] {K L : ℕ}

noncomputable def componentAntiderivative
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) : Equiv.Perm (Fin K) :=
  ((coordinatePairs (componentCoordinates hK S sigma c)).map
    (fun p => intervalProd
      (alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1))
      p.1 (p.2 - p.1))).prod

theorem componentAntiderivative_coboundary
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c x =
        (componentAntiderivative hK S sigma c).symm
          (nextPos hK
            (componentAntiderivative hK S sigma c (prevPos hK x))) := by
  have hEven : Even (componentCoordinates hK S sigma c).card :=
    componentCoordinates_even hK hL hLK S hP2 hprim hUkk sigma hEul c
  have hvalid :
      ∀ i ∈ componentCoordinates hK S sigma c,
        i + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1) := by
    intro i hi
    exact (componentCoordinate_mem_data
      hK hL hLK S hP2 hprim hUkk sigma hEul c hi).1
  have hcob :=
    coordinatePairs_coboundary_prod
      hK hL hLK S hprim hP2 sigma hEul
      c.1 (AltF hK sigma c.1)
      (chord_ne_image hK sigma c) rfl
      (componentCoordinates hK S sigma c) hEven hvalid
  have hboundary :=
    coordinatePairs_boundary_eq_componentSwitch
      hK hL hLK S hP2 hprim hUkk sigma hEul c
  have heq :
      coboundary (rhoEquiv hK) (componentAntiderivative hK S sigma c) =
        componentSwitch hK S sigma hEul hL hLK hprim hP2 c := by
    exact hcob.trans hboundary
  intro x
  have hx := congrArg (fun f : Equiv.Perm (Fin K) => f x) heq
  simpa [componentAntiderivative, coboundary, Equiv.Perm.mul_apply] using hx.symm

theorem componentAntiderivative_commutes_residual
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      componentAntiderivative hK S sigma c
          (componentResidual hK S sigma hEul hL hLK hprim hP2 c x) =
        componentResidual hK S sigma hEul hL hLK hprim hP2 c
          (componentAntiderivative hK S sigma c x) := by
  simpa [componentAntiderivative] using
    coordinatePairs_antiderivative_commute_componentResidual
      hK S sigma hEul hL hLK hprim hP2 hUkk c

theorem componentAntiderivative_preserves_vtx
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      vtx hK L S (componentAntiderivative hK S sigma c x) =
        vtx hK L S x := by
  simpa [componentAntiderivative] using
    coordinatePairs_antiderivative_preserves_vtx
      hK S sigma hEul hL hLK hprim hP2 hUkk c

theorem componentAntiderivative_witness
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    ∃ g : Fin K ≃ Fin K,
      (∀ x : Fin K,
        componentSwitch hK S sigma hEul hL hLK hprim hP2 c x =
          g.symm (nextPos hK (g (prevPos hK x)))) ∧
      (∀ x : Fin K,
        g (componentResidual hK S sigma hEul hL hLK hprim hP2 c x) =
          componentResidual hK S sigma hEul hL hLK hprim hP2 c (g x)) ∧
      (∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) := by
  refine ⟨componentAntiderivative hK S sigma c, ?_, ?_, ?_⟩
  · exact componentAntiderivative_coboundary
      hK hL hLK S hP2 hprim hUkk sigma hEul c
  · exact componentAntiderivative_commutes_residual
      hK hL hLK S hP2 hprim hUkk sigma hEul c
  · exact componentAntiderivative_preserves_vtx
      hK hL hLK S hP2 hprim hUkk sigma hEul c

theorem concrete_p2PrimSupportDescentStep (hL : 2 ≤ L) :
    P2PrimSupportDescentStep (α := α) L := by
  intro K hK W hLK hP2 hPrim σ hEul hpos
  have hprim : RepeatAdapter.IsPrimitive hK W :=
    IsPrimitive.shiftPrimitive hK hPrim
  have hUkk : Ukkonen hK L W :=
    P2.imp_Ukkonen hL hP2
  apply support_descent_step_of_P2Prim
    hK hL hLK W hprim hP2 σ hEul hpos
  intro c
  exact componentAntiderivative_witness
    hK hL hLK W hP2 hprim hUkk σ hEul c

theorem concrete_p2LongUnique (hL : 2 ≤ L) :
    AssemblyP1.Issue94Interface.P2LongUnique (α := α) L :=
  p2LongUnique_of_p2PrimSupportDescentStep hL
    (concrete_p2PrimSupportDescentStep hL)

#print axioms AssemblyP1.Issue94ConcreteAntiderivative.componentAntiderivative_witness
#print axioms AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2PrimSupportDescentStep
#print axioms AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2LongUnique

end AssemblyP1.Issue94ConcreteAntiderivative
