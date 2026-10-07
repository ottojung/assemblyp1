import AssemblyP1.Issue94ComponentDeleteEulerian
import AssemblyP1.Issue94ComponentResidual
import AssemblyP1.Issue94PhysicalChord
import AssemblyP1.Issue94SupportDescent

namespace AssemblyP1.Issue94P2SupportDescent

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94SupportDescent
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94ComponentResidual
open AssemblyP1.Issue94ComponentDeleteEulerian

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- A single P2/primitive support-descent step follows once one component
admits a vertex-preserving antiderivative commuting with its residual. -/
theorem support_descent_step_of_P2Prim
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hpos : 0 < supportMeasure hK sigma)
    (hantider :
      ∀ c : AltFChord hK sigma,
        ∃ g : Fin K ≃ Fin K,
          (∀ x : Fin K,
            componentSwitch hK S sigma hEul hL hLK hprim hP2 c x
              = g.symm (nextPos hK (g (prevPos hK x)))) ∧
          (∀ x : Fin K,
            g (componentResidual hK S sigma hEul hL hLK hprim hP2 c x)
              = componentResidual hK S sigma hEul hL hLK hprim hP2 c (g x)) ∧
          (∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x)) :
    ∃ tau : Fin K ≃ Fin K,
      EulerianCycle hK L S tau ∧
      supportMeasure hK tau < supportMeasure hK sigma ∧
      PointwiseVtxEq hK L S sigma tau := by
  have hcard : 0 < (Support (AltF hK sigma)).card := by
    simpa [supportMeasure] using hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
  have hne : AltF hK sigma a ≠ a := by
    simpa [mem_Support] using ha
  obtain ⟨c, _hc⟩ :=
    exists_physical_chord_of_support hK S sigma hEul hL hLK hprim hP2 hne
  obtain ⟨g, hcob, hcomm, hgVtx⟩ := hantider c
  have hdel := delete_component_eulerian
    hK L S sigma g
    (componentSwitch hK S sigma hEul hL hLK hprim hP2 c)
    (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
    (fun x => altF_eq_switch_residual hK S sigma hEul hL hLK hprim hP2 c x)
    (fun x => switch_residual_commute hK S sigma hEul hL hLK hprim hP2 c x)
    hcomm hcob hgVtx
    (residual_preserves_vtx hK S sigma hEul hL hLK hprim hP2 c)
  change
    (∀ q : Fin K,
      AltF hK (sigma.trans g) q =
        componentResidual hK S sigma hEul hL hLK hprim hP2 c q) ∧
    (∀ i : Fin K,
      vtx hK L S ((sigma.trans g) i) = vtx hK L S (sigma i)) ∧
    EulerianCycle hK L S (sigma.trans g) at hdel
  rcases hdel with ⟨hAltTau, hVtxTau, hEulTau⟩
  refine ⟨sigma.trans g, hEulTau, ?_, ?_⟩
  · have hres :=
      residual_support_lt hK S sigma hEul hL hLK hprim hP2 c
    have hfun :
        AltF hK (sigma.trans g) =
          componentResidual hK S sigma hEul hL hLK hprim hP2 c :=
      funext hAltTau
    simpa [supportMeasure, hfun] using hres
  · intro i
    exact (hVtxTau i).symm

#print axioms AssemblyP1.Issue94P2SupportDescent.support_descent_step_of_P2Prim

end AssemblyP1.Issue94P2SupportDescent
