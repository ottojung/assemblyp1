import AssemblyP1.Issue94PhysicalChord
import AssemblyP1.Issue94InterlaceComponents

set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94PhysicalComponent

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94InterlaceComponents

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem reachable_interlaceConnected
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    {c d : AltFChord hK sigma}
    (hreach : (altFInterlaceGraph hK S sigma).Reachable c d) :
    InterlaceConnected hK S sigma c.1 d.1 := by
  rcases hreach with ⟨w⟩
  induction w with
  | nil =>
      exact InterlaceConnected.refl _
  | @cons u v z huv p ih =>
      apply InterlaceConnected.step
      · exact huv
      · exact ih

theorem component_same_extension
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    {c d : AltFChord hK sigma}
    (hcomp :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d) :
    SameExtension K hK S
      c.1 (AltF hK sigma c.1)
      d.1 (AltF hK sigma d.1) := by
  apply connected_block hK hL hLK S hP2 hprim hUkk sigma hEul
  apply reachable_interlaceConnected hK S sigma
  exact SimpleGraph.ConnectedComponent.exact hcomp

#print axioms AssemblyP1.Issue94PhysicalComponent.reachable_interlaceConnected
#print axioms AssemblyP1.Issue94PhysicalComponent.component_same_extension

end AssemblyP1.Issue94PhysicalComponent
