import AssemblyP1.BBTEulerian
import Mathlib.Tactic.Decide

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Probe94

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerian

/-- The candidate `E` is `S4` shifted forward by one. -/
def E4 : Fin 4 → Fin 2 := fun i => BBTEulerian.S4 ⟨(i.val + 3) % 4, by omega⟩

theorem hE4 : RotEquiv BBTEulerian.hG4 E4 BBTEulerian.S4 :=
  ⟨1, fun i => rfl⟩

/-- The intermediate claim `hwin` used in `vertexCycleEq_of_RotEquiv_pullback`
at :136 is FALSE, refuted here by `decide` at `S = 0101, G = 4, L = 3`. -/
theorem hwin_false :
    ¬ (∀ i : Fin 4, window (L := 3) BBTEulerian.hG4 E4 i
        = window (L := 3) BBTEulerian.hG4 BBTEulerian.S4 i) := by
  decide

/-- ... while the theorem being proved there is not refuted: every `Matching`
pull-back for this rotational pair is vertex-cycle-trivial. -/
theorem pullback_ok :
    ∀ σ : Fin 4 → Fin 4, Matching (L := 3) BBTEulerian.hG4 BBTEulerian.S4 E4 σ →
      VertexCycleEq BBTEulerian.hG4 3 BBTEulerian.S4
        (BBTCondense.pullback BBTEulerian.hG4 3 BBTEulerian.S4 E4 σ.1)
        (Equiv.refl (α := Fin 4)) := by
  decide

end Probe94
