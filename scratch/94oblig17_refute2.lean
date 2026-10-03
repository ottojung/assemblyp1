import AssemblyP1.BBTEulerian
import AssemblyP1.BBTEulerianSearch
import AssemblyP1.BBTCondense
import AssemblyP1.BBTChords

set_option autoImplicit false
set_option maxHeartbeats 400000

open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords

namespace Test

theorem hG4 : 0 < 4 := by norm_num

def W : Fin 4 → Bool := ![false, false, false, true]
def E : Fin 4 → Bool := ![false, false, true, false]

/-- The matching used below: truth start `r` is paired with the candidate
start carrying the same length-`2` read. -/
def sg : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2

theorem sg_bijective : Function.Bijective sg := by decide

theorem sg_matching : Matching (L := 2) hG4 W E sg := by
  refine ⟨sg_bijective, fun r => ?_⟩
  fin_cases r <;> decide

/-- `E` is a cyclic shift of `W` by three positions. -/
theorem rotEquiv_E_W : RotEquiv hG4 E W := ⟨3, by decide⟩

/-- The pull-back of that matching is *not* a rotational vertex cycle.
This refutes the `←` half of clause 2 of `CandidateTransfer` as stated,
i.e. for an arbitrary `Matching`; see the report for the corrected form. -/
theorem not_vertexCycleEq_pullback :
    ¬ VertexCycleEq hG4 2 W (pullback hG4 2 W E sg_bijective) (Equiv.refl (α := Fin 4)) := by
  rintro ⟨k₀, hk⟩
  -- `pullback_window` turns the unknown pull-back start into the concrete one.
  have hpb : ∀ i : Fin 4,
      vtx hG4 2 W (pullback hG4 2 W E sg_bijective i) = vtx hG4 2 E i := by
    intro i
    have h := pullback_window (L := 2) hG4 W E sg_matching i
    ext d
    fin_cases d
    exact congrArg (fun f : Fin 2 → Bool => f ⟨0, by norm_num⟩) h
  have hclaim : ∀ i : Fin 4, vtx hG4 2 W (rotAdd hG4 k₀ i) = vtx hG4 2 E i := by
    intro i
    have h := hk i
    rw [hpb i] at h
    simpa only [Equiv.refl_apply] using h.symm
  fin_cases k₀
  · exact absurd (hclaim (2 : Fin 4)) (by decide)
  · exact absurd (hclaim (2 : Fin 4)) (by decide)
  · exact absurd (hclaim (2 : Fin 4)) (by decide)
  · exact absurd (hclaim (2 : Fin 4)) (by decide)

end Test
