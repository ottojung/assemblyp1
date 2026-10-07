import AssemblyP1.BBTEulerian

/-!
# Board 94 green restore: `hwin` is FALSE

The dead front (`94a18`) reported that the proof of
`Issue94EulerianTheta.vertexCycleEq_of_RotEquiv_pullback` introduces

  `have hwin : ∀ i, window E i = window S i`

and that this intermediate claim is false.  Here it is settled by execution, on
the smallest instance: `G = 4`, `L = 3`, `S = S4 = 0101`, and `E = S4` rotated by
one position (which *does* satisfy `RotEquiv hG4 E S4`, with `k = 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Probe94c

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction
open AssemblyP1
open AssemblyP1.BBTEulerian

private theorem mod_add (a b : Nat) : (a % 4 + b) % 4 = (a + b) % 4 := by
  rw [Nat.add_mod, Nat.add_mod]
  simp

/-- `E` is the rotation of `S4 = 0101` by one position. -/
def E4 : Fin 4 → Fin 2 := fun i => S4 ⟨(i.val + 3) % 4, Nat.mod_lt _ (by decide)⟩

/-- `E4` **is** a rotation of the truth: `RotEquiv hG4 E4 S4` with `k = 1`.  So
`hrot` holds and the theorem's hypotheses are met; only `hwin` fails. -/
theorem rot : RotEquiv hG4 E4 S4 := by
  refine ⟨1, fun i => ?_⟩
  have hmod : (((i.val + 1) % 4 + 3) % 4 : Nat) = i.val := by
    rw [mod_add]
    rw [show ((i.val + 4) % 4 : Nat) = (i.val % 4 + 4 % 4) % 4 by rw [Nat.add_mod]]
    rw [show ((i.val % 4 + 4 % 4) % 4 : Nat) = i.val % 4 by simp]
    exact Nat.mod_eq_of_lt i.isLt
  exact congrArg S4 (Fin.ext hmod)

/-- The `hwin` hypothesis is false already at `i = 0`: `window E4 0 ≠ window S4 0`. -/
theorem win0_ne : ¬ window (L := 3) hG4 E4 0 = window (L := 3) hG4 S4 0 := by
  decide

/-- ... hence `hwin` is refuted for this rotational pair. -/
theorem hwin_false :
    ¬ (∀ i : Fin 4, window (L := 3) hG4 E4 i = window (L := 3) hG4 S4 i) := by
  intro h
  exact win0_ne (h 0)

end Probe94c