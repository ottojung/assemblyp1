import AssemblyP1.Issue94InterlaceKernelNatBoundary
import AssemblyP1.Issue94PhysicalChord

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

def arcBit (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K) : ZMod 2 :=
  if c.1.val ≤ x.val ∧ x.val < (AltF hK sigma c.1).val then 1 else 0

theorem prev_val
    (hK : 0 < K) (y : Fin K) :
    (prevPos hK y).val =
      if y.val = 0 then K - 1 else y.val - 1 := by
  unfold prevPos
  simp only [Fin.val_mk]
  by_cases hy : y.val = 0
  · rw [ite_eq_left hy, hy]
    have hlt : K - 1 < K := by omega
    have heq0 : 0 + K - 1 = K - 1 := by omega
    rw [heq0, Nat.mod_eq_of_lt hlt]
  · rw [ite_eq_right hy]
    have heq : y.val + K - 1 = (y.val - 1) + K := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega

theorem arcBit_boundary_val
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (y : Fin K) :
    arcBit hK sigma c (prevPos hK y) + arcBit hK sigma c y =
      if y.val = c.1.val ∨ y.val = (AltF hK sigma c.1).val then 1 else 0 := by
  have hp := prev_val hK y
  have hnat := intervalBit_boundary_nat
    (K := K) (a := c.1.val) (b := (AltF hK sigma c.1).val) (y := y.val)
    hK c.1.isLt (chord_lower hK sigma c) (AltF hK sigma c.1).isLt y.isLt
  unfold arcBit
  rw [hp]
  exact hnat

end AssemblyP1.Issue94InterlaceKernel
