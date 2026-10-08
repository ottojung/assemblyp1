import AssemblyP1.Issue94PhysicalChord
import AssemblyP1.Issue94IterSlide
import AssemblyP1.Issue94CLEDeletion
import Mathlib.Data.ZMod.Basic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- Pure arithmetic form of the boundary of a half-open interval [a,b) on
the linearly represented circle. -/
theorem intervalBit_boundary_nat
    {K a b y : ℕ}
    (hK : 0 < K) (haK : a < K) (hab : a < b)
    (hbK : b < K) (hyK : y < K) :
    (if a ≤ (if y = 0 then K - 1 else y - 1) ∧
          (if y = 0 then K - 1 else y - 1) < b
      then (1 : ZMod 2) else 0) +
      (if a ≤ y ∧ y < b then 1 else 0)
      =
      (if y = a ∨ y = b then 1 else 0) := by
  by_cases hy0 : y = 0
  · subst y
    simp only [ite_eq_left_iff]
    by_cases ha0 : a = 0
    · subst a
      have hbpos : 0 < b := by omega
      have hK1 : ¬ K - 1 < b := by omega
      simp [hK1, hbpos]
    · have hK1 : ¬ K - 1 < b := by omega
      have h0a : ¬ (0 : ℕ) = a := by omega
      have h0b : ¬ (0 : ℕ) = b := by omega
      simp [ha0, hK1, h0a, h0b]
  · rw [ite_eq_right hy0]
    by_cases hya : y = a
    · subst y
      have hprev : ¬ a ≤ a - 1 := by omega
      simp [hprev, hab]
    · by_cases hyb : y = b
      · subst y
        have h1 : a ≤ b - 1 := by omega
        have h2 : b - 1 < b := by omega
        simp [hya, h1, h2]
      · by_cases hylt : y < a
        · have hnot1 : ¬ a ≤ y - 1 := by omega
          have hnot2 : ¬ a ≤ y := by omega
          simp [hya, hyb, hnot1, hnot2]
        · by_cases hyin : y < b
          · have hay : a ≤ y := by omega
            have hp_ge : a ≤ y - 1 := by omega
            have hp_lt : y - 1 < b := by omega
            simp [hya, hyb, hay, hyin, hp_ge, hp_lt]
            have htwo : (1 : ZMod 2) + 1 = 0 := by decide
            exact htwo
          · have hcur : ¬ (a ≤ y ∧ y < b) := by omega
            have hpre : ¬ (a ≤ y - 1 ∧ y - 1 < b) := by omega
            simp [hya, hyb, hcur, hpre]

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
