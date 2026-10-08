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


end AssemblyP1.Issue94InterlaceKernel
