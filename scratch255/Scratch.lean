import AssemblyP1.FixedXExactML
open Finset BigOperators

namespace AssemblyP1.FixedXExactML

def S255 : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]
def AA : Fin 2 → Fin 2 := fun _ => 0
def AB : Fin 2 → Fin 2 := fun i => if i = 0 then 0 else 1
def BB : Fin 2 → Fin 2 := fun _ => 1
def BA : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
def nodeA : Fin 1 → Fin 2 := fun _ => 0
def nodeB : Fin 1 → Fin 2 := fun _ => 1
def E255 : Finset (Fin 2 → Fin 2) := {AA, AB, BB, BA}

def B1 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 2 else if w = AB then 1 else if w = BB then 2 else if w = BA then 1 else 0
def B2 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 1 else if w = AB then 1 else if w = BB then 3 else if w = BA then 1 else 0
def B3 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 3 else if w = AB then 1 else if w = BB then 1 else if w = BA then 1 else 0
def B4 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 1 else if w = AB then 2 else if w = BB then 1 else if w = BA then 2 else 0

def x1 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 2 else if w = AB then 1 else if w = BB then 2 else if w = BA then 1 else 0
def xT : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 1 else if w = AB then 1 else if w = BB then 1 else if w = BA then 1 else 0
def x2 : (Fin 2 → Fin 2) → ℕ := fun w => if w = AA then 1 else if w = AB then 2 else if w = BB then 1 else if w = BA then 2 else 0

theorem word_cases (w : Fin 2 → Fin 2) : w = AA ∨ w = AB ∨ w = BB ∨ w = BA := by
  by_cases h0 : (w 0).val = 0
  · by_cases h1 : (w 1).val = 0
    · left; exact funext fun i => by
        fin_cases i
        · exact Fin.ext h0
        · exact Fin.ext h1
    · right; left
      have h1' : (w 1).val = 1 := by have := Fin.is_lt (w 1); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.ext h0
        · exact Fin.ext (Fin.val_injective h1')
  · by_cases h1 : (w 1).val = 0
    · right; right; right
      have h0' : (w 0).val = 1 := by have := Fin.is_lt (w 0); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.ext (Fin.val_injective h0')
        · exact Fin.ext h1
    · right; right; left
      have h0' : (w 0).val = 1 := by have := Fin.is_lt (w 0); omega
      have h1' : (w 1).val = 1 := by have := Fin.is_lt (w 1); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.ext (Fin.val_injective h0')
        · exact Fin.ext (Fin.val_injective h1')

theorem hsup255 : (OrientedRigidity.support (L := 2) (by decide) S255) = E255 := by decide
theorem hnodes255 : (OrientedRigidity.genomeNodes (L := 2) (by decide) S255) = {nodeA, nodeB} := by decide

theorem specCount_S255_eq_B1 : ∀ w, OrientedRigidity.specCount (L := 2) (by decide) S255 w = B1 w := by
  intro w; fin_cases w <;> decide

-- likProduct computations (all by decide)
theorem lp_B1_x1 : likProduct E255 B1 x1 = 16 := by unfold likProduct; decide
theorem lp_B2_x1 : likProduct E255 B2 x1 = 9 := by unfold likProduct; decide
theorem lp_B3_x1 : likProduct E255 B3 x1 = 9 := by unfold likProduct; decide
theorem lp_B4_x1 : likProduct E255 B4 x1 = 4 := by unfold likProduct; decide
theorem lp_B1_xT : likProduct E255 B1 xT = 4 := by unfold likProduct; decide
theorem lp_B2_xT : likProduct E255 B2 xT = 3 := by unfold likProduct; decide
theorem lp_B3_xT : likProduct E255 B3 xT = 3 := by unfold likProduct; decide
theorem lp_B4_xT : likProduct E255 B4 xT = 4 := by unfold likProduct; decide
theorem lp_B1_x2 : likProduct E255 B1 x2 = 4 := by unfold likProduct; decide
theorem lp_B2_x2 : likProduct E255 B2 x2 = 3 := by unfold likProduct; decide
theorem lp_B3_x2 : likProduct E255 B3 x2 = 3 := by unfold likProduct; decide
theorem lp_B4_x2 : likProduct E255 B4 x2 = 16 := by unfold likProduct; decide

end AssemblyP1.FixedXExactML
