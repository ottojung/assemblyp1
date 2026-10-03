import AssemblyP1.BBTCandidateTransfer

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1
open AssemblyP1.BBTSequenceGraph

/-- `W = T T F F` -/
def W1 : Fin 4 → Bool := ![true, true, false, false]

/-- `E = T F T F` -/
def E1 : Fin 4 → Bool := ![true, false, true, false]

/-- `σ = (0, 2, 1, 3)` -/
def s1 : Fin 4 → Fin 4 := ![0, 2, 1, 3]

example : Function.Bijective s1 := by native_decide

example : Matching (L := 1) (by norm_num : (0 : ℕ) < 4) W1 E1 s1 := by
  refine ⟨by native_decide, ?_⟩
  intro r
  funext d
  fin_cases d
  simp [window, cyc, W1, E1, s1]
  fin_cases r <;> norm_num

end AssemblyP1.BBTEulerian
namespace AssemblyP1.BBTEulerian
open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1
open AssemblyP1.BBTSequenceGraph

theorem W1_val (i : Fin 4) : W1 i = decide (i.val < 2) := by
  fin_cases i <;> simp [W1]

theorem E1_val (i : Fin 4) : E1 i = decide (i.val % 2 = 0) := by
  fin_cases i <;> simp [E1]

private theorem notRotL1 : ¬ RotEquiv (by norm_num : (0 : ℕ) < 4) E1 W1 := by
  rintro ⟨k, hk⟩
  have hNat : ∀ i : ℕ, i < 4 →
      decide (((i + k) % 4) % 2 = 0) = decide (i < 2) := by
    intro i hi
    have h := hk ⟨i, hi⟩
    simp only [E1_val, W1_val, Fin.mk_val] at h
    exact h
  have hkey : ∀ i : ℕ, i < 4 → (i + k) % 4 = (i + k % 4) % 4 := by
    intro i hi
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, j.val = k % 4 :=
    ⟨⟨k % 4, Nat.mod_lt k (by norm_num)⟩, rfl⟩
  have hNat' : ∀ i : ℕ, i < 4 →
      decide (((i + j.val) % 4) % 2 = 0) = decide (i < 2) := by
    intro i hi
    have h := hNat i hi
    rw [hkey i hi, ← hj] at h
    exact h
  have h0 := hNat' 0 (by norm_num)
  have h1 := hNat' 1 (by norm_num)
  have h2 := hNat' 2 (by norm_num)
  have h3 := hNat' 3 (by norm_num)
  fin_cases j <;> simp at h0 h1 h2 h3

end AssemblyP1.BBTEulerian
