import AssemblyP1.Issue94ComponentAlgebra

namespace AssemblyP1.Issue94IntervalCore

variable {Γ : Type*} [Group Γ]

def intervalProd (s : ℕ → Γ) (a : ℕ) : ℕ → Γ
  | 0 => 1
  | n + 1 => s a * intervalProd s (a + 1) n

theorem commute_intervalProd
    {s : ℕ → Γ} (hcomm : ∀ i j, Commute (s i) (s j))
    (k a n : ℕ) :
    Commute (s k) (intervalProd s a n) := by
  induction n generalizing a with
  | zero => simp [intervalProd]
  | succ n ih =>
      change s k * (s a * intervalProd s (a + 1) n) =
        (s a * intervalProd s (a + 1) n) * s k
      have hka := (hcomm k a).eq
      have ht := (ih (a := a + 1)).eq
      calc
        s k * (s a * intervalProd s (a + 1) n) =
            (s k * s a) * intervalProd s (a + 1) n := by rw [mul_assoc]
        _ = (s a * s k) * intervalProd s (a + 1) n := by rw [hka]
        _ = s a * (s k * intervalProd s (a + 1) n) := by rw [mul_assoc]
        _ = s a * (intervalProd s (a + 1) n * s k) := by rw [ht]
        _ = (s a * intervalProd s (a + 1) n) * s k := by rw [mul_assoc]

theorem intervalProd_inv
    {s : ℕ → Γ} (hcomm : ∀ i j, Commute (s i) (s j))
    (hinv : ∀ i, s i * s i = 1)
    (a n : ℕ) :
    (intervalProd s a n)⁻¹ = intervalProd s a n := by
  induction n generalizing a with
  | zero => simp [intervalProd]
  | succ n ih =>
      change (s a * intervalProd s (a + 1) n)⁻¹ =
        s a * intervalProd s (a + 1) n
      have hsa : (s a)⁻¹ = s a := by
        calc
          (s a)⁻¹ = (s a)⁻¹ * 1 := by simp
          _ = (s a)⁻¹ * (s a * s a) := by rw [hinv a]
          _ = ((s a)⁻¹ * s a) * s a := by rw [mul_assoc]
          _ = s a := by simp
      rw [mul_inv_rev, ih (a := a + 1), hsa]
      exact (commute_intervalProd hcomm a (a + 1) n).eq.symm

#print axioms AssemblyP1.Issue94IntervalCore.intervalProd_inv

end AssemblyP1.Issue94IntervalCore
