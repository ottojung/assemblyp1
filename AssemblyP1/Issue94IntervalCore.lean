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


theorem commute_intervalProd_mem
    {s : ℕ → Γ} {k a n : ℕ}
    (hcomm : ∀ j, a ≤ j → j < a + n → Commute (s k) (s j)) :
    Commute (s k) (intervalProd s a n) := by
  induction n generalizing a with
  | zero => simp [intervalProd]
  | succ n ih =>
      rw [intervalProd]
      apply Commute.mul_right
      · exact hcomm a (by omega) (by omega)
      · apply ih
        intro j hj1 hj2
        exact hcomm j (by omega) (by omega)

theorem intervalProd_inv_local
    {s : ℕ → Γ} {a n : ℕ}
    (hcomm : ∀ i j, a ≤ i → i < a + n → a ≤ j → j < a + n →
      Commute (s i) (s j))
    (hinv : ∀ i, a ≤ i → i < a + n → s i * s i = 1) :
    (intervalProd s a n)⁻¹ = intervalProd s a n := by
  induction n generalizing a with
  | zero => simp [intervalProd]
  | succ n ih =>
      rw [intervalProd, mul_inv_rev]
      have htail : (intervalProd s (a + 1) n)⁻¹ =
          intervalProd s (a + 1) n := by
        apply ih
        · intro i j hi1 hi2 hj1 hj2
          exact hcomm i j (by omega) (by omega) (by omega) (by omega)
        · intro i hi1 hi2
          exact hinv i (by omega) (by omega)
      rw [htail]
      have hsa : (s a)⁻¹ = s a := by
        have hs := hinv a (by omega) (by omega)
        calc
          (s a)⁻¹ = (s a)⁻¹ * 1 := by simp
          _ = (s a)⁻¹ * (s a * s a) := by rw [hs]
          _ = s a := by group
      rw [hsa]
      exact (commute_intervalProd_mem
        (k := a) (a := a + 1) (n := n)
        (fun j hj1 hj2 => hcomm a j (by omega) (by omega) (by omega) (by omega))).eq.symm

theorem conj_intervalProd_local
    {s : ℕ → Γ} (rho : Γ) {a n : ℕ}
    (hshift : ∀ i, a ≤ i → i < a + n →
      rho * s i * rho⁻¹ = s (i + 1)) :
    rho * intervalProd s a n * rho⁻¹ =
      intervalProd s (a + 1) n := by
  induction n generalizing a with
  | zero => simp [intervalProd]
  | succ n ih =>
      rw [intervalProd, intervalProd]
      calc
        rho * (s a * intervalProd s (a + 1) n) * rho⁻¹
            = (rho * s a * rho⁻¹) *
                (rho * intervalProd s (a + 1) n * rho⁻¹) := by group
        _ = s (a + 1) * intervalProd s (a + 1 + 1) n := by
              rw [hshift a (by omega) (by omega)]
              rw [ih (a := a + 1) (fun i hi1 hi2 =>
                hshift i (by omega) (by omega))]
        _ = s (a + 1) * intervalProd s ((a + 1) + 1) n := by rfl

theorem intervalProd_overlap_local
    {s : ℕ → Γ} {a n : ℕ}
    (hcomm : ∀ i j, a ≤ i → i ≤ a + n → a ≤ j → j ≤ a + n →
      Commute (s i) (s j))
    (hinv : ∀ i, a ≤ i → i ≤ a + n → s i * s i = 1) :
    intervalProd s a n * intervalProd s (a + 1) n =
      s a * s (a + n) := by
  induction n generalizing a with
  | zero =>
      simp only [intervalProd, mul_one]
      exact (hinv a (by omega) (by omega)).symm
  | succ n ih =>
      rw [intervalProd, intervalProd]
      have hc : Commute (intervalProd s (a + 1) n) (s (a + 1)) :=
        (commute_intervalProd_mem
          (k := a + 1) (a := a + 1) (n := n)
          (fun j hj1 hj2 =>
            hcomm (a + 1) j (by omega) (by omega) (by omega) (by omega))).symm
      calc
        (s a * intervalProd s (a + 1) n) *
              (s (a + 1) * intervalProd s (a + 1 + 1) n)
            = s a * s (a + 1) *
                (intervalProd s (a + 1) n *
                  intervalProd s (a + 1 + 1) n) := by
                    calc
                      (s a * intervalProd s (a + 1) n) *
                            (s (a + 1) * intervalProd s (a + 1 + 1) n)
                          = s a * ((intervalProd s (a + 1) n * s (a + 1)) *
                              intervalProd s (a + 1 + 1) n) := by group
                      _ = s a * ((s (a + 1) * intervalProd s (a + 1) n) *
                              intervalProd s (a + 1 + 1) n) := by rw [hc.eq]
                      _ = s a * s (a + 1) *
                            (intervalProd s (a + 1) n *
                              intervalProd s (a + 1 + 1) n) := by group
        _ = s a * s (a + 1) *
              (s (a + 1) * s ((a + 1) + n)) := by
                rw [ih
                  (fun i j hi1 hi2 hj1 hj2 =>
                    hcomm i j (by omega) (by omega) (by omega) (by omega))
                  (fun i hi1 hi2 => hinv i (by omega) (by omega))]
        _ = s a * s (a + (n + 1)) := by
              calc
                s a * s (a + 1) * (s (a + 1) * s (a + 1 + n))
                    = s a * ((s (a + 1) * s (a + 1)) * s (a + 1 + n)) := by group
                _ = s a * s (a + 1 + n) := by
                      rw [hinv (a + 1) (by omega) (by omega)]
                      simp
                _ = s a * s (a + (n + 1)) := by
                      exact congrArg (fun k => s a * s k) (by omega)

theorem intervalProd_commutator_local
    {s : ℕ → Γ} (rho : Γ) {a n : ℕ}
    (hcomm : ∀ i j, a ≤ i → i ≤ a + n → a ≤ j → j ≤ a + n →
      Commute (s i) (s j))
    (hinv : ∀ i, a ≤ i → i ≤ a + n → s i * s i = 1)
    (hshift : ∀ i, a ≤ i → i < a + n →
      rho * s i * rho⁻¹ = s (i + 1)) :
    (intervalProd s a n)⁻¹ * rho * intervalProd s a n * rho⁻¹ =
      s a * s (a + n) := by
  rw [intervalProd_inv_local
    (fun i j hi1 hi2 hj1 hj2 =>
      hcomm i j hi1 (by omega) hj1 (by omega))
    (fun i hi1 hi2 => hinv i hi1 (by omega))]
  calc
    intervalProd s a n * rho * intervalProd s a n * rho⁻¹
        = intervalProd s a n *
            (rho * intervalProd s a n * rho⁻¹) := by group
    _ = intervalProd s a n * intervalProd s (a + 1) n := by
          rw [conj_intervalProd_local rho hshift]
    _ = s a * s (a + n) := intervalProd_overlap_local hcomm hinv


#print axioms AssemblyP1.Issue94IntervalCore.intervalProd_commutator_local

end AssemblyP1.Issue94IntervalCore
