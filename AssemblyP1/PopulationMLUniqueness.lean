import Mathlib
import AssemblyP1.PopulationUniqueness

/-!
# Scratch: Gibbs/KL population layer
-/

namespace Scratch

open BigOperators

variable {W : Type} [Fintype W]

/-- `p(w) = c(w) / n`. -/
noncomputable def popProb (c : W → ℕ) (n : ℕ) (w : W) : ℝ := (c w : ℝ) / (n : ℝ)

theorem popProb_nonneg (c : W → ℕ) (n : ℕ) (w : W) : 0 ≤ popProb c n w := by
  unfold popProb; positivity

theorem popProb_sum_eq_one (c : W → ℕ) (hsum : (∑ w, c w) = n) (hn : 0 < n) :
    (∑ w, popProb c n w) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hn.ne'
  have hcast : (∑ w, (c w : ℝ)) = (n : ℝ) := by exact_mod_cast hsum
  unfold popProb
  calc (∑ w, (c w : ℝ) / (n : ℝ)) = (∑ w, (c w : ℝ)) / (n : ℝ) := by
        symm
        exact Finset.sum_div (s := (Finset.univ : Finset W))
          (f := fun w : W => (c w : ℝ)) (a := (n : ℝ))
    _ = (n : ℝ) / (n : ℝ) := by rw [hcast]
    _ = 1 := by field_simp

/-- Population log-likelihood `ℓpop_S(D) = ∑_w p_S(w) log p_D(w)`. -/
noncomputable def PopLogLik (pS pD : W → ℝ) : ℝ := ∑ w, pS w * Real.log (pD w)

/-- Candidate/truth read-type supports agree. -/
def SuppEq (pS pD : W → ℝ) : Prop := ∀ w, (0 < pS w ↔ 0 < pD w)

/-- Strict form of `log t ≤ t - 1`. -/
theorem Real.log_lt_sub_one_of_ne_one {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) :
    Real.log x < x - 1 := by
  have hne : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx h1
  have h := Real.add_one_lt_exp hne
  rw [Real.exp_log hx] at h
  linarith

/-- A read distribution is nonnegative and sums to `1`. -/
def IsProb (p : W → ℝ) : Prop :=
  (∀ w, 0 ≤ p w) ∧ (∑ w, p w) = 1

/-- A normalized integer spectrum is a read distribution. -/
theorem popProb_isProb (c : W → ℕ) (hsum : (∑ w, c w) = n) (hn : 0 < n) :
    IsProb (popProb c n) := by
  refine ⟨fun w => popProb_nonneg c n w, ?_⟩
  exact popProb_sum_eq_one c hsum hn

/-- Strict form of `1 - 1/x ≤ log x`. -/
theorem Real.one_sub_inv_lt_log_of_ne_one {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) :
    1 - x⁻¹ < Real.log x := by
  have h := Real.log_lt_sub_one_of_ne_one (inv_pos.mpr hx) ((inv_ne_one.mpr h1))
  rw [Real.log_inv] at h
  linarith

/-- The Gibbs pointwise bound: `p_S log p_S - p_S log p_D ≥ p_S - p_D`
whenever the supports agree and both are nonnegative. -/
theorem term_ge {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS0 : ∀ w, 0 ≤ pS w)
    (hD0 : ∀ w, 0 ≤ pD w) (w : W) :
    pS w * Real.log (pS w) - pS w * Real.log (pD w) ≥ pS w - pD w := by
  by_cases hs : pS w = 0
  · have hz : pD w = 0 := by
      by_contra hcon
      have hpos : 0 < pS w :=
        (hSupp w).mpr (lt_of_le_of_ne (hD0 w) (Ne.symm hcon))
      rw [hs] at hpos
      exact lt_irrefl 0 hpos
    simp [hs, hz, Real.log_zero]
  · have hs0 : 0 < pS w := lt_of_le_of_ne (hS0 w) (Ne.symm hs)
    have hd0 : 0 < pD w := (hSupp w).mp hs0
    have hneS : pS w ≠ 0 := hs0.ne'
    have hneD : pD w ≠ 0 := hd0.ne'
    have hlb := Real.one_sub_inv_le_log_of_pos (div_pos hs0 hd0)
    rw [inv_div] at hlb
    have hlog : Real.log (pS w / pD w) = Real.log (pS w) - Real.log (pD w) :=
      Real.log_div hneS hneD
    have hmul := mul_le_mul_of_nonneg_left hlb (le_of_lt hs0)
    have hdiv : pS w * (pD w / pS w) = pD w := by field_simp
    calc pS w * Real.log (pS w) - pS w * Real.log (pD w)
        = pS w * (Real.log (pS w) - Real.log (pD w)) := by ring
      _ = pS w * Real.log (pS w / pD w) := by rw [hlog]
      _ ≥ pS w * (1 - pD w / pS w) := hmul
      _ = pS w - pD w := by linarith

/-- The Gibbs excess of a candidate against the truth:
`p_S log p_S - p_S log p_D - (p_S - p_D)`. -/
noncomputable def KLExcess (pS pD : W → ℝ) (w : W) : ℝ :=
  (pS w * Real.log (pS w) - pS w * Real.log (pD w)) - (pS w - pD w)

/-- A population tie: candidate and truth have the same read types and the
same population log-likelihood. -/
def PopTie (pS pD : W → ℝ) : Prop :=
  SuppEq pS pD ∧ PopLogLik pS pD = PopLogLik pS pS

theorem sum_second_eq_zero {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    (∑ w, (pS w - pD w)) = 0 := by
  rw [Finset.sum_sub_distrib, hS.2, hD.2, sub_self]

theorem klExcess_nonneg {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS0 : ∀ w, 0 ≤ pS w)
    (hD0 : ∀ w, 0 ≤ pD w) (w : W) : 0 ≤ KLExcess pS pD w :=
  sub_nonneg.mpr (term_ge hSupp hS0 hD0 w)

theorem logLik_sub (pS pD : W → ℝ) :
    (∑ w, (pS w * Real.log (pS w))) - (∑ w, (pS w * Real.log (pD w)))
      = ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) := by
  rw [Finset.sum_sub_distrib]

theorem sum_first_eq (pS pD : W → ℝ) :
    (∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)))
      = (∑ w, (pS w - pD w)) + ∑ w, KLExcess pS pD w := by
  have h : (∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)))
      = ∑ w, (KLExcess pS pD w + (pS w - pD w)) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold KLExcess
    ring
  rw [h, Finset.sum_add_distrib, add_comm]

theorem sum_first_nonneg {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS : IsProb pS)
    (hD : IsProb pD) :
    0 ≤ ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) := by
  have h1 : 0 ≤ (∑ w, KLExcess pS pD w) :=
    Finset.sum_nonneg fun w _ => klExcess_nonneg hSupp hS.1 hD.1 w
  rw [sum_first_eq, sum_second_eq_zero hS hD]
  linarith

/-- **Gibbs inequality (Cover--Thomas), population form.** For read
distributions `p_S`, `p_D` with equal support, the truth maximizes the
population log-likelihood. -/
theorem popLogLik_le_self {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD)
    (hSupp : SuppEq pS pD) :
    PopLogLik pS pD ≤ PopLogLik pS pS := by
  unfold PopLogLik
  have h1 := sum_first_nonneg hSupp hS hD
  rw [← logLik_sub] at h1
  linarith

/-- **Gibbs equality characterization.** A population tie between two read
distributions with the same support forces the distributions to be equal. -/
theorem popTie_iff {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    PopTie pS pD ↔ pD = pS := by
  constructor
  · rintro ⟨hSupp, heq⟩
    have h1 : ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) = 0 := by
      rw [← logLik_sub]
      simp only [PopLogLik] at heq
      linarith
    have hex : ∀ w, KLExcess pS pD w = 0 := by
      intro w
      have hsum : (∑ x, KLExcess pS pD x) = 0 := by
        have h := sum_first_eq pS pD
        rw [h1, sum_second_eq_zero hS hD] at h
        simpa only [zero_add] using h.symm
      have hle := Finset.single_le_sum
        (fun i _ => klExcess_nonneg hSupp hS.1 hD.1 i) (Finset.mem_univ w)
      rw [hsum] at hle
      have hne' := klExcess_nonneg hSupp hS.1 hD.1 w
      linarith
    funext w
    by_cases hs : pS w = 0
    · have hpos : ¬ 0 < pS w := by rw [hs]; exact lt_irrefl 0
      have hz : pD w = 0 := by
        by_contra hcon
        exact hpos ((hSupp w).mpr (lt_of_le_of_ne (hD.1 w) (Ne.symm hcon)))
      rw [hs, hz]
    · have hs0 : 0 < pS w := lt_of_le_of_ne (hS.1 w) (Ne.symm hs)
      have hd0 : 0 < pD w := (hSupp w).mp hs0
      have hz : KLExcess pS pD w = 0 := hex w
      by_cases hne : pS w / pD w = 1
      · have hself : pS w = (pS w / pD w) * pD w := by field_simp
        rw [hne, one_mul] at hself
        exact hself.symm
      · exfalso
        have hlt := Real.one_sub_inv_lt_log_of_ne_one (div_pos hs0 hd0) hne
        have hmul := mul_lt_mul_of_pos_left hlt hs0
        have hdiv : pS w * (pD w / pS w) = pD w := by field_simp
        have hlog : Real.log (pS w / pD w) = Real.log (pS w) - Real.log (pD w) :=
          Real.log_div hs0.ne' hd0.ne'
        rw [inv_div] at hmul
        have hmul' : pS w * (1 - pD w / pS w)
            < pS w * (Real.log (pS w) - Real.log (pD w)) := by
          rw [← hlog]
          exact hmul
        have hself : pS w * (1 - pD w / pS w) = pS w - pD w := by linarith
        have h3 : pS w - pD w < pS w * (Real.log (pS w) - Real.log (pD w)) := by
          rw [hself] at hmul'
          exact hmul'
        have hz' : pS w * Real.log (pS w) - pS w * Real.log (pD w) = pS w - pD w := by
          unfold KLExcess at hz
          linarith
        linarith
  · intro h
    refine ⟨fun w => ?_, ?_⟩
    · simp only [h]
    · simp [PopLogLik, h]

end Scratch
