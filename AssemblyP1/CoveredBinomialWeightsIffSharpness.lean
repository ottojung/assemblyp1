import AssemblyP1.CoveredBinomialWeightsIff

/-!
# Sharpness of the covered-sample product-binomial classification (#259)

`AssemblyP1.CoveredBinomialWeightsIff.covered_product_le_iff_zero_or_pointwise`
classifies uniform covered-sample maximality for the MB09 §6.1 product-binomial
surrogate by the disjunction

`(∃ e, qB e = 0) ∨ (∀ e, qB e ≤ qA e)`.

This module records the **non-vacuity / sharpness** of that classification:
neither disjunct is redundant.  Dropping the zero-weight disjunct (keeping only
the pointwise inequality) makes the equivalence false, and dropping the
pointwise inequality (keeping only the zero-weight disjunct) also makes the
equivalence false.  Both failures are exhibited on `E = Fin 2` with the truth
weights and coverage baseline strictly positive, so the hypotheses of the
classification are satisfied.

The two counterexamples are:

* **Zero-weight disjunct is indispensable.**  Take `qA = (1, 1)`,
  `qB = (0, 5)`, baseline `a = (1, 1)`.  Every covered sample observes
  coordinate `0` at least once, so `qB 0 ^ x 0 = 0` and the competitor product
  is `0 ≤ ∏ qA ^ x`; the left-hand side holds.  But `qB 1 = 5 > 1 = qA 1`, so
  the pointwise inequality fails.  Hence `LHS ↔ (∀ e, qB e ≤ qA e)` is false.

* **Pointwise disjunct is indispensable.**  Take `qA = qB = (1, 1)`, baseline
  `a = (1, 1)`.  The left-hand side holds with equality, and no `qB e` is
  zero, so `LHS ↔ (∃ e, qB e = 0)` is false.
-/

namespace AssemblyP1.CoveredBinomialWeightsIffSharpness

open Finset BigOperators

/-- Dropping the zero-weight disjunct breaks the classification: there are
positive truth weights and a positive baseline for which the competitor is
dominated on every covered sample yet is not pointwise dominated. -/
theorem iff_needs_zero_disjunct :
    ¬ (∀ (qA qB a : Fin 2 → ℕ), (∀ e, 0 < qA e) → (∀ e, 0 < a e) →
      ((∀ x : Fin 2 → ℕ, (∀ e, a e ≤ x e) →
          (∏ e : Fin 2, qB e ^ x e) ≤ (∏ e : Fin 2, qA e ^ x e)) ↔
        (∀ e, qB e ≤ qA e))) := by
  intro h
  have hiff := h (fun _ => 1) (fun e => if e = 0 then 0 else 5) (fun _ => 1)
    (by intro e; norm_num) (by intro e; norm_num)
  have hLHS : (∀ x : Fin 2 → ℕ, (∀ e, (1 : ℕ) ≤ x e) →
      (∏ e : Fin 2, (fun e => if e = 0 then 0 else 5) e ^ x e) ≤
        (∏ e : Fin 2, (1 : ℕ) ^ x e)) := by
    intro x hx
    have hx0 : x 0 ≠ 0 := by have := hx 0; omega
    have hz : (fun e : Fin 2 => if e = 0 then 0 else 5) 0 ^ x 0 = 0 := by
      simp [hx0]
    have hprod : (∏ e : Fin 2, (fun e => if e = 0 then 0 else 5) e ^ x e) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) hz
    rw [hprod]
    exact Nat.zero_le _
  have hpt : ¬ (∀ e : Fin 2, (fun e => if e = 0 then 0 else 5) e ≤ 1) := by
    intro hh
    have h1 := hh 1
    norm_num at h1
  exact hpt (hiff.mp hLHS)

/-- Dropping the pointwise-inequality disjunct breaks the classification:
there are positive truth weights and a positive baseline for which the
competitor is dominated on every covered sample and has no zero weight. -/
theorem iff_needs_pointwise_disjunct :
    ¬ (∀ (qA qB a : Fin 2 → ℕ), (∀ e, 0 < qA e) → (∀ e, 0 < a e) →
      ((∀ x : Fin 2 → ℕ, (∀ e, a e ≤ x e) →
          (∏ e : Fin 2, qB e ^ x e) ≤ (∏ e : Fin 2, qA e ^ x e)) ↔
        (∃ e, qB e = 0))) := by
  intro h
  have hiff := h (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (by intro e; norm_num) (by intro e; norm_num)
  have hLHS : (∀ x : Fin 2 → ℕ, (∀ e, (1 : ℕ) ≤ x e) →
      (∏ e : Fin 2, (1 : ℕ) ^ x e) ≤ (∏ e : Fin 2, (1 : ℕ) ^ x e)) := by
    intro x hx; simp
  have hno : ¬ (∃ e : Fin 2, (fun _ : Fin 2 => (1 : ℕ)) e = 0) := by
    rintro ⟨e, he⟩; exact one_ne_zero he
  exact hno (hiff.mp hLHS)

end AssemblyP1.CoveredBinomialWeightsIffSharpness
