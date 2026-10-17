import AssemblyP1.CoveredBinomialWeightsIff
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Rigidity is necessary for sample-uniform maximality of the MB09 §6.1
product-binomial surrogate (board issue #259, necessity direction)

Medvedev–Brudno 2009 §6.1 score the read-count objective by a **product of
marginal binomials** with a fixed external genome length `N`.  For a candidate
spectrum `B : E → ℕ` over a fixed finite read-type universe `E`, the
candidate-dependent integer numerator is

```
effectiveProduct N B x = ∏_e (effectiveWeight N B e) ^ (x e),
effectiveWeight N B e = B e * ∏_{j ≠ e} (N - B j).
```

This is *not* the exact joint multinomial read likelihood (`#256`) and *not* the
§6.2 bidirected-flow objective (`#260`/`#261`); the extra
`(N - B j) ^ (n - x j)` factors of the unobserved coordinates are exactly what
separates it.

## What is proved here

The earlier `#259` increment (`AssemblyP1/CoveredBinomialWeightsIff`) classified
the **covered-sample** dominance of a fixed truth `A` over a fixed competitor
`B`:

> `A` dominates `B` on every sample with `A e ≤ x e` **iff** `B` has a zero
> effective weight on `supp A`, or `B`'s effective weights are pointwise
> dominated by `A`'s on `supp A`.

That classification is per-competitor.  The **sample-uniform maximality** of
`A` — `A` scores at least as high as *every* admissible competitor on *every*
covered sample — is therefore equivalent to: for every competitor `B`, either
`B` is zero on a true-supported class, or `B` is pointwise dominated.

The missing ingredient for the **rigidity** question is the following arithmetic
fact (this file's main new theorem):

> **`effectiveWeight_le_imp_eq`.** If `A` and `B` are *positive* count vectors
> of the same total `N` and `effectiveWeight N B e ≤ effectiveWeight N A e` for
> every `e`, then `A = B`.

Equivalently (`exists_effectiveWeight_gt_of_ne`): two distinct positive
count vectors of equal total can never be pointwise dominated in effective
weight — the larger-weight coordinate always exists.  The proof is an
information-theoretic one: the weighted geometric mean identity

```
∑_e B_e log (effectiveWeight N B e / effectiveWeight N A e)
  = ∑_e B_e log (B_e / A_e) + ∑_e (N - B_e) log ((N - B_e)/(N - A_e))
```

shows the left side is a sum of two nonnegative Kullback–Leibler-type terms
(`x - 1 ≤ x log x`), while the hypothesis `effectiveWeight N B ≤ effectiveWeight
N A` makes it nonpositive.  Hence it is zero, and the equality case of
`x - 1 ≤ x log x` forces `B = A`.

## The classification (necessity)

Combining this with the covered-sample iff gives the **exact** sample-uniform
maximality criterion over any candidate class `F` of positive count vectors of
total `N` that contains `A`:

> **`robust_iff_unique`.** `A` is a sample-uniform maximizer over `F` on all
> covered samples **iff** `F = {A}`.

`F = {A}` is exactly **rigidity** of `A` when `F` is the set of positive
balanced circulations of total `N` on `supp A`: the truth spectrum is the only
same-support candidate.  Consequently rigidity is **necessary** for
sample-uniform maximality.  It is *not sufficient* once candidates with **new
support** (classes outside `supp A`) are admitted: `newsupport_rigid_not_maximal`
exhibits a rigid truth `A = (2,1,1,0)` (the length-4 spectrum of `0001`) that is
beaten by the new-support candidate `B = (1,1,1,1)` (the spectrum of `0011`).
So the §6.1 product-binomial `robust ⟺ unique` is a *one-way* strengthening of
the exact-multinomial `#256` result: necessity survives the extra unobserved
factors, sufficiency does not.

## Scope

* Objective: MB09 §6.1 fixed-external-`N` product-binomial **surrogate**.
* Candidate length: same-length, fixed finite universe `E = supp A`.
* Normalization `N`: fixed external; omitted candidate-constant factors cancel.
* Support: same-support candidates for `robust_iff_unique`; the new-support
  sufficiency failure is a separate scoped witness.
* Sample size `n = ∑ x`: free, bounded below by the truth spectrum.
* Still open: variable genome length, §6.2 bidirected flows, and a rigidity
  *sufficiency* theorem over the full new-support candidate class.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace AssemblyP1.ProductBinomialRigidityNecessity

open AssemblyP1.FixedNBinomialEffectiveWeights

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## Elementary facts about positive vectors of total `N` -/

/-- A positive count vector of total `N` over at least two classes has every
coordinate strictly below `N`.  This is what makes `N - ·` positive (and the
logarithms below well defined). -/
theorem lt_of_card (hcard : 2 ≤ Fintype.card E) {N : ℕ} {A : E → ℕ}
    (hA : ∀ e, 0 < A e) (hAtot : ∑ e, A e = N) (e : E) : A e < N := by
  have hge : 1 ≤ ∑ g ∈ Finset.univ.erase e, A g := by
    have hc : 1 ≤ (Finset.univ.erase e).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ]
      omega
    calc (1 : ℕ) ≤ (Finset.univ.erase e).card := hc
      _ = ∑ _g ∈ Finset.univ.erase e, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ g ∈ Finset.univ.erase e, A g := Finset.sum_le_sum (fun g _ => hA g)
  have hsum : ∑ g ∈ Finset.univ.erase e, A g = N - A e := by
    have := Finset.sum_erase_add Finset.univ A (Finset.mem_univ e)
    omega
  omega

/-- `effectiveWeight` written with an explicit `erase`, isolating the factor
`N - v j` of every *other* class. -/
theorem effectiveWeight_eq_erase (N : ℕ) (v : E → ℕ) (e : E) :
    effectiveWeight N v e = v e * ∏ j ∈ Finset.univ.erase e, (N - v j) := by
  unfold effectiveWeight
  congr 1
  rw [← Finset.prod_erase (s := Finset.univ)
        (f := fun j => if e = j then (1 : ℕ) else (N - v j)) (a := e) (by simp)]
  exact Finset.prod_congr rfl (fun j hj =>
    ite_eq_right (Ne.symm (Finset.mem_erase.mp hj).1))

/-- The effective weight of a positive vector is positive, provided the other
classes keep `N - v j > 0`. -/
theorem effectiveWeight_pos {N : ℕ} {v : E → ℕ} (hv : ∀ e, 0 < v e)
    (hvN : ∀ e, v e < N) (e : E) : 0 < effectiveWeight N v e := by
  rw [effectiveWeight_eq_erase]
  have hprod : 1 ≤ ∏ j ∈ Finset.univ.erase e, (N - v j) :=
    Finset.one_le_prod (fun j _ => by have := hvN j; omega)
  nlinarith [hv e]

/-! ## Two elementary real inequalities -/

/-- `b - a ≤ b * log (b / a)` for `a > 0`, `b ≥ 0`.  This is the scaled form of
`x - 1 ≤ x log x`, the Gibbs/KL nonnegativity engine. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    b - a ≤ b * Real.log (b / a) := by
  have hx : 0 ≤ b / a := div_nonneg hb (le_of_lt ha)
  have h := Real.self_sub_one_le_mul_log hx
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt ha)
  have h1 : a * (b / a) = b := by field_simp
  have h2 : a * (b / a - 1) = b - a := by rw [mul_sub, mul_one, h1]
  have h3 : a * (b / a * Real.log (b / a)) = b * Real.log (b / a) := by
    rw [← mul_assoc, h1]
  rwa [h2, h3] at hmul

/-- The equality case of `sub_le_mul_log_div`: `b * log (b/a) = b - a` forces
`b = a` (for `a > 0`, `b ≥ 0`). -/
theorem eq_of_sub_eq_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (h : b * Real.log (b / a) = b - a) : b = a := by
  by_contra hne
  have hbpos : 0 < b := by
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0] at h; simp only [zero_mul] at h; linarith
    · exact hbpos
  have hxpos : 0 < b / a := div_pos hbpos ha
  have hxne : b / a ≠ 1 := by
    intro h1
    rw [div_eq_iff (ne_of_gt ha), one_mul] at h1
    exact hne h1
  have hstrict := Real.self_sub_one_lt_mul_log (le_of_lt hxpos) hxne
  have h2 : (b / a) * Real.log (b / a) = b / a - 1 := by
    rw [div_mul_eq_mul_div, h, sub_div, div_self (ne_of_gt ha)]
  linarith

/-! ## The weighted-geometric-mean identity -/

/-- **Effective-weight logarithm identity.**  For a positive vector `v` with
`v j < N` and any weight vector `w` of total `N`,

```
∑_e w_e log (effectiveWeight N v e)
  = ∑_e w_e log v_e + ∑_e (N - w_e) log (N - v_e).
```

This is the algebra behind the KL-type lower bound: the cross terms of
`∏_{j ≠ e} (N - v j)` reindex by the total-sum constraint `∑ w = N`. -/
theorem sum_mul_log_effectiveWeight (N : ℕ) (v w : E → ℕ)
    (hv : ∀ e, 0 < v e) (hvN : ∀ e, v e < N) (hw : ∑ e, w e = N) :
    (∑ e, (w e : ℝ) * Real.log ((effectiveWeight N v e : ℝ)))
      = (∑ e, (w e : ℝ) * Real.log ((v e : ℝ)))
        + (∑ e, ((N : ℝ) - (w e : ℝ))
            * Real.log (((N : ℝ) - (v e : ℝ)))) := by
  have hcast : ((N : ℝ)) = ∑ e, (w e : ℝ) := by
    rw [← Nat.cast_sum, hw]
  have hsep : ∀ e, ((N : ℝ) - (v e : ℝ)) ≠ 0 := by
    intro e
    have : (v e : ℝ) < (N : ℝ) := by exact_mod_cast hvN e
    linarith
  have hlogprod : ∀ e, Real.log ((effectiveWeight N v e : ℝ))
      = Real.log ((v e : ℝ))
        + ∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ))) := by
    intro e
    have hprodne : (∏ j ∈ Finset.univ.erase e, ((N : ℝ) - (v j : ℝ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hsep j)
    have hcastprod : ((∏ j ∈ Finset.univ.erase e, (N - v j) : ℕ) : ℝ)
        = ∏ j ∈ Finset.univ.erase e, ((N : ℝ) - (v j : ℝ)) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun j _ =>
        by rw [Nat.cast_sub (le_of_lt (hvN j))])
    rw [effectiveWeight_eq_erase, Nat.cast_mul, hcastprod,
      Real.log_mul (by exact_mod_cast (ne_of_gt (hv e))) hprodne, Real.log_prod]
    intro j _
    exact hsep j
  have hkey : (∑ e, (w e : ℝ)
        * (∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ)))))
      = ∑ e, ((N : ℝ) - (w e : ℝ))
          * Real.log (((N : ℝ) - (v e : ℝ))) := by
    have h1 : ∀ e, (∑ j ∈ Finset.univ.erase e,
          Real.log (((N : ℝ) - (v j : ℝ))))
        = (∑ j, Real.log (((N : ℝ) - (v j : ℝ))))
          - Real.log (((N : ℝ) - (v e : ℝ))) := by
      intro e
      have := Finset.sum_erase_add Finset.univ
        (fun j => Real.log (((N : ℝ) - (v j : ℝ)))) (Finset.mem_univ e)
      linarith
    calc (∑ e, (w e : ℝ)
          * (∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ)))))
        = ∑ e, (w e : ℝ) * ((∑ j, Real.log (((N : ℝ) - (v j : ℝ))))
            - Real.log (((N : ℝ) - (v e : ℝ)))) :=
          Finset.sum_congr rfl (fun e _ => by rw [h1 e])
      _ = ∑ e, ((w e : ℝ) * (∑ j, Real.log (((N : ℝ) - (v j : ℝ))))
            - (w e : ℝ) * Real.log (((N : ℝ) - (v e : ℝ)))) :=
          Finset.sum_congr rfl (fun e _ => by rw [mul_sub])
      _ = (∑ e, (w e : ℝ) * (∑ j, Real.log (((N : ℝ) - (v j : ℝ)))))
            - ∑ e, (w e : ℝ) * Real.log (((N : ℝ) - (v e : ℝ))) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ e, (w e : ℝ)) * (∑ j, Real.log (((N : ℝ) - (v j : ℝ))))
            - ∑ e, (w e : ℝ) * Real.log (((N : ℝ) - (v e : ℝ))) := by
          rw [Finset.sum_mul]
      _ = (N : ℝ) * (∑ j, Real.log (((N : ℝ) - (v j : ℝ))))
            - ∑ e, (w e : ℝ) * Real.log (((N : ℝ) - (v e : ℝ))) := by
          rw [hcast]
      _ = ∑ e, ((N : ℝ) - (w e : ℝ))
            * Real.log (((N : ℝ) - (v e : ℝ))) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun e _ => by ring)
  calc (∑ e, (w e : ℝ) * Real.log ((effectiveWeight N v e : ℝ)))
      = ∑ e, (w e : ℝ) * (Real.log ((v e : ℝ))
          + ∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ)))) :=
        Finset.sum_congr rfl (fun e _ => by rw [hlogprod e])
    _ = ∑ e, ((w e : ℝ) * Real.log ((v e : ℝ))
          + (w e : ℝ)
              * (∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ))))) :=
        Finset.sum_congr rfl (fun e _ => by rw [mul_add])
    _ = (∑ e, (w e : ℝ) * Real.log ((v e : ℝ)))
          + ∑ e, (w e : ℝ)
              * (∑ j ∈ Finset.univ.erase e, Real.log (((N : ℝ) - (v j : ℝ)))) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ e, (w e : ℝ) * Real.log ((v e : ℝ)))
          + ∑ e, ((N : ℝ) - (w e : ℝ))
              * Real.log (((N : ℝ) - (v e : ℝ))) := by rw [hkey]

/-- Weighted splitting of a log of a ratio into a difference of weighted log
sums. -/
theorem sum_mul_log_div_split (w f g : E → ℝ)
    (hf : ∀ e, f e ≠ 0) (hg : ∀ e, g e ≠ 0) :
    (∑ e, w e * Real.log (f e / g e))
      = (∑ e, w e * Real.log (f e)) - (∑ e, w e * Real.log (g e)) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun e _ => by rw [Real.log_div (hf e) (hg e)]; ring)

/-- **The log-ratio identity.**  The weighted log-ratio of the effective
products splits into the sum of the two KL-type divergences
`∑ B_e log(B_e/A_e) + ∑ (N-B_e) log((N-B_e)/(N-A_e))`. -/
theorem sum_log_ratio_identity (N : ℕ) (A B : E → ℕ)
    (hA : ∀ e, 0 < A e) (hB : ∀ e, 0 < B e)
    (hAN : ∀ e, A e < N) (hBN : ∀ e, B e < N)
    (hBtot : ∑ e, B e = N) :
    (∑ e, (B e : ℝ)
        * Real.log ((effectiveWeight N B e : ℝ) / (effectiveWeight N A e : ℝ)))
      = (∑ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ)))
        + (∑ e, ((N : ℝ) - (B e : ℝ))
            * Real.log (((N : ℝ) - (B e : ℝ)) / ((N : ℝ) - (A e : ℝ)))) := by
  have hBeff : ∀ e, 0 < effectiveWeight N B e := effectiveWeight_pos hB hBN
  have hAeff : ∀ e, 0 < effectiveWeight N A e := effectiveWeight_pos hA hAN
  have hNB : ∀ e, ((N : ℝ) - (B e : ℝ)) ≠ 0 := by
    intro e
    have h : (B e : ℝ) < (N : ℝ) := by exact_mod_cast hBN e
    linarith
  have hNA : ∀ e, ((N : ℝ) - (A e : ℝ)) ≠ 0 := by
    intro e
    have h : (A e : ℝ) < (N : ℝ) := by exact_mod_cast hAN e
    linarith
  have hdiv := sum_mul_log_div_split (fun e => (B e : ℝ))
    (fun e => (effectiveWeight N B e : ℝ)) (fun e => (effectiveWeight N A e : ℝ))
    (fun e => by exact_mod_cast (ne_of_gt (hBeff e)))
    (fun e => by exact_mod_cast (ne_of_gt (hAeff e)))
  have hB' := sum_mul_log_effectiveWeight N B B hB hBN hBtot
  have hA' := sum_mul_log_effectiveWeight N A B hA hAN hBtot
  have hKL1div := sum_mul_log_div_split (fun e => (B e : ℝ))
    (fun e => (B e : ℝ)) (fun e => (A e : ℝ))
    (fun e => by exact_mod_cast (ne_of_gt (hB e)))
    (fun e => by exact_mod_cast (ne_of_gt (hA e)))
  have hKL2div := sum_mul_log_div_split (fun e => ((N : ℝ) - (B e : ℝ)))
    (fun e => ((N : ℝ) - (B e : ℝ))) (fun e => ((N : ℝ) - (A e : ℝ))) hNB hNA
  rw [hdiv, hB', hA', hKL1div, hKL2div]
  ring

/-! ## The necessity lemma -/

/-- **Effective-weight domination is only possible by equality.**  If two
positive count vectors of the same total `N` satisfy `effectiveWeight N B e ≤
effectiveWeight N A e` for every class `e`, then `A = B`. -/
theorem effectiveWeight_le_imp_eq (hcard : 2 ≤ Fintype.card E) (N : ℕ)
    (A B : E → ℕ) (hA : ∀ e, 0 < A e) (hB : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = N) (hBtot : ∑ e, B e = N)
    (hle : ∀ e, effectiveWeight N B e ≤ effectiveWeight N A e) : A = B := by
  have hAN : ∀ e, A e < N := fun e => lt_of_card hcard hA hAtot e
  have hBN : ∀ e, B e < N := fun e => lt_of_card hcard hB hBtot e
  have hAeff : ∀ e, 0 < effectiveWeight N A e := effectiveWeight_pos hA hAN
  have hBeff : ∀ e, 0 < effectiveWeight N B e := effectiveWeight_pos hB hBN
  have hident := sum_log_ratio_identity N A B hA hB hAN hBN hBtot
  -- Nonpositive by the hypothesis.
  have hDle : (∑ e, (B e : ℝ)
        * Real.log ((effectiveWeight N B e : ℝ) / (effectiveWeight N A e : ℝ)))
      ≤ 0 := by
    apply Finset.sum_nonpos
    intro e _
    have hAe : (0 : ℝ) < (effectiveWeight N A e : ℝ) := by exact_mod_cast hAeff e
    have hBe : (0 : ℝ) < (effectiveWeight N B e : ℝ) := by exact_mod_cast hBeff e
    have hratio : (effectiveWeight N B e : ℝ) / (effectiveWeight N A e : ℝ) ≤ 1 := by
      rw [div_le_one hAe]
      exact_mod_cast hle e
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Real.log_nonpos (le_of_lt (div_pos hBe hAe)) hratio)
  -- Nonnegative: each KL-type sum is nonnegative.
  have hKL1nn : 0 ≤ ∑ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ)) := by
    have h0 : (0 : ℝ) ≤ ∑ e, ((B e : ℝ) - (A e : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      have : (∑ e, (B e : ℝ)) = (∑ e, (A e : ℝ)) := by
        rw [← Nat.cast_sum, ← Nat.cast_sum, hBtot, hAtot]
      linarith
    calc (0 : ℝ) ≤ ∑ e, ((B e : ℝ) - (A e : ℝ)) := h0
      _ ≤ ∑ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ)) :=
        Finset.sum_le_sum (fun e _ =>
          sub_le_mul_log_div (a := (A e : ℝ)) (b := (B e : ℝ))
            (by exact_mod_cast hA e) (by positivity))
  have hKL2nn : 0 ≤ ∑ e, ((N : ℝ) - (B e : ℝ))
        * Real.log (((N : ℝ) - (B e : ℝ)) / ((N : ℝ) - (A e : ℝ))) := by
    have hNApos : ∀ e, (0 : ℝ) < (N : ℝ) - (A e : ℝ) := by
      intro e
      have h : (A e : ℝ) < (N : ℝ) := by exact_mod_cast hAN e
      linarith
    have hNBpos : ∀ e, (0 : ℝ) < (N : ℝ) - (B e : ℝ) := by
      intro e
      have h : (B e : ℝ) < (N : ℝ) := by exact_mod_cast hBN e
      linarith
    have hBNsum : (∑ e, (B e : ℝ)) = (∑ e, (A e : ℝ)) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum, hBtot, hAtot]
    have h0 : (0 : ℝ) ≤
        ∑ e, (((N : ℝ) - (B e : ℝ)) - ((N : ℝ) - (A e : ℝ))) := by
      rw [Finset.sum_sub_distrib]
      have hEq : (∑ e, ((N : ℝ) - (B e : ℝ)))
          = (∑ e, ((N : ℝ) - (A e : ℝ))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hBNsum]
      linarith
    calc (0 : ℝ) ≤ ∑ e, (((N : ℝ) - (B e : ℝ)) - ((N : ℝ) - (A e : ℝ))) := h0
      _ ≤ ∑ e, ((N : ℝ) - (B e : ℝ))
            * Real.log (((N : ℝ) - (B e : ℝ)) / ((N : ℝ) - (A e : ℝ))) :=
        Finset.sum_le_sum (fun e _ =>
          sub_le_mul_log_div (a := (N : ℝ) - (A e : ℝ)) (b := (N : ℝ) - (B e : ℝ))
            (hNApos e) (le_of_lt (hNBpos e)))
  have hDge : 0 ≤ ∑ e, (B e : ℝ)
        * Real.log ((effectiveWeight N B e : ℝ) / (effectiveWeight N A e : ℝ)) := by
    rw [hident]; exact add_nonneg hKL1nn hKL2nn
  have hDzero : (∑ e, (B e : ℝ)
        * Real.log ((effectiveWeight N B e : ℝ) / (effectiveWeight N A e : ℝ)))
      = 0 := le_antisymm hDle hDge
  have hKL1 : (∑ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ))) = 0 := by
    have hDsum : (∑ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ)))
        + (∑ e, ((N : ℝ) - (B e : ℝ))
            * Real.log (((N : ℝ) - (B e : ℝ)) / ((N : ℝ) - (A e : ℝ)))) = 0 := by
      rw [← hident, hDzero]
    linarith [hKL1nn, hKL2nn, hDsum]
  -- Termwise: `B_e log(B_e/A_e) = B_e - A_e`, whose equality case is `B_e = A_e`.
  have hterm : ∀ e, (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ))
      = (B e : ℝ) - (A e : ℝ) := by
    have hsum0 : (∑ e, ((B e : ℝ) - (A e : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib]
      have : (∑ e, (B e : ℝ)) = (∑ e, (A e : ℝ)) := by
        rw [← Nat.cast_sum, ← Nat.cast_sum, hBtot, hAtot]
      linarith
    have hgsum : (∑ e, ((B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ))
        - ((B e : ℝ) - (A e : ℝ)))) = 0 := by
      rw [Finset.sum_sub_distrib, hKL1, hsum0, sub_zero]
    have hgnn : ∀ e ∈ (Finset.univ : Finset E),
        0 ≤ (B e : ℝ) * Real.log ((B e : ℝ) / (A e : ℝ))
          - ((B e : ℝ) - (A e : ℝ)) := fun e _ => by
      have := sub_le_mul_log_div (a := (A e : ℝ)) (b := (B e : ℝ))
        (by exact_mod_cast hA e) (by positivity)
      linarith
    intro e
    have hsingle := (Finset.sum_eq_zero_iff_of_nonneg hgnn).mp hgsum e (Finset.mem_univ e)
    linarith
  funext e
  exact_mod_cast (eq_of_sub_eq_mul_log_div (by exact_mod_cast hA e) (by positivity)
    (hterm e)).symm

/-- **The positive form of the necessity lemma.**  Two distinct positive count
vectors of the same total `N` can never be pointwise dominated in effective
weight: there is always a class on which the competitor strictly exceeds the
truth. -/
theorem exists_effectiveWeight_gt_of_ne (hcard : 2 ≤ Fintype.card E) (N : ℕ)
    (A B : E → ℕ) (hA : ∀ e, 0 < A e) (hB : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = N) (hBtot : ∑ e, B e = N) (hne : A ≠ B) :
    ∃ e, effectiveWeight N A e < effectiveWeight N B e := by
  by_contra h
  push Not at h
  exact hne (effectiveWeight_le_imp_eq hcard N A B hA hB hAtot hBtot h)

/-! ## Sample-uniform maximality implies uniqueness (rigidity) -/

/-- **The necessity theorem, beating form.**  If `B` is a positive count vector
of total `N` distinct from the positive truth `A` (also of total `N`, over at
least two classes), then some **covered** sample strictly prefers `B` to `A`:
there is `x` with `A e ≤ x e` for every class and
`effectiveProduct N A x < effectiveProduct N B x`.

This is the §6.1 analogue of the exact-multinomial beating lemma of `#256`, and
it is the contrapositive engine of the rigidity necessity. -/
theorem exists_beating_sample (hcard : 2 ≤ Fintype.card E) (N : ℕ)
    (A B : E → ℕ) (hA : ∀ e, 0 < A e) (hB : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = N) (hBtot : ∑ e, B e = N) (hne : A ≠ B) :
    ∃ x : E → ℕ, (∀ e, A e ≤ x e) ∧
      effectiveProduct N A x < effectiveProduct N B x := by
  have hAN : ∀ e, A e < N := fun e => lt_of_card hcard hA hAtot e
  have hBN : ∀ e, B e < N := fun e => lt_of_card hcard hB hBtot e
  have hAeff : ∀ e, 0 < effectiveWeight N A e := effectiveWeight_pos hA hAN
  have hBeff : ∀ e, 0 < effectiveWeight N B e := effectiveWeight_pos hB hBN
  obtain ⟨e0, he0⟩ := exists_effectiveWeight_gt_of_ne hcard N A B hA hB hAtot hBtot hne
  have hnot : ¬ ((∃ e, effectiveWeight N B e = 0) ∨
      ∀ e, effectiveWeight N B e ≤ effectiveWeight N A e) := by
    rintro (h | h)
    · obtain ⟨e, he⟩ := h
      exact absurd he (ne_of_gt (hBeff e))
    · exact absurd (h e0) (not_le.mpr he0)
  have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_effectiveProduct_le_iff
    N A B hA hAeff
  have : ¬ (∀ x : E → ℕ, (∀ e, A e ≤ x e) →
      effectiveProduct N B x ≤ effectiveProduct N A x) := fun h => hnot (hiff.mp h)
  push Not at this
  exact this

/-- **The necessity classification.**  For any candidate class `F` of positive
count vectors of total `N` containing the positive truth `A` (over at least two
classes), the truth is a sample-uniform maximizer over `F` on every covered
sample **iff** `F = {A}`.

When `F` is the set of positive balanced circulations of total `N` on
`supp A`, `F = {A}` is exactly rigidity of `A`; the theorem therefore says that
sample-uniform maximality implies rigidity (necessity), and that a unique
same-support candidate is automatically maximal. -/
theorem robust_iff_unique (hcard : 2 ≤ Fintype.card E) (N : ℕ) (A : E → ℕ)
    (hA : ∀ e, 0 < A e) (hAtot : ∑ e, A e = N)
    (F : Set (E → ℕ))
    (hFpos : ∀ B ∈ F, ∀ e, 0 < B e)
    (hFtot : ∀ B ∈ F, ∑ e, B e = N)
    (hAF : A ∈ F) :
    (∀ x : E → ℕ, (∀ e, A e ≤ x e) →
        ∀ B ∈ F, effectiveProduct N B x ≤ effectiveProduct N A x) ↔
      F = {A} := by
  constructor
  · intro H
    ext B
    constructor
    · intro hB
      rw [Set.mem_singleton_iff]
      by_contra hne
      obtain ⟨x, hx, hlt⟩ :=
        exists_beating_sample hcard N A B hA (hFpos B hB) hAtot (hFtot B hB)
          (Ne.symm hne)
      exact absurd (H x hx B hB) (not_le.mpr hlt)
    · intro hB
      rw [Set.mem_singleton_iff] at hB
      rw [hB]
      exact hAF
  · intro hF x _ B hB
    rw [hF] at hB
    rw [Set.mem_singleton_iff] at hB
    rw [hB]

/-! ## Sufficiency fails: a rigid truth beaten by a new-support candidate -/

/-- The length-4 truth spectrum of the circular word `0001`: the oriented
2-mer counts `(00,01,10,11) = (2,1,1,0)`.  Its support is `{00,01,10}`. -/
def newsupportA : Fin 4 → ℕ := ![2, 1, 1, 0]

/-- The **new-support** candidate spectrum `(1,1,1,1)` of the circular word
`0011`; it uses the class `11`, which the truth `0001` never produces. -/
def newsupportB : Fin 4 → ℕ := ![1, 1, 1, 1]

theorem newsupportA_total : ∑ e, newsupportA e = 4 := by decide

theorem newsupportA_support_pos :
    ∀ i, 0 < newsupportA i → 0 < effectiveWeight 4 newsupportA i := by decide

/-- The ambient covered-sample criterion's failure branch holds for the
new-support candidate: no zero effective weight on the truth support, and the
pointwise domination fails (`effectiveWeight 4 B 1 = 27 > 24 =
effectiveWeight 4 A 1`). -/
theorem newsupportB_defeats :
    ¬ ((∃ i, 0 < newsupportA i ∧ effectiveWeight 4 newsupportB i = 0) ∨
      ∀ i, 0 < newsupportA i →
        effectiveWeight 4 newsupportB i ≤ effectiveWeight 4 newsupportA i) := by
  decide

/-- `newsupportA` is **rigid**: on its support `{00,01,10}` (with the class `11`
absent), the only positive balanced circulation of total `4` is `newsupportA`
itself.  The de Bruijn balance condition at the two 1-mer nodes reduces to
`C 1 = C 2` (`01 = 10`); with `C 3 = 0` (support) and total `4` the only
positive solution is `(2,1,1,0)`. -/
theorem newsupportA_rigid :
    ∀ C : Fin 4 → ℕ,
      (C 0 + C 1 + C 2 + C 3 = 4) →
      (0 < C 0) → (0 < C 1) → (0 < C 2) → (C 3 = 0) → (C 1 = C 2) →
      C = ![2, 1, 1, 0] := by
  intro C hsum h0 h1 h2 h3 h12
  funext i
  fin_cases i <;> simp_all <;> omega

/-- **Rigidity does not imply sample-uniform maximality.**  The rigid truth
`newsupportA = (2,1,1,0)` is strictly beaten by the new-support candidate
`newsupportB = (1,1,1,1)` on a covered sample.  Hence the §6.1 `robust ⟺
unique` of `robust_iff_unique` cannot be extended to a candidate class that
admits new-support spectra: rigidity is necessary but **not** sufficient. -/
theorem newsupport_rigid_not_maximal :
    (∀ C : Fin 4 → ℕ,
        (C 0 + C 1 + C 2 + C 3 = 4) →
        (0 < C 0) → (0 < C 1) → (0 < C 2) → (C 3 = 0) → (C 1 = C 2) →
        C = ![2, 1, 1, 0]) ∧
      (∃ x : Fin 4 → ℕ, (∀ e, newsupportA e ≤ x e) ∧
        (∀ j, newsupportA j = 0 → x j = 0) ∧
        effectiveProduct 4 newsupportA x < effectiveProduct 4 newsupportB x) := by
  refine ⟨newsupportA_rigid, ?_⟩
  have hnot := newsupportB_defeats
  have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff
    4 newsupportA newsupportB newsupportA_support_pos
  have : ¬ (∀ x : Fin 4 → ℕ, (∀ i, newsupportA i ≤ x i) →
      (∀ j, newsupportA j = 0 → x j = 0) →
      effectiveProduct 4 newsupportB x ≤ effectiveProduct 4 newsupportA x) :=
    fun h => hnot (hiff.mp h)
  push Not at this
  exact this

end AssemblyP1.ProductBinomialRigidityNecessity
