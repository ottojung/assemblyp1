import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Exact finite-sample iid ML/MAP envelope (Antonina #269/#271)

For a fixed finite read-type universe E, baseline counts a : E → ℕ (positive on the
true support), arbitrary surplus y : E → ℕ totaling m, true probabilities p_i > 0,
competing probabilities q_i ≥ 0, and positive prior weights πP, πQ, the
likelihood/prior ratio of competitor vs truth at any sample x = a + y with
∑ y = m is bounded by

    (πQ/πP) · (∏ r_i^{a_i}) · rmax^m

where r_i = q_i/p_i are nonnegative ratios and rmax = max_i r_i.  Equality is
attained by concentrating all surplus at the maximizer j.  Support holes
(q_j = 0 with a_j > 0) force the ratio to zero.

Hence truth is the maximizer for ALL fully covered samples of exactly n = G + m
iff this scalar envelope is ≤ 1 (or a support hole exists).

Scope notes:
- "Fully covered" means a i > 0 for all i ∈ E (E is exactly the true read support).
- Candidate q may assign probability outside E; this theorem is abstract over the
  restricted coordinates E. Normalization of q over E is NOT assumed here.
- The hnoHole premise is unnecessary: if q_j = 0 and a_j > 0, the baseline product
  ∏ r_i^{a_i} is already zero, giving scalar bound 0 (even with m = 0).

This is EXACT IID multinomial with fixed sample size.  It is NOT the MB09
fixed-N product-binomial model, nor the general bidirected-flow structural
classification.
-/

namespace AssemblyP1.FiniteSampleIidEnvelope

open Finset BigOperators

variable {E : Type*} [Fintype E]

/-- Core abstract bound: for nonnegative ratios r, baseline a, surplus y with
sum m, the product ∏ r_i^{a_i+y_i} is bounded by (∏ r_i^{a_i}) · r_j^m where
r_j = rmax. -/
theorem prod_pow_le_prod_pow_mul_rmax_pow
    (r : E → ℝ) (a y : E → ℕ)
    (hr : ∀ i, 0 ≤ r i)
    (j : E) (hrmax : ∀ i, r i ≤ r j)
    (m : ℕ) (hy : ∑ i ∈ Finset.univ, y i = m) :
    (∏ i : E, (r i) ^ (a i + y i)) ≤ (∏ i : E, (r i) ^ (a i)) * (r j) ^ m := by
  simp_rw [pow_add, Finset.prod_mul_distrib]
  have h2 : ∀ i ∈ Finset.univ, (r i) ^ (y i) ≤ (r j) ^ (y i) := by
    intro i _
    exact pow_le_pow_left₀ (hr i) (hrmax i) (y i)
  have h3 : (∏ i : E, (r i) ^ (y i)) ≤ (∏ i : E, (r j) ^ (y i)) :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hr i) (y i)) h2
  have h4 : (∏ i : E, (r j) ^ (y i)) = (r j) ^ (∑ i ∈ Finset.univ, y i) := by
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [h4] at h3
  rw [hy] at h3
  exact mul_le_mul_of_nonneg_left h3 (Finset.prod_nonneg (fun i _ => pow_nonneg (hr i) _))

/-- Equality witness: concentrating all surplus at the maximizer j attains the
bound with equality. -/
theorem prod_pow_eq_prod_pow_mul_rmax_pow_concentrated [DecidableEq E]
    (r : E → ℝ) (a : E → ℕ)
    (j : E) (m : ℕ)
    (_hr : ∀ i, 0 ≤ r i) :
    (∏ i : E, (r i) ^ (a i + (if i = j then m else 0)))
      = (∏ i : E, (r i) ^ (a i)) * (r j) ^ m := by
  simp_rw [pow_add, Finset.prod_mul_distrib]
  have key : (∏ i : E, (r i) ^ (if i = j then m else 0)) = (r j) ^ m := by
    classical
    simp
  rw [key]

/-- Likelihood/prior ratio at sample x = a + y decomposed as
(πQ/πP) · ∏ (q_i/p_i)^{x_i}. -/
theorem likelihood_prior_ratio_eq
    (p q : E → ℝ) (piP piQ : ℝ) (x : E → ℕ)
    (hp : ∀ i, 0 < p i) :
    ((∏ i : E, (q i) ^ (x i)) / (∏ i : E, (p i) ^ (x i))) * (piQ / piP)
      = (piQ / piP) * (∏ i : E, (q i / p i) ^ (x i)) := by
  have hne : (∏ i : E, (p i) ^ (x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ne_of_gt (pow_pos (hp i) (x i))
  have hkey : ∏ i : E, (q i / p i) ^ (x i) = (∏ i : E, (q i) ^ (x i)) / (∏ i : E, (p i) ^ (x i)) := by
    simp only [div_pow, Finset.prod_div_distrib]
  rw [hkey]
  ring

/-- Support hole: q_j = 0 with a_j > 0 forces the likelihood ratio to zero. -/
theorem likelihood_prior_ratio_eq_zero_of_support_hole
    (p q : E → ℝ) (piP piQ : ℝ) (a y : E → ℕ)
    (hp : ∀ i, 0 < p i)
    (_hq : ∀ i, 0 ≤ q i)
    (j : E) (ha : 0 < a j) (hqj : q j = 0) :
    ((∏ i : E, (q i) ^ (a i + y i)) / (∏ i : E, (p i) ^ (a i + y i))) * (piQ / piP)
      = 0 := by
  have hxj : 0 < (a j + y j) := by simp [ha]
  have hqj0 : (q j) ^ (a j + y j) = 0 := by rw [hqj]; exact zero_pow (ne_of_gt hxj : (a j + y j : ℕ) ≠ 0)
  have hne : (∏ i : E, (p i) ^ (a i + y i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ne_of_gt (pow_pos (hp i) (a i + y i))
  rw [likelihood_prior_ratio_eq p q piP piQ (fun i => a i + y i) hp]
  have hr0 : (q j / p j) ^ (a j + y j) = 0 := by
    rw [hqj, zero_div]
    exact zero_pow (ne_of_gt hxj : (a j + y j : ℕ) ≠ 0)
  have hprod : (∏ i : E, (q i / p i) ^ (a i + y i)) = 0 := by
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨j, Finset.mem_univ j, hr0⟩
  rw [hprod]
  ring

/-- Main envelope theorem: for every surplus y with sum m, the likelihood/prior
ratio is bounded by the scalar envelope. -/
theorem likelihood_prior_ratio_le_envelope
    (p q : E → ℝ) (piP piQ : ℝ) (a y : E → ℕ)
    (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 ≤ q i)
    (hpiP : 0 < piP) (hpiQ : 0 < piQ)
    (j : E)
    (hrmax : ∀ i, q i / p i ≤ q j / p j)
    (m : ℕ) (hy : ∑ i ∈ Finset.univ, y i = m) :
    ((∏ i : E, (q i) ^ (a i + y i)) / (∏ i : E, (p i) ^ (a i + y i))) * (piQ / piP)
      ≤ (piQ / piP) * (∏ i : E, (q i / p i) ^ (a i)) * (q j / p j) ^ m := by
  rw [likelihood_prior_ratio_eq p q piP piQ (fun i => a i + y i) hp]
  have hr_nonneg : ∀ i : E, 0 ≤ q i / p i := by
    intro i
    exact div_nonneg (hq i) (le_of_lt (hp i))
  have hbound := prod_pow_le_prod_pow_mul_rmax_pow (fun i => q i / p i) a y hr_nonneg j hrmax m hy
  exact (mul_le_mul_of_nonneg_left hbound (div_nonneg (le_of_lt hpiQ) (le_of_lt hpiP))).trans
    (by ring_nf; exact le_of_eq (by ring))

/-- For every count vector x = a + y with sum y = m, truth is a MAP maximizer iff the scalar envelope is ≤ 1. If every a_i > 0 on the true read support, these vectors are the type-count vectors compatible with latent full start coverage; observed type counts alone do not certify actual latent start coverage. -/
theorem truth_maximizer_iff_envelope_le_one [DecidableEq E]
    (p q : E → ℝ) (piP piQ : ℝ) (a : E → ℕ)
    (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 ≤ q i)
    (hpiP : 0 < piP) (hpiQ : 0 < piQ)
    (j : E)
    (hrmax : ∀ i, q i / p i ≤ q j / p j)
    (m : ℕ) :
    (∀ y : E → ℕ, ∑ i ∈ Finset.univ, y i = m →
      ((∏ i : E, (q i) ^ (a i + y i)) / (∏ i : E, (p i) ^ (a i + y i))) * (piQ / piP) ≤ 1)
      ↔ (piQ / piP) * (∏ i : E, (q i / p i) ^ (a i)) * (q j / p j) ^ m ≤ 1 := by
  constructor
  · intro hy
    have hy' := hy (fun i => if i = j then m else 0) (by
      rw [Finset.sum_ite_eq' Finset.univ j (fun _ => m)]
      simp)
    rw [likelihood_prior_ratio_eq p q piP piQ (fun i => a i + (if i = j then m else 0)) hp] at hy'
    have hr_nonneg : ∀ i : E, 0 ≤ q i / p i := by
      intro i
      exact div_nonneg (hq i) (le_of_lt (hp i))
    have hconc := prod_pow_eq_prod_pow_mul_rmax_pow_concentrated (fun i => q i / p i) a j m hr_nonneg
    rw [hconc] at hy'
    simpa only [mul_assoc] using hy'
  · intro henvelope y hy
    have hle := likelihood_prior_ratio_le_envelope p q piP piQ a y hp hq hpiP hpiQ j hrmax m hy
    exact le_trans hle henvelope

/-- A count vector `x` is compatible with **full true-start coverage** on the
true oriented read support `E`: every true read type is observed at least as
often as its start multiplicity `A i`.  This is the type-count shadow of
sampling every true genome start at least once. -/
def FullStartCovered (A x : E → ℕ) : Prop := ∀ i, A i ≤ x i

/-- **Exact iid full-start-covered pointwise classification.**

Let `E` be the true oriented read-type support, `A i > 0` the truth's start
spectrum, `p i > 0` the truth's exact iid read-type probabilities, and `q i ≥ 0`
a candidate's read-type probabilities.  Then the candidate's exact iid
likelihood is never strictly larger than the truth's on *any* full-start-covered
observed count vector `x ≥ A` if and only if either the candidate assigns zero
probability to some true read type, or it is coordinatewise dominated by the
truth on the true support.

This is the `m`-free generalization of `truth_maximizer_iff_envelope_le_one`:
the latter fixes the total surplus `m`, while this quantifies over every
admissible full-start-covered sample.  Sufficiency is the product inequality on
the observed types (with the zero-support case immediate); necessity samples the
baseline once and then concentrates `k` surplus copies at a type where
`q j > p j`, whose likelihood ratio `C · (q j / p j)^k` grows without bound.

This is EXACT IID multinomial likelihood; it is NOT the MB09 fixed-`N`
product-binomial model, nor the general bidirected-flow structural
classification. -/
theorem truth_maximizer_forall_covered_iff [DecidableEq E]
    (p q : E → ℝ) (A : E → ℕ)
    (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 ≤ q i)
    (hA : ∀ i, 0 < A i) :
    (∀ x : E → ℕ, FullStartCovered A x →
      (∏ i : E, (q i) ^ (x i)) ≤ (∏ i : E, (p i) ^ (x i)))
      ↔ (∃ j, q j = 0) ∨ (∀ i, q i ≤ p i) := by
  constructor
  · intro h
    by_cases hhole : ∃ j, q j = 0
    · exact Or.inl hhole
    · right
      push Not at hhole
      by_contra hnotle
      push Not at hnotle
      obtain ⟨j, hpj⟩ := hnotle
      have hqpos : ∀ i, 0 < q i := fun i => lt_of_le_of_ne (hq i) (Ne.symm (hhole i))
      have hrj : 1 < q j / p j := (one_lt_div (hp j)).mpr hpj
      have hPqpos : 0 < ∏ i : E, (q i) ^ (A i) :=
        Finset.prod_pos (fun i _ => pow_pos (hqpos i) (A i))
      have hPppos : 0 < ∏ i : E, (p i) ^ (A i) :=
        Finset.prod_pos (fun i _ => pow_pos (hp i) (A i))
      have hCpos : 0 < (∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i)) :=
        div_pos hPqpos hPppos
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
        (1 / ((∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i)))) hrj
      have hgt1 : 1 < ((∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i))) *
          (q j / p j) ^ k := by
        have hc : ((∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i))) *
            (1 / ((∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i)))) = 1 := by
          field_simp
        have hstep := mul_lt_mul_of_pos_left hk hCpos
        rwa [hc] at hstep
      let x : E → ℕ := fun i => A i + if i = j then k else 0
      have hcov : FullStartCovered A x := fun i => by
        dsimp only [FullStartCovered, x]; omega
      have hx := h x hcov
      have hqx : (∏ i : E, (q i) ^ (x i)) =
          (∏ i : E, (q i) ^ (A i)) * (q j) ^ k := by
        dsimp only [x]
        exact prod_pow_eq_prod_pow_mul_rmax_pow_concentrated q A j k hq
      have hpx : (∏ i : E, (p i) ^ (x i)) =
          (∏ i : E, (p i) ^ (A i)) * (p j) ^ k := by
        dsimp only [x]
        exact prod_pow_eq_prod_pow_mul_rmax_pow_concentrated p A j k
          (fun i => le_of_lt (hp i))
      have hden : 0 < (∏ i : E, (p i) ^ (x i)) :=
        Finset.prod_pos (fun i _ => pow_pos (hp i) (x i))
      have hratio : (∏ i : E, (q i) ^ (x i)) / (∏ i : E, (p i) ^ (x i)) =
          ((∏ i : E, (q i) ^ (A i)) / (∏ i : E, (p i) ^ (A i))) *
            (q j / p j) ^ k := by
        rw [hqx, hpx, div_pow, div_mul_div_comm]
      have hle1 : (∏ i : E, (q i) ^ (x i)) / (∏ i : E, (p i) ^ (x i)) ≤ 1 := by
        rw [div_le_one hden]; exact hx
      rw [hratio] at hle1
      exact absurd hgt1 (not_lt_of_ge hle1)
  · rintro (⟨j, hqj⟩ | hle) x hx
    · have hxj : 0 < x j := lt_of_lt_of_le (hA j) (hx j)
      have hzj : (q j) ^ (x j) = 0 := by
        rw [hqj]; exact zero_pow (ne_of_gt hxj)
      have hprod0 : (∏ i : E, (q i) ^ (x i)) = 0 :=
        Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_univ j, hzj⟩
      rw [hprod0]
      exact Finset.prod_nonneg (fun i _ => pow_nonneg (le_of_lt (hp i)) (x i))
    · exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hq i) (x i))
        (fun i _ => pow_le_pow_left₀ (hq i) (hle i) (x i))

#print axioms prod_pow_le_prod_pow_mul_rmax_pow
#print axioms likelihood_prior_ratio_le_envelope
#print axioms truth_maximizer_iff_envelope_le_one
#print axioms truth_maximizer_forall_covered_iff

end AssemblyP1.FiniteSampleIidEnvelope
