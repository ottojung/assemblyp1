import AssemblyP1.FiniteReadRecovery
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Generic Hellinger-affinity exponential decay for exact-ML error (issue #281)

`AssemblyP1.FiniteReadRecovery` kernel-checks the finite-read Hellinger
machinery: the pairwise bound `eventProb_pairwise`, the finite union bound
`eventProb_wrong_le_sum` (the concrete sum-of-powers form), and the
uniform-affinity bound `eventProb_wrong_le_card`, which gives

    eventProb p n (wrongEvent p Θ n) ≤ (Θ.card : ℝ) * ρ_max ^ n

under a uniform sub-unit affinity `ρ_max`. That is the *concrete
sum-of-powers* bound the issue permits as a first step. What was missing is
the **generic Hellinger-affinity contraction step** that converts `ρ_max ^ n`
into the explicit exponential form `exp(-c n)` with rate `c = -log ρ_max`, and
the corresponding finite-family exponential theorem.

This module supplies exactly that step, reusing the merged
`eventProb_wrong_le_card` endpoint rather than reproving it. The final
exponential decay result is kernel-checked here, not merely a related abstract
surrogate.

## Scope

* `Θ` is a finite family of read distributions (`IsPmf`). The identifiability
  corollary `eventProb_wrong_le_exp_neg_identifiable` assumes `p ≠ q` for
  every `q ∈ Θ`; the generic bound `eventProb_wrong_le_exp_neg` only needs a
  uniform sub-unit affinity bound `0 < ρ_max < 1`.
* The rate is `c = -log ρ_max`. When `ρ_max = 0` (disjoint supports) the error
  probability is `0` for every `n ≥ 1`; the corollary handles this degenerate
  case separately.
* No `axiom`, `sorry` or `admit`; the only kernel axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
-/

namespace AssemblyP1.HellingerExponentialDecay

open AssemblyP1.FiniteReadRecovery
open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- **Hellinger-affinity contraction step.** For a strictly positive,
strictly sub-unit affinity `ρ`, the `n`-fold power equals the exponential form
with rate `c = -log ρ`:

    ρ ^ n = exp (-(n : ℝ) * c).

This is the analytic bridge from the concrete sum-of-powers bound to the
explicit exponential form. -/
theorem hellinger_pow_eq_exp_neg {ρ : ℝ} (hρpos : 0 < ρ) (_hρlt : ρ < 1) (n : ℕ) :
    ρ ^ n = Real.exp (-(n : ℝ) * (- Real.log ρ)) := by
  have hexp : -(n : ℝ) * (- Real.log ρ) = (n : ℝ) * Real.log ρ := by ring
  rw [hexp, Real.exp_nat_mul, Real.exp_log hρpos]

/-- The contraction step in inequality form. -/
theorem hellinger_pow_le_exp_neg {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1) (n : ℕ) :
    ρ ^ n ≤ Real.exp (-(n : ℝ) * (- Real.log ρ)) :=
  (hellinger_pow_eq_exp_neg hρpos hρlt n).le

/-- **Generic finite-family exponential exact-ML error bound.** For a finite
family `Θ` of read distributions and a uniform sub-unit affinity bound
`ρ_max`, the exact probability that some competitor ties or beats the truth
after `n` iid reads is at most `|Θ| * exp(-c n)` with `c = -log ρ_max > 0`.

This reuses the merged `eventProb_wrong_le_card` and adds only the
Hellinger-affinity contraction step. -/
theorem eventProb_wrong_le_exp_neg (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ)
    (ρ_max : ℝ) (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hρ : ∀ q ∈ Θ, hellinger p q ≤ ρ_max)
    (hρpos : 0 < ρ_max) (hρlt : ρ_max < 1) :
    eventProb p n (wrongEvent p Θ n)
      ≤ (Θ.card : ℝ) * Real.exp (-(n : ℝ) * (- Real.log ρ_max)) := by
  have h1 := eventProb_wrong_le_card p Θ n ρ_max hp hq hρ
  have h2 : ρ_max ^ n ≤ Real.exp (-(n : ℝ) * (- Real.log ρ_max)) :=
    hellinger_pow_le_exp_neg hρpos hρlt n
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))

/-- Under pairwise identifiability a uniform strictly-sub-unit affinity bound
exists. The empty family gives the trivial bound `0`. -/
theorem exists_uniform_affinity_lt_one (p : W → ℝ) (Θ : Finset (W → ℝ))
    (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hne : ∀ q ∈ Θ, p ≠ q) :
    ∃ ρ_max : ℝ, 0 ≤ ρ_max ∧ ρ_max < 1 ∧
      ∀ q ∈ Θ, hellinger p q ≤ ρ_max := by
  classical
  by_cases hΘ : Θ.Nonempty
  · obtain ⟨q, hqΘ, hmax⟩ := Finset.exists_max_image Θ (fun r => hellinger p r) hΘ
    refine ⟨hellinger p q, hellinger_nonneg p q, ?_, fun r hr => hmax r hr⟩
    exact (hellinger_lt_one_iff_ne p q hp (hq q hqΘ)).2 (hne q hqΘ)
  · have hempty : Θ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hΘ
    refine ⟨0, le_refl _, by norm_num, ?_⟩
    intro q hq
    simp [hempty] at hq

/-- **Exponential exact-ML error decay under identifiability.** For a finite
family `Θ` of read distributions, none equal to the truth `p`, there is a
strictly positive rate `c` such that the exact probability that some
competitor ties or beats the truth after `n` iid reads is at most
`|Θ| * exp(-c n)`. -/
theorem eventProb_wrong_le_exp_neg_identifiable (p : W → ℝ) (Θ : Finset (W → ℝ))
    (n : ℕ) (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hne : ∀ q ∈ Θ, p ≠ q) :
    ∃ c : ℝ, 0 < c ∧
      eventProb p n (wrongEvent p Θ n) ≤ (Θ.card : ℝ) * Real.exp (-(n : ℝ) * c) := by
  classical
  obtain ⟨ρ_max, hρnn, hρlt, hρ⟩ := exists_uniform_affinity_lt_one p Θ hp hq hne
  by_cases hzero : ρ_max = 0
  · refine ⟨1, by norm_num, ?_⟩
    have h1 := eventProb_wrong_le_card p Θ n ρ_max hp hq hρ
    rw [hzero] at h1
    by_cases hn : n = 0
    · subst hn
      simpa using h1
    · have h0 : (0 : ℝ) ^ n = 0 := zero_pow hn
      rw [h0] at h1
      have hgoal : (Θ.card : ℝ) * 0 ≤ (Θ.card : ℝ) * Real.exp (-(n : ℝ) * 1) := by
        rw [mul_zero]
        positivity
      exact h1.trans hgoal
  · have hρpos : 0 < ρ_max := lt_of_le_of_ne hρnn (Ne.symm hzero)
    refine ⟨- Real.log ρ_max, ?_, ?_⟩
    · have hlog : Real.log ρ_max < 0 := (Real.log_neg_iff hρpos).mpr hρlt
      linarith
    · exact eventProb_wrong_le_exp_neg p Θ n ρ_max hp hq hρ hρpos hρlt

end AssemblyP1.HellingerExponentialDecay
