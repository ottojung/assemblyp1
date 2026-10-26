import AssemblyP1.HellingerExponentialDecay

/-!
# Two-competitor exponential exact-ML error bound (issue #281)

Small closed-form specialization of the generic finite-family exponential
bound `AssemblyP1.HellingerExponentialDecay.eventProb_wrong_le_exp_neg` to a
pair `Θ = {q₁, q₂}` of distinct competitors: the exact probability that
either competitor ties or beats the truth after `n` iid reads is at most
`2 * exp(-c n)` with `c = -log ρ_max > 0`.

This is the form cited alongside the two-genome non-monotonicity witness:
identifiability gives an exponential error *rate*, not a monotone success
curve. No claim is made that finite-sample success probability is monotone
in `n`, nor that likelihood itself grows exponentially.

Scope: generic finite read distributions; no genome or candidate-class
structure is assumed. No `axiom`, `sorry` or `admit`; the only kernel axioms
are `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace AssemblyP1.HellingerTwoCompetitor

open AssemblyP1.FiniteReadRecovery
open AssemblyP1.HellingerExponentialDecay
open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- **Two-competitor exponential exact-ML error bound.** For two distinct
competitor read distributions sharing a uniform sub-unit affinity bound
`ρ_max` against the truth, the exact probability that either ties or beats
the truth after `n` iid reads is at most `2 * exp (-(n : ℝ) * c)` with
`c = -log ρ_max`. -/
theorem eventProb_wrong_pair_le_two_mul_exp (p q₁ q₂ : W → ℝ) (n : ℕ)
    (ρ_max : ℝ) (hp : IsPmf p) (hq₁ : IsPmf q₁) (hq₂ : IsPmf q₂)
    (hne : q₁ ≠ q₂)
    (hρ₁ : hellinger p q₁ ≤ ρ_max) (hρ₂ : hellinger p q₂ ≤ ρ_max)
    (hρpos : 0 < ρ_max) (hρlt : ρ_max < 1) :
    eventProb p n (wrongEvent p {q₁, q₂} n)
      ≤ 2 * Real.exp (-(n : ℝ) * (- Real.log ρ_max)) := by
  classical
  have hq : ∀ q ∈ ({q₁, q₂} : Finset (W → ℝ)), IsPmf q := by
    intro q hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hq₁
    · exact hq₂
  have hρ : ∀ q ∈ ({q₁, q₂} : Finset (W → ℝ)), hellinger p q ≤ ρ_max := by
    intro q hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hρ₁
    · exact hρ₂
  have hcard : ({q₁, q₂} : Finset (W → ℝ)).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa using hne
  have h := eventProb_wrong_le_exp_neg p {q₁, q₂} n ρ_max hp hq hρ hρpos hρlt
  rw [hcard] at h
  simpa using h

end AssemblyP1.HellingerTwoCompetitor
