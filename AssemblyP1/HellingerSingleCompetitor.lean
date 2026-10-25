import AssemblyP1.HellingerExponentialDecay

/-!
# Single-competitor exponential exact-ML error bound (issue #281)

Base cell of the finite-family exponential decay: specializing the generic
bound `AssemblyP1.HellingerExponentialDecay.eventProb_wrong_le_exp_neg` to a
singleton family `Θ = {q}`. The exact probability that the single competitor
ties or beats the truth after `n` iid reads is at most `exp(-c n)` with
`c = -log ρ_max > 0` — no family-size prefactor.

Scope: generic finite read distributions; no genome or candidate-class
structure is assumed. No claim is made that finite-sample success probability
is monotone in `n`, nor that likelihood itself grows exponentially. Ties count
as errors. No `axiom`, `sorry` or `admit`; the only kernel axioms are
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace AssemblyP1.HellingerSingleCompetitor

open AssemblyP1.FiniteReadRecovery
open AssemblyP1.HellingerExponentialDecay
open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- **Single-competitor exponential exact-ML error bound.** For one competitor
read distribution with affinity bound `ρ_max` against the truth, the exact
probability that it ties or beats the truth after `n` iid reads is at most
`exp (-(n : ℝ) * c)` with `c = -log ρ_max`. -/
theorem eventProb_wrong_single_le_exp_neg (p q : W → ℝ) (n : ℕ)
    (ρ_max : ℝ) (hp : IsPmf p) (hq : IsPmf q)
    (hρ : hellinger p q ≤ ρ_max)
    (hρpos : 0 < ρ_max) (hρlt : ρ_max < 1) :
    eventProb p n (wrongEvent p {q} n)
      ≤ Real.exp (-(n : ℝ) * (- Real.log ρ_max)) := by
  classical
  have hqmem : ∀ r ∈ ({q} : Finset (W → ℝ)), IsPmf r := by
    intro r hmem
    simp only [Finset.mem_singleton] at hmem
    rw [hmem]
    exact hq
  have hρmem : ∀ r ∈ ({q} : Finset (W → ℝ)), hellinger p r ≤ ρ_max := by
    intro r hmem
    simp only [Finset.mem_singleton] at hmem
    rw [hmem]
    exact hρ
  have h := eventProb_wrong_le_exp_neg p {q} n ρ_max hp hqmem hρmem hρpos hρlt
  rw [Finset.card_singleton] at h
  simpa using h

end AssemblyP1.HellingerSingleCompetitor
