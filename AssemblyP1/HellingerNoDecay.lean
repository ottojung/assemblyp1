import AssemblyP1.HellingerExponentialDecay

/-!
# No-decay boundary for exact-ML error (issue #281)

Negative boundary complementing the generic finite-family exponential bound
`AssemblyP1.HellingerExponentialDecay.eventProb_wrong_le_exp_neg`: when the
competitor family `Θ` contains the truth `p` itself — in particular when a
competitor distribution *equals* the truth, so Hellinger affinity is one
(see `hellinger_lt_one_iff_ne`) — no read sample can statistically
distinguish the candidates. Every read tuple ties, ties count as errors, and
the exact wrong-selection probability is `1` at every sample size `n`.

Scope: generic finite read distributions; no genome or candidate-class
structure is assumed. This is a statement about the *error* probability, not
about likelihood growth, and it makes no monotonicity claim. No `axiom`,
`sorry` or `admit`; the only kernel axioms are `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace AssemblyP1.HellingerNoDecay

open AssemblyP1.FiniteReadRecovery
open AssemblyP1.HellingerExponentialDecay
open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- **No-decay boundary.** If the competitor family contains the truth `p`
(so some competitor is statistically indistinguishable from the truth),
every read tuple ties for the exact-ML lead and the wrong-selection event is
the whole tuple space: its exact probability is `1` for every `n`. -/
theorem eventProb_wrong_eq_one_of_mem (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ)
    (hp : IsPmf p) (hmem : p ∈ Θ) :
    eventProb p n (wrongEvent p Θ n) = 1 := by
  have hall : ∀ t : Fin n → W, wrongEvent p Θ n t :=
    fun t => ⟨p, hmem, le_refl _⟩
  unfold eventProb
  rw [Finset.sum_congr rfl (fun t _ => ite_eq_left (hall t))]
  rw [sum_tupleLikelihood, hp.2, one_pow]

end AssemblyP1.HellingerNoDecay
