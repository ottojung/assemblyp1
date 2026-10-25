import AssemblyP1.FiniteBayesDecision

/-!
# Conditional refinement audit for finite Bayes success

For an event `A` on the *old* observation space, conditional MAP success is
monotone after refinement only when the same event is lifted to the new space
by ignoring the added observation. The unnormalized event joint mass must also
be marginalized consistently. This is a mathematical finite-sample lemma; it
does not assert monotonicity for events whose definition changes with sample
size (for example, observing at least one occurrence of every read).
-/

namespace AssemblyP1.ConditionalRefinementAudit

variable {Θ X Y : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X] [Fintype Y]

/-- Success mass restricted to an event, with no normalization by the event
probability. -/
def eventSuccess (J : Θ → X → ℝ) (A : X → Prop) [DecidablePred A]
    (d : X → Θ) : ℝ :=
  ∑ x : X, if A x then J (d x) x else 0

/-- Success mass on the lifted event `A x` after observing `(x,y)`. -/
def liftedEventSuccess (K : Θ → X → Y → ℝ) (A : X → Prop)
    [DecidablePred A] (d : X → Y → Θ) : ℝ :=
  ∑ x : X, ∑ y : Y, if A x then K (d x y) x y else 0

/-- With consistent marginalization, optimizing over refined observations
cannot decrease success mass restricted to a fixed old-sample event. -/
theorem event_refinement_success_monotone
    (J : Θ → X → ℝ) (K : Θ → X → Y → ℝ) (A : X → Prop)
    [DecidablePred A] (old : X → Θ) (new : X → Y → Θ)
    (hmarg : ∀ θ x, (∑ y : Y, K θ x y) = J θ x)
    (hmax : ∀ x y θ, K θ x y ≤ K (new x y) x y) :
    eventSuccess J A old ≤ liftedEventSuccess K A new := by
  unfold eventSuccess liftedEventSuccess
  apply Finset.sum_le_sum
  intro x _
  by_cases hA : A x
  · simp only [if_pos hA]
    calc
      J (old x) x = ∑ y : Y, K (old x) x y := (hmarg (old x) x).symm
      _ ≤ ∑ y : Y, K (new x y) x y := by
        apply Finset.sum_le_sum
        intro y _
        exact hmax x y (old x)
  · simp [hA]

#print axioms event_refinement_success_monotone

end AssemblyP1.ConditionalRefinementAudit
