import Mathlib

/-!
# Finite Bayesian zero-one decision optimality

A finite observation space X and finite hypothesis space Θ carry an arbitrary
joint mass function J θ x. A deterministic decision d : X → Θ succeeds with
mass ∑_θ ∑_x [d x = θ] J θ x, which is exactly ∑_x J (d x) x.
If a pointwise MAP decision m has J θ x ≤ J (m x) x for every θ,x,
then m dominates every deterministic or normalized randomized decision under
prior-averaged zero-one success. The algebra does not need positivity or mass
normalization: those are required only when interpreting J probabilistically.

This is a finite Bayesian decision theorem, not the MB09 product-binomial
surrogate, nor an assembly-flow realization theorem.
-/

namespace AssemblyP1.FiniteBayesDecision

variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]

/-- Joint mass of successful deterministic decisions. -/
def success (J : Θ → X → ℝ) (d : X → Θ) : ℝ :=
  ∑ θ : Θ, ∑ x : X, if d x = θ then J θ x else 0

/-- Summing successful decisions over true hypotheses is pointwise evaluation. -/
theorem success_eq_observation_sum (J : Θ → X → ℝ) (d : X → Θ) :
    success J d = ∑ x : X, J (d x) x := by
  classical
  unfold success
  rw [Finset.sum_comm]
  simp

/-- A pointwise maximizer of the joint mass maximizes aggregate success among
all deterministic decisions, for any finite observation space. -/
theorem pointwise_MAP_optimal (J : Θ → X → ℝ) (m d : X → Θ)
    (hm : ∀ x θ, J θ x ≤ J (m x) x) :
    success J d ≤ success J m := by
  rw [success_eq_observation_sum, success_eq_observation_sum]
  exact Finset.sum_le_sum (fun x _ => hm x (d x))

/-- Success mass of a randomized decision kernel. -/
def randomizedSuccess (J : Θ → X → ℝ) (w : X → Θ → ℝ) : ℝ :=
  ∑ x : X, ∑ θ : Θ, w x θ * J θ x

/-- Randomization cannot improve on a pointwise MAP rule under zero-one loss. -/
theorem pointwise_MAP_optimal_randomized (J : Θ → X → ℝ)
    (m : X → Θ) (w : X → Θ → ℝ)
    (hm : ∀ x θ, J θ x ≤ J (m x) x)
    (hw : ∀ x θ, 0 ≤ w x θ)
    (hnorm : ∀ x, ∑ θ : Θ, w x θ = 1) :
    randomizedSuccess J w ≤ success J m := by
  rw [success_eq_observation_sum]
  unfold randomizedSuccess
  apply Finset.sum_le_sum
  intro x _
  calc
    (∑ θ : Θ, w x θ * J θ x)
        ≤ ∑ θ : Θ, w x θ * J (m x) x := by
            apply Finset.sum_le_sum
            intro θ _
            exact mul_le_mul_of_nonneg_left (hm x θ) (hw x θ)
    _ = (∑ θ : Θ, w x θ) * J (m x) x := by rw [Finset.sum_mul]
    _ = J (m x) x := by rw [hnorm]; ring

/-- For iid finite read observations, a pointwise posterior-mass maximizer is
prior-average optimal for all deterministic policies, at every sample size n,
including n = 0. The MAP maximizer's existence and normalization of prior/pmf
are handled separately; this theorem assumes the displayed pointwise inequality. -/
theorem finite_iid_MAP_optimal
    {R : Type*} [Fintype R]
    (n : ℕ) (π : Θ → ℝ) (p : Θ → R → ℝ)
    (m d : (Fin n → R) → Θ)
    (hm : ∀ x θ, π θ * (∏ i : Fin n, p θ (x i))
             ≤ π (m x) * (∏ i : Fin n, p (m x) (x i))) :
    success (fun θ x => π θ * ∏ i : Fin n, p θ (x i)) d
      ≤ success (fun θ x => π θ * ∏ i : Fin n, p θ (x i)) m := by
  exact pointwise_MAP_optimal _ m d hm

#print axioms pointwise_MAP_optimal
#print axioms pointwise_MAP_optimal_randomized
#print axioms finite_iid_MAP_optimal

end AssemblyP1.FiniteBayesDecision
