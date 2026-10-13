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

/-! ## The pointwise MAP rule exists on any nonempty finite hypothesis space. -/

/-- Choose a posterior joint-mass maximizer for each observed sample. -/
noncomputable def chooseMAP [Nonempty Θ] (J : Θ → X → ℝ) (x : X) : Θ :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset Θ)
      (fun θ : Θ => J θ x) (Finset.univ_nonempty))

omit [DecidableEq Θ] [Fintype X] in
/-- The selected finite MAP rule genuinely maximizes every observation score. -/
theorem chooseMAP_maximizes [Nonempty Θ] (J : Θ → X → ℝ)
    (x : X) (θ : Θ) : J θ x ≤ J (chooseMAP J x) x := by
  unfold chooseMAP
  have h := Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset Θ)
      (fun a : Θ => J a x) (Finset.univ_nonempty))
  exact h.2 θ (Finset.mem_univ θ)

/-- The constructed MAP rule is optimal among all deterministic decisions. -/
theorem chooseMAP_optimal [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ) :
    success J d ≤ success J (chooseMAP J) := by
  exact pointwise_MAP_optimal J (chooseMAP J) d
    (fun x θ => chooseMAP_maximizes J x θ)

/-- The same MAP rule also dominates every normalized randomized decision. -/
theorem chooseMAP_optimal_randomized [Nonempty Θ] (J : Θ → X → ℝ)
    (w : X → Θ → ℝ)
    (hw : ∀ x θ, 0 ≤ w x θ)
    (hnorm : ∀ x, ∑ θ : Θ, w x θ = 1) :
    randomizedSuccess J w ≤ success J (chooseMAP J) := by
  exact pointwise_MAP_optimal_randomized J (chooseMAP J) w
    (fun x θ => chooseMAP_maximizes J x θ) hw hnorm

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
#print axioms chooseMAP_maximizes
#print axioms chooseMAP_optimal
#print axioms chooseMAP_optimal_randomized

end AssemblyP1.FiniteBayesDecision
