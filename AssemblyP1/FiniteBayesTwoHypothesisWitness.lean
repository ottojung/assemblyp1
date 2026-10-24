import Mathlib
import AssemblyP1.FiniteBayesDecision

/-!
# A tiny normalized iid finite Bayes/MAP witness (#269)

This fully explicit two-candidate, binary-read model records the boundary case
`n = 0` and the first read.  Both candidates have the same normalized read pmf,
the prior is uniform on the two candidates, and a deterministic tie rule picks
candidate zero.  Every deterministic policy has prior-average success `1/2`;
the selected MAP rule attains it.  This is a concrete kernel-checkable instance,
not a substitute for the general theorem in `FiniteBayesDecision`.
-/

namespace AssemblyP1.FiniteBayesTwoHypothesisWitness

open Finset BigOperators

abbrev Candidate := Fin 2
abbrev Read := Fin 2

/-- Uniform prior on the two candidate classes. -/
noncomputable def prior (_θ : Candidate) : ℝ := 1 / 2

/-- A candidate-independent fair binary read pmf. -/
noncomputable def readPmf (_θ : Candidate) (_w : Read) : ℝ := 1 / 2

theorem prior_normalized : ∑ θ : Candidate, prior θ = 1 := by
  norm_num [prior]

theorem readPmf_normalized (θ : Candidate) : ∑ w : Read, readPmf θ w = 1 := by
  norm_num [readPmf]

/-- Empty-sample joint mass; the empty product is exactly one. -/
noncomputable def jointZero (θ : Candidate) (_x : Fin 0 → Read) : ℝ := prior θ

/-- One-read iid joint mass for the exact finite model. -/
noncomputable def jointOne (θ : Candidate) (x : Fin 1 → Read) : ℝ :=
  prior θ * ∏ i : Fin 1, readPmf θ (x i)

/-- The deterministic tie rule returns candidate zero. -/
def tiePolicy {n : ℕ} (_x : Fin n → Read) : Candidate := 0

theorem jointZero_tie_is_MAP (x : Fin 0 → Read) (θ : Candidate) :
    jointZero θ x ≤ jointZero (tiePolicy x) x := by
  simp [jointZero, prior]

theorem jointOne_tie_is_MAP (x : Fin 1 → Read) (θ : Candidate) :
    jointOne θ x ≤ jointOne (tiePolicy x) x := by
  simp [jointOne, prior, readPmf]

theorem empty_policy_optimal (d : (Fin 0 → Read) → Candidate) :
    FiniteBayesDecision.success jointZero d ≤
      FiniteBayesDecision.success jointZero tiePolicy := by
  exact FiniteBayesDecision.pointwise_MAP_optimal jointZero tiePolicy d
    (fun x θ => jointZero_tie_is_MAP x θ)

theorem one_read_policy_optimal (d : (Fin 1 → Read) → Candidate) :
    FiniteBayesDecision.success jointOne d ≤
      FiniteBayesDecision.success jointOne tiePolicy := by
  exact FiniteBayesDecision.pointwise_MAP_optimal jointOne tiePolicy d
    (fun x θ => jointOne_tie_is_MAP x θ)

theorem empty_success_eq_half :
    FiniteBayesDecision.success jointZero tiePolicy = 1 / 2 := by
  norm_num [FiniteBayesDecision.success, jointZero, tiePolicy, prior]

theorem one_read_success_eq_half :
    FiniteBayesDecision.success jointOne tiePolicy = 1 / 2 := by
  norm_num [FiniteBayesDecision.success, jointOne, tiePolicy, prior, readPmf]

#print axioms prior_normalized
#print axioms readPmf_normalized
#print axioms empty_policy_optimal
#print axioms one_read_policy_optimal
#print axioms empty_success_eq_half
#print axioms one_read_success_eq_half

end AssemblyP1.FiniteBayesTwoHypothesisWitness
