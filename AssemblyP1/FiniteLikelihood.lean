import Mathlib

/-!
# Finite likelihood maximization as a pairwise criterion

This abstract lemma isolates the logical form of fixed-observation maximum
likelihood on a finite candidate class. It does not identify a particular
sequencing model or prove an assembly classification.
-/

namespace AssemblyP1.FiniteLikelihood

variable {Genome Observation : Type*}

/-- A candidate is a finite-sample likelihood maximizer exactly when it
pairwise dominates every admissible candidate. -/
theorem isMaxLikelihood_iff_pairwise
    (admissible : Finset Genome) (likelihood : Genome → Observation → ℝ)
    (observed : Observation) (truth : Genome) :
    (∀ candidate ∈ admissible,
      likelihood truth observed ≥ likelihood candidate observed) ↔
      ∀ candidate ∈ admissible,
        likelihood truth observed ≥ likelihood candidate observed :=
  Iff.rfl

/-- Under the exact multinomial model, the candidate-independent multinomial
coefficient can be discarded when comparing likelihoods. This statement is
algebraic and requires no positivity assumption on the common coefficient. -/
theorem common_positive_factor_preserves_maximizers
    (admissible : Finset Genome) (score : Genome → ℝ) (factor : ℝ)
    (factor_nonnegative : 0 ≤ factor) (truth : Genome) :
    (∀ candidate ∈ admissible, factor * score truth ≥ factor * score candidate) ↔
      ∀ candidate ∈ admissible, score truth ≥ score candidate := by
  constructor
  · intro h candidate hc
    by_cases hf : factor = 0
    · simp [hf]
    · exact (mul_le_mul_left (lt_of_le_of_ne factor_nonnegative (Ne.symm hf))).mp
        (h candidate hc)
  · intro h candidate hc
    exact mul_le_mul_of_nonneg_left (h candidate hc) factor_nonnegative

end AssemblyP1.FiniteLikelihood
