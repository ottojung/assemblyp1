import Mathlib

namespace AssemblyP1.ExactVariantECounterexample

inductive DNA where
  | A | C | G | T
  deriving DecidableEq, BEq, Repr, Inhabited

abbrev Genome := List DNA

private def base (g : Genome) (i : Nat) : DNA :=
  g[i % g.length]!

private def dinucleotideCount (g : Genome) (x y : DNA) : Nat :=
  (List.range g.length).countP fun i => base g i == x && base g (i + 1) == y

/--
Exact multinomial likelihood for the fixed observed multiset `{AC, AC, GT}`.

This is the finite specialization of exact Variant E from
`docs/ml-formalization-contract.md`: the observation-only multinomial
coefficient is `3! / (2! 1!) = 3`, each read probability is its circular
occurrence multiplicity divided by the candidate's own intrinsic length, and
candidate length is not fixed externally.
-/
def sampleLikelihood (g : Genome) : ℚ :=
  3 * ((dinucleotideCount g .A .C : ℚ) / (g.length : ℚ)) ^ 2 *
    ((dinucleotideCount g .G .T : ℚ) / (g.length : ℚ))

/-- The true circular genome in the finite counterexample. -/
def truth : Genome := [.A, .C, .G, .T]

/-- A strictly more likely nonempty circular candidate of a different length. -/
def competitor : Genome := [.A, .C, .A, .C, .G, .T]

private def starts : List Nat := [0, 0, 2]

/-- Every true position is covered by at least one realized length-two read. -/
private def covered : Prop :=
  ∀ i : Fin truth.length, ∃ s ∈ starts, ∃ d < 2, i.val = (s + d) % truth.length

/--
For the concrete truth `ACGT`, distinct circular starts already disagree in
their first symbol. Hence no positive-length repeat exists at distinct starts.
This is stronger than the repeat absence needed to make the triple-repeat and
interleaved-repeat bridging obligations vacuous.
-/
private def noPositiveRepeat : Prop :=
  ∀ i j : Fin truth.length, i ≠ j → base truth i.val ≠ base truth j.val

/--
The concrete finite information-feasibility facts needed by the counterexample:
coverage holds, and the stronger no-positive-repeat fact makes the source
triple/interleaved bridging clauses vacuous.
-/
def informationFeasible : Prop := covered ∧ noPositiveRepeat

/--
Maximum-likelihood predicate for this finite exact-Variant-E specialization.
Candidates range over every nonempty finite circular genome, so competitor
length is deliberately unrestricted.
-/
def IsMaximumLikelihood (g : Genome) : Prop :=
  ∀ candidate : Genome, candidate ≠ [] →
    sampleLikelihood candidate ≤ sampleLikelihood g

theorem truth_covered : covered := by
  unfold covered
  decide

theorem truth_has_no_positive_repeat : noPositiveRepeat := by
  unfold noPositiveRepeat
  decide

theorem truth_information_feasible : informationFeasible :=
  ⟨truth_covered, truth_has_no_positive_repeat⟩

theorem truth_AC_count : dinucleotideCount truth .A .C = 1 := by decide
theorem truth_GT_count : dinucleotideCount truth .G .T = 1 := by decide
theorem competitor_AC_count : dinucleotideCount competitor .A .C = 2 := by decide
theorem competitor_GT_count : dinucleotideCount competitor .G .T = 1 := by decide

theorem truth_likelihood : sampleLikelihood truth = 3 / 64 := by
  unfold sampleLikelihood
  rw [truth_AC_count, truth_GT_count]
  norm_num [truth]

theorem competitor_likelihood : sampleLikelihood competitor = 1 / 18 := by
  unfold sampleLikelihood
  rw [competitor_AC_count, competitor_GT_count]
  norm_num [competitor]

theorem competitor_beats_truth : sampleLikelihood truth < sampleLikelihood competitor := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihood truth := by
  intro h
  have hcomp := h competitor (by decide)
  rw [competitor_likelihood, truth_likelihood] at hcomp
  norm_num at hcomp

/--
Kernel-checked finite counterexample to unrestricted-candidate-length exact
Variant E: the realized reads satisfy coverage and the bridging obligations are
vacuous because the truth has no positive-length repeats, yet the truth is not
an exact multinomial maximum-likelihood candidate.

This theorem does not claim anything about fixed-length exact ML, the
Medvedev–Brudno separable approximation, the Section 6.2 flow feasible set, or
which interpretation Shomorony et al. intended in the published open question.
-/
theorem finite_unrestricted_exact_variant_e_counterexample :
    informationFeasible ∧ ¬ IsMaximumLikelihood truth :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

end AssemblyP1.ExactVariantECounterexample
