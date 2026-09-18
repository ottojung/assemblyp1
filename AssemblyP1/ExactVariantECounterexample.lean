import Mathlib

namespace AssemblyP1.ExactVariantECounterexample

inductive DNA where
  | A | C | G | T
  deriving DecidableEq, Repr, Inhabited

abbrev Genome := List DNA

private def base (g : Genome) (i : Nat) : DNA :=
  g[i % g.length]!

private def dinucleotideCount (g : Genome) (x y : DNA) : Nat :=
  (List.range g.length).countP fun i => base g i = x && base g (i + 1) = y

/-- Exact multinomial likelihood for the concrete observed multiset `AC, AC, GT`.
The multinomial coefficient is `3! / (2! 1!) = 3`; each read probability is
its circular occurrence count divided by the candidate's own length. -/
private def sampleLikelihood (g : Genome) : ℚ :=
  3 * (dinucleotideCount g .A .C / g.length : ℚ) ^ 2 *
    (dinucleotideCount g .G .T / g.length : ℚ)

private def truth : Genome := [.A, .C, .G, .T]
private def competitor : Genome := [.A, .C, .A, .C, .G, .T]
private def starts : List Nat := [0, 0, 2]

/-- The realized length-two reads cover every position of the true circular genome. -/
private def covered : Prop :=
  ∀ i : Fin truth.length, ∃ s ∈ starts, ∃ d < 2, i.val = (s + d) % truth.length

/-- Distinct starts in `ACGT` already disagree in their first symbol, so no
positive-length repeat can occur at distinct starts. -/
private def noPositiveRepeat : Prop :=
  ∀ i j : Fin truth.length, i ≠ j → base truth i.val ≠ base truth j.val

theorem truth_covered : covered := by decide

theorem truth_has_no_positive_repeat : noPositiveRepeat := by decide

theorem truth_AC_count : dinucleotideCount truth .A .C = 1 := by decide
theorem truth_GT_count : dinucleotideCount truth .G .T = 1 := by decide
theorem competitor_AC_count : dinucleotideCount competitor .A .C = 2 := by decide
theorem competitor_GT_count : dinucleotideCount competitor .G .T = 1 := by decide

theorem truth_likelihood : sampleLikelihood truth = 3 / 64 := by
  norm_num [sampleLikelihood, dinucleotideCount, truth, base]

theorem competitor_likelihood : sampleLikelihood competitor = 1 / 18 := by
  norm_num [sampleLikelihood, dinucleotideCount, competitor, base]

theorem competitor_beats_truth : sampleLikelihood truth < sampleLikelihood competitor := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

end AssemblyP1.ExactVariantECounterexample
