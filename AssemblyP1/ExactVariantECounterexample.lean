import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Unrestricted-candidate-length exact Variant E counterexample (ACGT → ACACGT)

This file kernel-checks the finite, unrestricted-length exact-multinomial
counterexample.  The truth is the circular genome `ACGT`; the observed read
multiset is `{AC, AC, GT}` (three length-`2` reads at starts `0, 0, 2`); and the
competitor is the circular genome `ACACGT`, of a *different* length `6`.

Model scope.  The objective is the exact Variant E likelihood of
`docs/ml-formalization-contract.md`: the observation-only multinomial coefficient
is `3! / (2! 1!) = 3`, each read probability is its circular occurrence
multiplicity divided by the candidate's own intrinsic length, and candidate
length is **not** fixed externally.  The candidate universe is now literally
`SourceFaithfulIs.Genome DNA`, that is: every nonempty circular DNA sequence of
every length, so "unrestricted" is a property of the statement rather than a
comment about it.

Hypothesis scope.  The hypothesis side uses the shared source-faithful
predicate `SourceFaithfulIs.InformationFeasible` at full strength, discharged by
`decide` on `truthGenome` with `L = 2` and the realized start set `{0, 2}`.
This is strictly stronger than the previous "no positive-length repeat"
shortcut: that shortcut had to be *argued* in order to conclude the bridging
clauses are vacuous, whereas here vacuity is checked by the same computation
that checks every other repeat of the truth, and no repeat is enumerated by hand.

The conclusion is unchanged and is a genuine failure of the model-specific
maximum-likelihood claim: the truth is not an exact maximum-likelihood candidate
even though the realization satisfies every clause of `I_s`.
-/

namespace AssemblyP1.ExactVariantECounterexample

open SourceFaithfulIs

inductive DNA where
  | A | C | G | T
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The true circular genome `ACGT` in the shared source-faithful
representation. -/
/- This genome is a reducible abbreviation, not an opaque `def`, so that the
   `Fin`-indexed numerals and the `Decidable` instances of the shared layer are
   found by instance search when the finite `I_s` membership is decided. -/
abbrev truthGenome : SourceFaithfulIs.Genome DNA where
  len := 4
  len_pos := by norm_num
  sym := ![DNA.A, DNA.C, DNA.G, DNA.T]

/-- A strictly more likely nonempty circular candidate of a different length,
`ACACGT`, in the shared source-faithful representation. -/
abbrev competitorGenome : SourceFaithfulIs.Genome DNA where
  len := 6
  len_pos := by norm_num
  sym := ![DNA.A, DNA.C, DNA.A, DNA.C, DNA.G, DNA.T]

/-- Number of circular positions of `g` at which the symbol `x` is followed by
`symbol y`.  This is the multiplicity `d_xy` of the read type `xy`. -/
def dinucleotideCount (g : SourceFaithfulIs.Genome DNA) (x y : DNA) : ℕ :=
  (List.range g.len).countP fun i => g.cycl i == x && g.cycl (i + 1) == y

/--
Exact multinomial likelihood for the fixed observed multiset `{AC, AC, GT}`.

This is the finite specialization of exact Variant E from
`docs/ml-formalization-contract.md`: the observation-only multinomial
coefficient is `3! / (2! 1!) = 3`, each read probability is its circular
occurrence multiplicity divided by the candidate's own intrinsic length, and
candidate length is not fixed externally.
-/
def sampleLikelihood (g : SourceFaithfulIs.Genome DNA) : ℚ :=
  3 * ((dinucleotideCount g .A .C : ℚ) / (g.len : ℚ)) ^ 2 *
    ((dinucleotideCount g .G .T : ℚ) / (g.len : ℚ))

/-- The realized length-`2` read start positions `0, 0, 2`, as a set of
distinct placements.  Multiplicity of a read *type* is recorded separately, by
the squared exponent in `sampleLikelihood`. -/
def readStarts : Finset (Fin 4) := {0, 2}

/-- The two distinct realized read types returned by those placements. -/
def observedAC : Fin 2 → DNA := ![DNA.A, DNA.C]
def observedGT : Fin 2 → DNA := ![DNA.G, DNA.T]

/-- The realized placements really do produce the observed read multiset: the
start `0` is used twice and the start `2` once. -/
theorem realized_reads :
    truthGenome.window 2 0 = observedAC ∧ truthGenome.window 2 2 = observedGT := by
  decide

/-! ## The source-faithful `I_s` hypothesis -/

/-- Every true position is covered by at least one realized length-two read:
this is the first clause of `I_s`, stated with the shared `Covers` predicate. -/
theorem truth_covers : SourceFaithfulIs.Covers truthGenome 2 readStarts := by
  unfold SourceFaithfulIs.Covers
  decide

/-- **Full source-faithful `I_s` membership**: all three clauses of Shomorony et
al. Eq. (1) hold for the truth under the realized read placements, checked by
finite computation over every admissible repeat length and every selection of
starts.  For this truth no two distinct starts agree on any window of length
`1 ≤ e < 4`, so there is no repeat at all and clauses 2 and 3 hold vacuously —
but that is a *conclusion* of the computation, not an assumption. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 2 readStarts := by
  unfold SourceFaithfulIs.InformationFeasible
  decide

/-! ## Exact likelihood arithmetic -/

theorem truth_AC_count : dinucleotideCount truthGenome .A .C = 1 := by decide
theorem truth_GT_count : dinucleotideCount truthGenome .G .T = 1 := by decide
theorem competitor_AC_count : dinucleotideCount competitorGenome .A .C = 2 := by decide
theorem competitor_GT_count : dinucleotideCount competitorGenome .G .T = 1 := by decide

theorem truth_likelihood : sampleLikelihood truthGenome = 3 / 64 := by
  unfold sampleLikelihood
  rw [truth_AC_count, truth_GT_count]
  norm_num [truthGenome]

theorem competitor_likelihood : sampleLikelihood competitorGenome = 1 / 18 := by
  unfold sampleLikelihood
  rw [competitor_AC_count, competitor_GT_count]
  norm_num [competitorGenome]

theorem competitor_beats_truth :
    sampleLikelihood truthGenome < sampleLikelihood competitorGenome := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

/-- Maximum-likelihood predicate for this finite exact-Variant-E
specialization.  Candidates range over *every* nonempty circular DNA sequence,
so competitor length is deliberately unrestricted. -/
def IsMaximumLikelihood (g : SourceFaithfulIs.Genome DNA) : Prop :=
  ∀ candidate : SourceFaithfulIs.Genome DNA, sampleLikelihood candidate ≤ sampleLikelihood g

theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihood truthGenome := by
  intro h
  have hcomp := h competitorGenome
  rw [competitor_likelihood, truth_likelihood] at hcomp
  norm_num at hcomp

/--
Kernel-checked finite counterexample to unrestricted-candidate-length exact
Variant E: the realized reads satisfy **full** source-faithful information
feasibility `R ∈ I_s`, yet the truth is not an exact multinomial
maximum-likelihood candidate among circular genomes of any length.

This theorem does not claim anything about fixed-length exact ML, the
Medvedev–Brudno separable approximation, the Section 6.2 flow feasible set, or
which interpretation Shomorony et al. intended in the published open question.
-/
theorem finite_unrestricted_exact_variant_e_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 2 readStarts ∧
      ¬ IsMaximumLikelihood truthGenome :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

end AssemblyP1.ExactVariantECounterexample
