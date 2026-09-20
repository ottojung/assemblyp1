import Mathlib

/-!
# Unrestricted-length exact-multinomial counterexample with non-vacuous bridging

This file kernel-checks that allowing the candidate genome length to vary does
**not** restore the true sequence for the repository's source-faithful
fixed-length witness (issue #31), and indeed strictly strengthens the
counterexample there.

Scope and assumptions.  The candidate universe is the set of *nonempty finite
circular genomes over a fixed four-symbol alphabet, of any length*; the
objective is the literal Medvedev–Brudno §6.1 exact read-count multinomial
likelihood, whose denominator is the candidate's own length `N(D)`.  This is
the repository's *unrestricted-length exact* variant ("Variant E" with
candidate-dependent length).  The file does **not** claim anything about
fixed-length exact ML, the separable/binomial approximation, the Section 6.2
flow feasible set, or which of those the 2016 source intended.

Instance (issue #31):

* true circular genome `truth = AAABB` (`G = 5`);
* read length `L = 3`, realized starts `0, 1, 4`;
* observed read multiset `{AAA, AAB, BAA}`, each with multiplicity one;
* an unrestricted-length competitor `competitor = AAABAAAAB` of length `9`.

For the truth, each observed type occurs once, so the exact likelihood part is
`(1/5)^3`.  For the competitor the circular 3-windows are
`AAA (x3), AAB (x2), BAA (x2)`, so the likelihood part is
`(3/9)(2/9)(2/9)`.  Including the observation-only multinomial coefficient
`3! = 6`, the truth has likelihood `6/125` and the competitor `8/81`, a ratio
of `500/243 > 1`.  Hence the truth is not a maximum-likelihood maximizer once
candidate length is unrestricted.

Unlike `AssemblyP1/ExactVariantECounterexample.lean`, whose truth `ACGT` has no
positive-length repeat and therefore only *vacuous* bridging obligations, the
certificate below records the same **non-vacuous** source-faithful facts as the
fixed-length witness: coverage, and a maximal length-1 triple repeat that is
all-bridged.  Thus the variable-length failure is not an artifact of vacuous
repeat hypotheses.

The file does not prove that `500/243` is the unrestricted optimum; that
sharper statement is a mathematical proof recorded in
`docs/variable-length-exact-ml-frontier.md` and checked numerically by
`scripts/verify_variable_length_frontier.py`.
-/

namespace AssemblyP1.VariableLengthExactCounterexample

/-- Four-symbol alphabet: the two witness symbols `A`, `B` plus two unused
symbols so that "any circular genome over the alphabet" is the full candidate
class. -/
inductive Base where
  | A
  | B
  | C
  | G
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A circular genome is a nonempty list of symbols. -/
abbrev Genome := List Base

/-- The `i`-th symbol of a circular genome; wraps around and defaults out of
range (only nonempty candidates are ever scored). -/
def base (g : Genome) (i : Nat) : Base :=
  g[i % g.length]!

/-- Number of circular start positions whose length-3 window is `(a, b, c)`. -/
def tripCount (g : Genome) (a b c : Base) : Nat :=
  (List.range g.length).countP fun i =>
    base g i == a && base g (i + 1) == b && base g (i + 2) == c

/-- The true circular genome `S = AAABB`. -/
def truth : Genome := [.A, .A, .A, .B, .B]

/-- The unrestricted-length competitor `D = A A A B A A A A B` (length 9). -/
def competitor : Genome :=
  [.A, .A, .A, .B, .A, .A, .A, .A, .B]

/--
Exact Medvedev–Brudno read-count multinomial likelihood (up to the
observation-only multinomial coefficient) of the observed multiset
`{AAA, AAB, BAA}`, each with multiplicity one, under a circular candidate of
any length.

The observation coefficient is `3! = 6`.  The denominator is the candidate's
own length, so candidate length is unrestricted.
-/
def likelihood (g : Genome) : ℚ :=
  (6 : ℚ) * ((tripCount g .A .A .A : ℚ) / (g.length : ℚ)) *
    ((tripCount g .A .A .B : ℚ) / (g.length : ℚ)) *
    ((tripCount g .B .A .A : ℚ) / (g.length : ℚ))

/-- Maximum-likelihood predicate over *every* nonempty circular genome of any
length. -/
def IsMaximumLikelihood (g : Genome) : Prop :=
  ∀ candidate : Genome, candidate ≠ [] → likelihood candidate ≤ likelihood g

/-! ## Exact counts and likelihoods -/

theorem truth_trip_AAA : tripCount truth .A .A .A = 1 := by decide
theorem truth_trip_AAB : tripCount truth .A .A .B = 1 := by decide
theorem truth_trip_BAA : tripCount truth .B .A .A = 1 := by decide

theorem competitor_trip_AAA : tripCount competitor .A .A .A = 3 := by decide
theorem competitor_trip_AAB : tripCount competitor .A .A .B = 2 := by decide
theorem competitor_trip_BAA : tripCount competitor .B .A .A = 2 := by decide

theorem truth_length : truth.length = 5 := by decide
theorem competitor_length : competitor.length = 9 := by decide

theorem likelihood_truth : likelihood truth = 6 / 125 := by
  unfold likelihood
  rw [truth_trip_AAA, truth_trip_AAB, truth_trip_BAA, truth_length]
  norm_num

theorem likelihood_competitor : likelihood competitor = 8 / 81 := by
  unfold likelihood
  rw [competitor_trip_AAA, competitor_trip_AAB, competitor_trip_BAA,
    competitor_length]
  norm_num

/-- The unrestricted competitor strictly beats the truth. -/
theorem competitor_beats_truth : likelihood truth < likelihood competitor := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

/-- Therefore the truth is not unrestricted-length maximum likelihood. -/
theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihood truth := by
  intro h
  have hcomp := h competitor (by decide)
  rw [likelihood_competitor, likelihood_truth] at hcomp
  norm_num at hcomp

/-! ## Source-faithful `I_s` certificate (identical to the fixed-length witness) -/

/-- The realized read start positions `0, 1, 4`. -/
def readStarts : Finset Nat := {0, 1, 4}

/-- Coverage: the realized length-3 reads at starts `0, 1, 4` cover every
circular position of the truth. -/
def Covers (g : Genome) : Prop :=
  ∀ p : Fin g.length, ∃ r ∈ readStarts, ∃ d : Fin 3,
    p.val = (r + d.val) % g.length

/--
Concrete source-faithful triple-repeat certificate: the length-1 windows at
starts `0, 1, 2` are equal (`A`), the three-copy maximality condition holds
(the preceding symbols `B, A, A` are not all equal and the following symbols
`A, A, B` are not all equal), and every one of the three copies is bridged by a
realized read: the read at `4` bridges the copy at `0`, the read at `0` bridges
the copy at `1`, and the read at `1` bridges the copy at `2`.

Bridging a length-1 copy at `t` by a length-3 read starting at `r` means
`t = r + 1 (mod 5)`, i.e. the copy is strictly interior to the read.
-/
def TripleRepeatAllBridged (g : Genome) : Prop :=
  base g 0 = base g 1 ∧ base g 1 = base g 2 ∧
  ¬(base g 4 = base g 0 ∧ base g 0 = base g 1) ∧
  ¬(base g 1 = base g 2 ∧ base g 2 = base g 3) ∧
  (∀ t : Fin 5, (t.val = 0 ∨ t.val = 1 ∨ t.val = 2) →
    ∃ r ∈ readStarts, (r + 1) % 5 = t.val)

/-- Coverage holds for the truth. -/
theorem truth_covered : Covers truth := by
  unfold Covers
  decide

/-- The maximal length-1 triple repeat is all-bridged for the truth. -/
theorem truth_triple_repeat_all_bridged : TripleRepeatAllBridged truth := by
  unfold TripleRepeatAllBridged
  decide

/-- The instance-specific, kernel-checked part of the source-faithful `I_s`
hypothesis: coverage plus the maximal all-bridged length-1 triple repeat. -/
def SourceHypotheses (g : Genome) : Prop :=
  Covers g ∧ TripleRepeatAllBridged g

theorem truth_source_hypotheses : SourceHypotheses truth :=
  ⟨truth_covered, truth_triple_repeat_all_bridged⟩

/-! ## Main finite theorem -/

/--
Kernel-checked finite counterexample to unrestricted-candidate-length exact
Variant E on a **non-vacuously** bridging source-faithful instance: the truth
`AAABB` with realized reads at starts `0, 1, 4` satisfies coverage and the
all-bridged triple-repeat certificate, yet a length-9 candidate is strictly
more likely.

This strictly refines the fixed-length result of
`AssemblyP1/FixedLengthExactCounterexample.lean` (same instance, ratio `2`
among same-length candidates): allowing the candidate length to vary raises the
winning ratio to `500/243` and cannot restore the truth.
-/
theorem variable_length_exact_counterexample :
    SourceHypotheses truth ∧ ¬ IsMaximumLikelihood truth :=
  ⟨truth_source_hypotheses, truth_not_maximum_likelihood⟩

end AssemblyP1.VariableLengthExactCounterexample
