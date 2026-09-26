import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Fixed-length exact-multinomial counterexample (issue #31)

This file kernel-checks the concrete, same-length witness to the claim that
source-faithful bridging hypotheses force the true sequence to be an exact
maximum-likelihood assembly.

Scope.  The candidate universe here is the set of circular genomes of length
`G = 5` over a fixed four-symbol alphabet, and the objective is the exact
Medvedev–Brudno read-count multinomial likelihood evaluated at the observed
read counts.  This is the repository's *fixed-length exact* variant.  The file
does **not** claim anything about unrestricted-length exact ML, the
separable/binomial approximation, the Section 6.2 flow feasible set, or which
of those the source paper intended.

Instance (issue #31):

* true circular genome `truth = AAABB` (length `G = 5`);
* read length `L = 3`, realized starts `0, 1, 4`;
* observed read multiset `{AAA, AAB, BAA}`, each with multiplicity one;
* same-length competitor `competitor = AAAAB`.

The observed types occur once each in `truth`.  In `competitor`, `AAA` occurs
twice and `AAB`, `BAA` once each.  With equal candidate length the multinomial
coefficient and the length factor cancel, so the exact likelihood ratio is
exactly `2`: the competitor is strictly more likely than the truth, so the
truth is not a maximum-likelihood maximizer even among same-length candidates.

The hypothesis side uses the shared source-faithful layer
`AssemblyP1.SourceFaithfulIs` directly.  `truth_information_feasible` is a
kernel-checked proof of **full** `I_s` membership, that is
`SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts`, not a
weakened stand-in for it: `decide` discharges the coverage clause, the
universally quantified all-bridged clause over *all* selected triple repeats at
all admissible lengths, and the universally quantified bridged clause over *all*
interleaved repeat pairs.  No repeat is enumerated by hand.

For this instance that is a genuine content claim, not a formality: the truth
`AAABB` has a maximal length-`1` repeat at starts `0, 2` and another at `3, 4`,
the maximal length-`1` triple repeat at starts `0, 1, 2` is all-bridged by the
reads at `4, 0, 1`, and there is in fact no interleaved repeat pair, so the
third clause of `I_s` holds vacuously for this truth.
-/

namespace AssemblyP1.FixedLengthExactCounterexample

open SourceFaithfulIs

/-- Four-symbol alphabet for the fixed-length candidate universe.  It is the
DNA alphabet under a renaming that keeps the two symbols `A`, `B` of the
issue's witness. -/
inductive Base where
  | A
  | B
  | C
  | G
  deriving DecidableEq, Inhabited, Repr

/-- A circular genome of length `5`. -/
abbrev Genome := Fin 5 → Base

/-- The `i`-th symbol of a circular genome of length `5`. -/
def cyc (g : Genome) (i : Nat) : Base :=
  g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The length-`3` circular window of `g` beginning at start `r`, i.e. the
read type obtained by a length-`3` read placed at `r`. -/
def window (g : Genome) (r : Fin 5) : Fin 3 → Base :=
  fun d => cyc g (r.val + d.val)

/-- Read type `AAA`. -/
def readAAA : Fin 3 → Base := fun _ => Base.A

/-- Read type `AAB`. -/
def readAAB : Fin 3 → Base := ![Base.A, Base.A, Base.B]

/-- Read type `BAA`. -/
def readBAA : Fin 3 → Base := ![Base.B, Base.A, Base.A]

/-- Number of circular start positions of `g` whose length-`3` window is `w`. -/
def occ (g : Genome) (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => window g r = w)).card

/-- The true circular genome `S = AAABB`, as a shared-layer circular genome. -/
/- This genome is a reducible abbreviation, not an opaque `def`, so that the
   `Fin`-indexed numerals and the `Decidable` instances of the shared layer are
   found by instance search when the finite `I_s` membership is decided. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.B, Base.B]

/-- The same-length competitor `D = AAAAB`, as a shared-layer circular genome. -/
abbrev competitorGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.A, Base.B]

/-- The true circular genome `S = AAABB` in the candidate universe. -/
def truth : Genome := ![Base.A, Base.A, Base.A, Base.B, Base.B]

/-- The same-length competitor `D = AAAAB` in the candidate universe. -/
def competitor : Genome := ![Base.A, Base.A, Base.A, Base.A, Base.B]

/-- The truth of the candidate universe and of the shared source-faithful layer
are the same circular sequence; this pins the two presentations together so the
likelihood and the hypothesis refer to one genome. -/
theorem truth_eq_genome : truth = truthGenome.sym := rfl

/-- Likewise for the competitor. -/
theorem competitor_eq_genome : competitor = competitorGenome.sym := rfl

/-! ## Exact fixed-length multinomial likelihood -/

/--
Exact Medvedev–Brudno read-count multinomial likelihood of the observed
multiset `{AAA, AAB, BAA}` under a length-`5` circular candidate.

The observation has `n = 3` reads, each observed type having multiplicity one,
so the observation-only multinomial coefficient is `3! = 6`, and the candidate
length is `5` for every candidate in `Genome`.  The three factors are the
`(d_i / 5)^{x_i}` contributions of the observed types.
-/
def likelihood (g : Genome) : ℚ :=
  (6 : ℚ) * ((occ g readAAA : ℚ) / 5) * ((occ g readAAB : ℚ) / 5) *
    ((occ g readBAA : ℚ) / 5)

/-- `AAA` occurs once in the truth. -/
theorem occ_truth_AAA : occ truth readAAA = 1 := by decide

/-- `AAB` occurs once in the truth. -/
theorem occ_truth_AAB : occ truth readAAB = 1 := by decide

/-- `BAA` occurs once in the truth. -/
theorem occ_truth_BAA : occ truth readBAA = 1 := by decide

/-- `AAA` occurs twice in the competitor. -/
theorem occ_competitor_AAA : occ competitor readAAA = 2 := by decide

/-- `AAB` occurs once in the competitor. -/
theorem occ_competitor_AAB : occ competitor readAAB = 1 := by decide

/-- `BAA` occurs once in the competitor. -/
theorem occ_competitor_BAA : occ competitor readBAA = 1 := by decide

/-- Exact likelihood of the observed reads under the truth. -/
theorem likelihood_truth : likelihood truth = 6 / 125 := by
  unfold likelihood
  rw [occ_truth_AAA, occ_truth_AAB, occ_truth_BAA]
  norm_num

/-- Exact likelihood of the observed reads under the competitor. -/
theorem likelihood_competitor : likelihood competitor = 12 / 125 := by
  unfold likelihood
  rw [occ_competitor_AAA, occ_competitor_AAB, occ_competitor_BAA]
  norm_num

/-- The exact likelihoods stand in ratio `2`, matching the issue certificate. -/
theorem likelihood_ratio : likelihood competitor / likelihood truth = 2 := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

/-- Fixed-length maximum-likelihood predicate: the truth is at least as likely
as every candidate circular genome of the same length `5`. -/
def IsMaximumLikelihoodFixedLength (g : Genome) : Prop :=
  ∀ candidate : Genome, likelihood candidate ≤ likelihood g

/-- The competitor strictly beats the truth, so the truth is not an exact
maximum-likelihood maximizer among same-length candidates. -/
theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihoodFixedLength truth := by
  intro h
  have hcomp := h competitor
  rw [likelihood_truth, likelihood_competitor] at hcomp
  norm_num at hcomp

/-! ## Source-faithful `I_s` for the instance

The hypothesis side is the shared source-faithful predicate itself, at full
strength. -/

/-- The realized read start positions `0, 1, 4`.  These are the latent
placements; the observed read multiset `{AAA, AAB, BAA}` is recoverable from them
by `realized_reads` below. -/
def readStarts : Finset (Fin 5) := {0, 1, 4}

/-- The realized length-`3` reads at starts `0, 1, 4` return exactly the three
observed read types, one each.  This ties the latent placements used on the
hypothesis side to the read multiset consumed by `likelihood`. -/
theorem realized_reads :
    window truth 0 = readAAA ∧ window truth 1 = readAAB ∧ window truth 4 = readBAA :=
  ⟨by decide, by decide, by decide⟩

/-- Coverage: the realized length-`3` reads at starts `0, 1, 4` cover all five
circular positions of the truth.  This is the first clause of `I_s`, stated with
the shared `Covers` predicate. -/
theorem truth_covers : SourceFaithfulIs.Covers truthGenome 3 readStarts := by
  unfold SourceFaithfulIs.Covers
  decide

/-- **Full source-faithful `I_s` membership**, not a hand-listed certificate:
all three clauses of Shomorony et al. Eq. (1) hold for the truth under the
realized read placements.  Clause 2 is quantified over every admissible repeat
length and every ordered triple of selected starts, and clause 3 over every pair
of maximal repeats and every ordering of their four selected starts. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts := by
  unfold SourceFaithfulIs.InformationFeasible
  decide

/-! ## Main finite theorem -/

/--
Kernel-checked finite counterexample to the fixed-length exact-multinomial
variant: the concrete instance satisfies the *full* source-faithful
information-feasibility condition `R ∈ I_s`, yet the true sequence is not an
exact maximum-likelihood assembly among circular candidates of the same length.

This theorem is deliberately limited to the fixed-length exact multinomial
variant and to this finite instance.  It does not settle unrestricted-length
exact ML, the separable/binomial approximation, the Section 6.2 flow feasible
set, or the source-ambiguous Shomorony et al. open question.
-/
theorem fixed_length_exact_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts ∧
      ¬ IsMaximumLikelihoodFixedLength truth :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

end AssemblyP1.FixedLengthExactCounterexample
