import Mathlib

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

`SourceHypotheses` below records the concrete source-faithful certificate for
this instance: the realized reads cover the circular truth, and the three
length-1 `A` copies at starts `0, 1, 2` form a maximal triple repeat that is
all-bridged by the reads at starts `4, 0, 1`.  This instance has no interleaved
repeat pair; that finite check is recorded in
`docs/fixed-length-exact-counterexample.md` rather than formalized here, so
that no general repeat/interleaving infrastructure is introduced.
-/

namespace AssemblyP1.FixedLengthExactCounterexample

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

/-- The true circular genome `S = AAABB`. -/
def truth : Genome := ![Base.A, Base.A, Base.A, Base.B, Base.B]

/-- The same-length competitor `D = AAAAB`. -/
def competitor : Genome := ![Base.A, Base.A, Base.A, Base.A, Base.B]

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

/-! ## Source-faithful `I_s` certificate for the instance -/

/-- The realized read start positions `0, 1, 4`. -/
def readStarts : Finset (Fin 5) := {0, 1, 4}

/--
Coverage: the realized length-`3` reads at starts `0, 1, 4` cover all five
circular positions of the truth.
-/
def Covers : Prop :=
  ∀ p : Fin 5, ∃ r ∈ readStarts, ∃ d : Fin 3, p.val = (r.val + d.val) % 5

/-- The realized reads cover the truth. -/
theorem truth_covered : Covers := by
  unfold Covers
  decide

/--
Concrete source-faithful triple-repeat certificate: the length-`1` windows at
starts `0, 1, 2` are equal (`A`), the three-copy maximality condition holds
(the preceding symbols `B, A, A` are not all equal and the following symbols
`A, A, B` are not all equal), and every one of the three copies is bridged by a
realized read: the read at `4` bridges the copy at `0`, the read at `0` bridges
the copy at `1`, and the read at `1` bridges the copy at `2`.

Bridging a length-`1` copy at `t` by a length-`3` read starting at `r` means
`t = r + 1` (mod `5`), i.e. the copy is strictly interior to the read, as
required by the strict-extension source convention.
-/
def TripleRepeatAllBridged (g : Genome) : Prop :=
  g 0 = g 1 ∧ g 1 = g 2 ∧
  ¬(g 4 = g 0 ∧ g 0 = g 1) ∧
  ¬(g 1 = g 2 ∧ g 2 = g 3) ∧
  (∀ t : Fin 5, (t.val = 0 ∨ t.val = 1 ∨ t.val = 2) →
    ∃ r ∈ readStarts, (r.val + 1) % 5 = t.val)

/-- The concrete triple-repeat certificate holds for the truth. -/
theorem truth_triple_repeat_all_bridged : TripleRepeatAllBridged truth := by
  unfold TripleRepeatAllBridged
  decide

/--
The instance-specific part of the source-faithful `I_s` hypothesis that is
kernel-checked here: coverage plus the maximal, all-bridged length-`1` triple
repeat.  Absence of interleaved repeat pairs for this instance is recorded in
`docs/fixed-length-exact-counterexample.md`.
-/
def SourceHypotheses (g : Genome) : Prop :=
  Covers ∧ TripleRepeatAllBridged g

/-- The truth satisfies the kernel-checked `I_s` certificate. -/
theorem truth_source_hypotheses : SourceHypotheses truth :=
  ⟨truth_covered, truth_triple_repeat_all_bridged⟩

/-! ## Main finite theorem -/

/--
Kernel-checked finite counterexample to the fixed-length exact-multinomial
variant: the concrete instance satisfies the source-faithful coverage and
all-bridged-triple-repeat certificate, yet the true sequence is not an exact
maximum-likelihood assembly among circular candidates of the same length.

This theorem is deliberately limited to the fixed-length exact multinomial
variant and to this finite instance.  It does not settle unrestricted-length
exact ML, the separable/binomial approximation, the Section 6.2 flow feasible
set, or the source-ambiguous Shomorony et al. open question.
-/
theorem fixed_length_exact_counterexample :
    SourceHypotheses truth ∧ ¬ IsMaximumLikelihoodFixedLength truth :=
  ⟨truth_source_hypotheses, truth_not_maximum_likelihood⟩

end AssemblyP1.FixedLengthExactCounterexample
