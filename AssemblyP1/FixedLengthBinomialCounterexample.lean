import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Fixed-length binomial-approximation counterexample (issue #32)

This file kernel-checks the concrete, same-length witness recorded in
`docs/fixed-length-binomial-counterexample.md` against the literal
Medvedev–Brudno §6.1 **product-of-binomial-marginals** approximation.

Scope.  The candidate universe is the set of circular genomes of length
`G = 5` over a fixed four-symbol alphabet, and the objective is the product over
the DNA read-type space of the individual binomial marginals

`Binom(n, x_i) (d_i / N)^{x_i} (1 - d_i / N)^{n - x_i}`

with the *fixed external* genome length `N = 5`, total read count `n = 3`,
observed read-type counts `x_i`, and candidate read-type multiplicities `d_i`.
Crucially, unlike the exact multinomial of `FixedLengthExactCounterexample`,
read types with `x_i = 0` still contribute their `(1 - d_i / N)^n` factor.  The
example is chosen so that this factor is what distinguishes the two candidates.

This file does **not** claim anything about unrestricted-length exact ML, the
Section 6.2 flow feasible set, or which of those the source paper intended.

Instance (issue #32):

* true circular genome `truth = AAACC` (length `G = 5`);
* read length `L = 3`, realized starts `0, 1, 4`;
* observed read multiset `{AAA, AAC, CAA}`, each with multiplicity one;
* same-length competitor `competitor = AAAAC`.

The observed types occur once each in `truth`.  In `competitor`, `AAA` occurs
twice and `AAC`, `CAA` once each; additionally `competitor` contains the
unobserved type `ACA`, whose zero-count marginal `(1 - 1/5)^3` is *retained*
under the literal approximation.  The exact product-of-binomial-marginals ratio
is `1125/512 > 1`, so the competitor is strictly more likely than the truth:
the truth is not a fixed-length maximum-likelihood maximizer.

`truth_information_feasible` below is a kernel-checked proof of **full** `I_s`
membership, that is `SourceFaithfulIs.InformationFeasible truthGenome 3
readStarts`, discharged by `decide`.  It is the same hypothesis statement as in
`FixedLengthExactCounterexample` applied to the `AAABB` witness with `B`
relabeled to `C`, so the two instances share one source-faithful hypothesis
predicate rather than two local proxies.  No repeat is enumerated by hand.
-/

namespace AssemblyP1.FixedLengthBinomialCounterexample

open SourceFaithfulIs

/-- Four-symbol alphabet for the fixed-length candidate universe; the ordinary
DNA alphabet, with `A` and `C` the two symbols used by the issue's witness. -/
inductive Base where
  | A
  | B
  | C
  | G
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.B, Base.C, Base.G}
  complete := by intro x; cases x <;> simp

/-- A circular genome of length `5`. -/
abbrev Genome := Fin 5 → Base

/-- The `i`-th symbol of a circular genome of length `5`. -/
def cyc (g : Genome) (i : Nat) : Base :=
  g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The length-`3` circular window of `g` beginning at start `r`, i.e. the
read type obtained by a length-`3` read placed at `r`. -/
def window (g : Genome) (r : Fin 5) : Fin 3 → Base :=
  fun d => cyc g (r.val + d.val)

/-- Number of circular start positions of `g` whose length-`3` window is `w`. -/
def occ (g : Genome) (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => window g r = w)).card

/-- Read type `AAA`. -/
def readAAA : Fin 3 → Base := fun _ => Base.A

/-- Read type `AAC`. -/
def readAAC : Fin 3 → Base := ![Base.A, Base.A, Base.C]

/-- Read type `CAA`. -/
def readCAA : Fin 3 → Base := ![Base.C, Base.A, Base.A]

/-- Read type `ACC` (unobserved, has positive multiplicity in the truth). -/
def readACC : Fin 3 → Base := ![Base.A, Base.C, Base.C]

/-- Read type `CCA` (unobserved, has positive multiplicity in the truth). -/
def readCCA : Fin 3 → Base := ![Base.C, Base.C, Base.A]

/-- Read type `ACA` (unobserved, has positive multiplicity in the competitor). -/
def readACA : Fin 3 → Base := ![Base.A, Base.C, Base.A]

/-- The true circular genome `S = AAACC`, as a shared-layer circular genome. -/
/- This genome is a reducible abbreviation, not an opaque `def`, so that the
   `Fin`-indexed numerals and the `Decidable` instances of the shared layer are
   found by instance search when the finite `I_s` membership is decided. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.C, Base.C]

/-- The same-length competitor `D = AAAAC`, as a shared-layer circular genome. -/
abbrev competitorGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.A, Base.C]

/-- The true circular genome `S = AAACC`. -/
def truth : Genome := ![Base.A, Base.A, Base.A, Base.C, Base.C]

/-- The same-length competitor `D = AAAAC`. -/
def competitor : Genome := ![Base.A, Base.A, Base.A, Base.A, Base.C]

/-- The truth of the candidate universe and of the shared source-faithful layer
are the same circular sequence. -/
theorem truth_eq_genome : truth = truthGenome.sym := rfl

/-- Likewise for the competitor. -/
theorem competitor_eq_genome : competitor = competitorGenome.sym := rfl

/-- The four-symbol read-type space is fixed and finite; every factor outside
this six-element set is `1` for both candidates below because both its observed
count and its candidate multiplicity vanish there.  The six types listed are
exactly the observed types together with the positive-multiplicity types of
`truth` and `competitor`. -/
def relevant : Finset (Fin 3 → Base) :=
  {readAAA, readAAC, readCAA, readACC, readCCA, readACA}

/-! ## Literal Section 6.1 product-of-binomial-marginals objective -/

/-- Observed count `x_w` of read type `w`: the reads `AAA, AAC, CAA` were each
observed once and nothing else was observed. -/
def obsCount (w : Fin 3 → Base) : Nat :=
  (if w = readAAA then 1 else 0) + (if w = readAAC then 1 else 0) +
    (if w = readCAA then 1 else 0)

/-- The literal binomial marginal for read type `w` under candidate `g`, with
the fixed external length `N = 5` and total read count `n = 3`:
`Binom(3, x_w) (d_w / 5)^{x_w} (1 - d_w / 5)^{3 - x_w}`, where `d_w = occ g w`.
Zero observed counts thus retain the factor `(1 - d_w / 5)^3`. -/
def marginal (g : Genome) (w : Fin 3 → Base) : ℚ :=
  (Nat.choose 3 (obsCount w) : ℚ) * ((occ g w : ℚ) / 5) ^ (obsCount w) *
    (1 - (occ g w : ℚ) / 5) ^ (3 - obsCount w)

/-- The Section 6.1 approximation: the product of the individual binomial
marginals over the whole DNA read-type space. -/
def likelihood (g : Genome) : ℚ :=
  ∏ w : Fin 3 → Base, marginal g w

/-! ## Reduction of the full type space to the six relevant types -/

/-- Every read type outside `relevant` has observed count zero. -/
theorem obsCount_eq_zero_of_not_relevant :
    ∀ w : Fin 3 → Base, w ∉ relevant → obsCount w = 0 := by decide

/-- Every read type outside `relevant` has multiplicity zero in the truth. -/
theorem occ_truth_eq_zero_of_not_relevant :
    ∀ w : Fin 3 → Base, w ∉ relevant → occ truth w = 0 := by decide

/-- Every read type outside `relevant` has multiplicity zero in the competitor. -/
theorem occ_competitor_eq_zero_of_not_relevant :
    ∀ w : Fin 3 → Base, w ∉ relevant → occ competitor w = 0 := by decide

/-- A type with `x_w = 0` and `d_w = 0` contributes the factor `Binom(3,0) *
(0/5)^0 * (1-0)^3 = 1` to the product. -/
theorem marginal_eq_one_of_occ_eq_zero (g : Genome) (w : Fin 3 → Base)
    (hocc : occ g w = 0) (hobs : obsCount w = 0) : marginal g w = 1 := by
  simp [marginal, hocc, hobs]

/-- For a candidate all of whose support lies in `relevant`, the full product
of binomial marginals equals the product over `relevant`. -/
theorem likelihood_eq_relevant_prod (g : Genome)
    (h : ∀ w : Fin 3 → Base, w ∉ relevant → occ g w = 0) :
    likelihood g = ∏ w ∈ relevant, marginal g w := by
  unfold likelihood
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro x _; exact Finset.mem_univ x)
    (by
      intro w _ hw
      exact marginal_eq_one_of_occ_eq_zero g w (h w hw)
        (obsCount_eq_zero_of_not_relevant w hw))).symm

/-- The product over the six-element `relevant` set written as an explicit
nested product. -/
theorem relevant_prod_eq (f : (Fin 3 → Base) → ℚ) :
    ∏ w ∈ relevant, f w =
      f readAAA * (f readAAC * (f readCAA * (f readACC *
        (f readCCA * f readACA)))) := by
  unfold relevant
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

/-! ## Exact arithmetic -/

/-- The observed count `x_w` of the six relevant types; all other types have
count `0` by `obsCount_eq_zero_of_not_relevant`. -/
theorem obsCount_AAA : obsCount readAAA = 1 := by decide

theorem obsCount_AAC : obsCount readAAC = 1 := by decide

theorem obsCount_CAA : obsCount readCAA = 1 := by decide

theorem obsCount_ACC : obsCount readACC = 0 := by decide

theorem obsCount_CCA : obsCount readCCA = 0 := by decide

theorem obsCount_ACA : obsCount readACA = 0 := by decide

/-- `AAA` occurs once in the truth. -/
theorem occ_truth_AAA : occ truth readAAA = 1 := by decide

/-- `AAC` occurs once in the truth. -/
theorem occ_truth_AAC : occ truth readAAC = 1 := by decide

/-- `CAA` occurs once in the truth. -/
theorem occ_truth_CAA : occ truth readCAA = 1 := by decide

/-- `ACC` occurs once in the truth. -/
theorem occ_truth_ACC : occ truth readACC = 1 := by decide

/-- `CCA` occurs once in the truth. -/
theorem occ_truth_CCA : occ truth readCCA = 1 := by decide

/-- `ACA` never occurs in the truth. -/
theorem occ_truth_ACA : occ truth readACA = 0 := by decide

/-- `AAA` occurs twice in the competitor. -/
theorem occ_competitor_AAA : occ competitor readAAA = 2 := by decide

/-- `AAC` occurs once in the competitor. -/
theorem occ_competitor_AAC : occ competitor readAAC = 1 := by decide

/-- `CAA` occurs once in the competitor. -/
theorem occ_competitor_CAA : occ competitor readCAA = 1 := by decide

/-- `ACC` never occurs in the competitor. -/
theorem occ_competitor_ACC : occ competitor readACC = 0 := by decide

/-- `CCA` never occurs in the competitor. -/
theorem occ_competitor_CCA : occ competitor readCCA = 0 := by decide

/-- `ACA` occurs once in the competitor. -/
theorem occ_competitor_ACA : occ competitor readACA = 1 := by decide

/-- Exact product-of-binomial-marginals likelihood of the observed reads under
the truth, including the zero-count factors for `ACC` and `CCA`. -/
theorem likelihood_truth : likelihood truth = 452984832 / 30517578125 := by
  rw [likelihood_eq_relevant_prod truth occ_truth_eq_zero_of_not_relevant,
    relevant_prod_eq]
  simp only [marginal]
  rw [obsCount_AAA, obsCount_AAC, obsCount_CAA, obsCount_ACC, obsCount_CCA,
    obsCount_ACA, occ_truth_AAA, occ_truth_AAC, occ_truth_CAA, occ_truth_ACC,
    occ_truth_CCA, occ_truth_ACA]
  norm_num

/-- Exact product-of-binomial-marginals likelihood of the observed reads under
the competitor, including the zero-count factor for `ACA`. -/
theorem likelihood_competitor : likelihood competitor = 7962624 / 244140625 := by
  rw [likelihood_eq_relevant_prod competitor occ_competitor_eq_zero_of_not_relevant,
    relevant_prod_eq]
  simp only [marginal]
  rw [obsCount_AAA, obsCount_AAC, obsCount_CAA, obsCount_ACC, obsCount_CCA,
    obsCount_ACA, occ_competitor_AAA, occ_competitor_AAC, occ_competitor_CAA,
    occ_competitor_ACC, occ_competitor_CCA, occ_competitor_ACA]
  norm_num

/-- The exact likelihoods stand in ratio `1125/512 > 1`, matching the issue
certificate.  This is the point at which the retained zero-count factor
`(1 - 1/5)^3` changes the exact-multinomial ratio of `2` into `1125/512`. -/
theorem likelihood_ratio :
    likelihood competitor / likelihood truth = 1125 / 512 := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

/-- Fixed-length maximum-likelihood predicate: the truth is at least as likely
as every candidate circular genome of the same length `5`. -/
def IsMaximumLikelihoodFixedLength (g : Genome) : Prop :=
  ∀ candidate : Genome, likelihood candidate ≤ likelihood g

/-- The competitor strictly beats the truth, so the truth is not a
product-of-binomial-marginals maximum-likelihood maximizer even among
same-length candidates. -/
theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihoodFixedLength truth := by
  intro h
  have hcomp := h competitor
  rw [likelihood_truth, likelihood_competitor] at hcomp
  norm_num at hcomp

/-! ## Source-faithful `I_s` for the instance -/

/-- The realized read start positions `0, 1, 4`. -/
def readStarts : Finset (Fin 5) := {0, 1, 4}

/-- The realized length-`3` reads at starts `0, 1, 4` return exactly the three
observed read types, one each.  This ties the latent placements used on the
hypothesis side to the read multiset consumed by `likelihood`. -/
theorem realized_reads :
    window truth 0 = readAAA ∧ window truth 1 = readAAC ∧ window truth 4 = readCAA :=
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
Kernel-checked finite counterexample to the fixed-length literal
Medvedev–Brudno §6.1 product-of-binomial-marginals variant: the concrete
instance satisfies the *full* source-faithful information-feasibility condition
`R ∈ I_s`, yet the true sequence is not a maximum-likelihood maximizer
among circular candidates of the same length.

This theorem is deliberately limited to the fixed-length
product-of-binomial-marginals variant and to this finite instance.  It does not
settle unrestricted-length exact ML, the Section 6.2 flow feasible set, or the
source-ambiguous Shomorony et al. open question. -/
theorem fixed_length_binomial_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts /\
      ¬ IsMaximumLikelihoodFixedLength truth :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

end AssemblyP1.FixedLengthBinomialCounterexample
