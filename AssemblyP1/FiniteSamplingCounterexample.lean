import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Finite-sampling counterexample

This file kernel-checks the project-level finite-sampling witness used to
motivate the population model.  It is deliberately self-contained: the claim
is about the concrete circular genomes `AABBC` and `AABC`, read length three,
and the observed reads `AAB` and `BCA`.

Both candidates are primitive and satisfy P1 (their circular length-two
windows are pairwise distinct), yet the shorter wrong candidate has exact
multinomial likelihood larger by `25/16`.  Thus intrinsic structural checks do
not remove finite-sample frequency fluctuation.

The hypothesis side uses the shared source-faithful layer
`AssemblyP1.SourceFaithfulIs` directly: `truth_information_feasible` is a
kernel-checked proof of full `I_s` membership, that is
`SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts`, discharged by
`decide` over every admissible repeat length and every selection of starts.  The
truth and the competitor are now both `SourceFaithfulIs.Genome Base`, so the
likelihood side ranges over genuinely different intrinsic lengths `5` and `4`
and refers to the same objects the hypothesis side does.
-/


namespace AssemblyP1.FiniteSamplingCounterexample

open SourceFaithfulIs

inductive Base where
  | A | B | C | G
  deriving DecidableEq, Inhabited, Repr

abbrev Read := Fin 3 → Base
abbrev Pair := Fin 2 → Base

/-- The truth `AABBC` and the competitor `AABC`, both in the shared
source-faithful circular representation, so that the hypothesis side and the
likelihood side refer to the same two objects and to candidate classes of
genuinely different intrinsic lengths `5` and `4`. -/
/- This genome is a reducible abbreviation, not an opaque `def`, so that the
   `Fin`-indexed numerals and the `Decidable` instances of the shared layer are
   found by instance search when the finite `I_s` membership is decided. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.B, Base.B, Base.C]

abbrev competitorGenome : SourceFaithfulIs.Genome Base where
  len := 4
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.B, Base.C]

def truthWindow2 (r : Fin 5) : Pair := fun d => truthGenome.cycl (r.val + d.val)
def competitorWindow2 (r : Fin 4) : Pair := fun d => competitorGenome.cycl (r.val + d.val)

def truthOcc (w : Read) : ℕ :=
  (Finset.univ.filter (fun r : Fin 5 => truthGenome.window 3 r = w)).card

def competitorOcc (w : Read) : ℕ :=
  (Finset.univ.filter (fun r : Fin 4 => competitorGenome.window 3 r = w)).card

/-- P1 at `L = 3`: no circular `(L-1) = 2`-mer occurs at two starts. -/
def TruthP1 : Prop := Function.Injective truthWindow2

def CompetitorP1 : Prop := Function.Injective competitorWindow2

theorem truth_p1 : TruthP1 := by unfold TruthP1 Function.Injective; decide

theorem competitor_p1 : CompetitorP1 := by unfold CompetitorP1 Function.Injective; decide

/-- Concrete primitivity certificate: no nonzero shift fixes the circular word. -/
def TruthPrimitive : Prop :=
  ∀ k : Fin 5, k ≠ 0 → ∃ i : Fin 5, truthGenome.cycl (i.val + k.val) ≠ truthGenome.sym i

/-- Concrete primitivity certificate for the length-four competitor. -/
def CompetitorPrimitive : Prop :=
  ∀ k : Fin 4, k ≠ 0 →
    ∃ i : Fin 4, competitorGenome.cycl (i.val + k.val) ≠ competitorGenome.sym i

theorem truth_primitive : TruthPrimitive := by unfold TruthPrimitive; decide

theorem competitor_primitive : CompetitorPrimitive := by
  unfold CompetitorPrimitive; decide

def readAAB : Read := ![Base.A, Base.A, Base.B]
def readBCA : Read := ![Base.B, Base.C, Base.A]

/-- Starts `0` and `3` in `AABBC` realize exactly the advertised reads. -/
theorem realized_reads : truthGenome.window 3 0 = readAAB ∧
    truthGenome.window 3 3 = readBCA := by
  decide

/-- The realized read start positions `0, 3`. -/
def readStarts : Finset (Fin 5) := {0, 3}

theorem truth_occ_AAB : truthOcc readAAB = 1 := by decide
theorem truth_occ_BCA : truthOcc readBCA = 1 := by decide
theorem competitor_occ_AAB : competitorOcc readAAB = 1 := by decide
theorem competitor_occ_BCA : competitorOcc readBCA = 1 := by decide

/-- Exact multinomial likelihood for the two observed, distinct read types.
The observation-only coefficient is `2! = 2`; candidate length is intrinsic. -/
def truthLikelihood : ℚ :=
  2 * ((truthOcc readAAB : ℚ) / 5) * ((truthOcc readBCA : ℚ) / 5)

def competitorLikelihood : ℚ :=
  2 * ((competitorOcc readAAB : ℚ) / 4) * ((competitorOcc readBCA : ℚ) / 4)

theorem truth_likelihood : truthLikelihood = 2 / 25 := by
  unfold truthLikelihood
  rw [truth_occ_AAB, truth_occ_BCA]
  norm_num

theorem competitor_likelihood : competitorLikelihood = 1 / 8 := by
  unfold competitorLikelihood
  rw [competitor_occ_AAB, competitor_occ_BCA]
  norm_num

/-- The wrong candidate is more likely by exactly `25/16`. -/
theorem likelihood_ratio : competitorLikelihood / truthLikelihood = 25 / 16 := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

theorem competitor_strictly_better : truthLikelihood < competitorLikelihood := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

/-! ## The source-faithful `I_s` hypothesis -/

/-- Every true position is covered by at least one realized length-three read.
This is the first clause of `I_s`, stated with the shared `Covers` predicate. -/
theorem truth_covers : SourceFaithfulIs.Covers truthGenome 3 readStarts := by
  unfold SourceFaithfulIs.Covers
  decide

/-- **Full source-faithful `I_s` membership**: all three clauses of Shomorony et
al. Eq. (1) hold for the truth under the realized read placements, checked by
finite computation over every admissible repeat length and every selection of
starts.

This is a real check, not a formality: `AABBC` has maximal length-`1` repeats at
starts `0, 1` and at `2, 3`, and every one of them is bridged by the realized
read that strictly straddles it.  There is no maximal length-`1` triple repeat,
because no symbol occurs three times, and the two maximal length-`1` repeats do
not interleave, so clause 3 holds vacuously. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts := by
  unfold SourceFaithfulIs.InformationFeasible
  decide

/-! ## Main finite theorem -/

/--
Kernel-checked finite-sampling witness: the realized reads satisfy **full**
source-faithful information feasibility `R ∈ I_s`; both genomes pass the
intrinsic P1/primitivity checks; the stated sample really comes from the truth;
and the wrong candidate nevertheless has strictly larger exact likelihood. -/
theorem finite_sampling_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 readStarts /\
      TruthP1 /\ CompetitorP1 /\ TruthPrimitive /\ CompetitorPrimitive /\
      (truthGenome.window 3 0 = readAAB /\ truthGenome.window 3 3 = readBCA) /\
      competitorLikelihood / truthLikelihood = 25 / 16 /\
      truthLikelihood < competitorLikelihood :=
  ⟨truth_information_feasible, truth_p1, competitor_p1, truth_primitive,
    competitor_primitive, realized_reads, likelihood_ratio,
    competitor_strictly_better⟩

end AssemblyP1.FiniteSamplingCounterexample
