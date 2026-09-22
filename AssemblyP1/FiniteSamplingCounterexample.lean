import Mathlib

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
-/

namespace AssemblyP1.FiniteSamplingCounterexample

inductive Base where
  | A | B | C | G
  deriving DecidableEq, Inhabited, Repr

abbrev TruthGenome := Fin 5 → Base
abbrev CompetitorGenome := Fin 4 → Base
abbrev Read := Fin 3 → Base
abbrev Pair := Fin 2 → Base

def truth : TruthGenome := ![Base.A, Base.A, Base.B, Base.B, Base.C]
def competitor : CompetitorGenome := ![Base.A, Base.A, Base.B, Base.C]

def readAAB : Read := ![Base.A, Base.A, Base.B]
def readBCA : Read := ![Base.B, Base.C, Base.A]

/-- Circular indexing for the truth. -/
def truthCyc (i : Nat) : Base := truth ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Circular indexing for the competitor. -/
def competitorCyc (i : Nat) : Base := competitor ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

def truthWindow3 (r : Fin 5) : Read := fun d => truthCyc (r.val + d.val)
def competitorWindow3 (r : Fin 4) : Read := fun d => competitorCyc (r.val + d.val)
def truthWindow2 (r : Fin 5) : Pair := fun d => truthCyc (r.val + d.val)
def competitorWindow2 (r : Fin 4) : Pair := fun d => competitorCyc (r.val + d.val)

def truthOcc (w : Read) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => truthWindow3 r = w)).card

def competitorOcc (w : Read) : Nat :=
  (Finset.univ.filter (fun r : Fin 4 => competitorWindow3 r = w)).card

/-- P1 at `L = 3`: no circular `(L-1) = 2`-mer occurs at two starts. -/
def TruthP1 : Prop := Function.Injective truthWindow2

def CompetitorP1 : Prop := Function.Injective competitorWindow2

theorem truth_p1 : TruthP1 := by decide

theorem competitor_p1 : CompetitorP1 := by decide

/-- Concrete primitivity certificate: no nonzero shift fixes the circular word. -/
def TruthPrimitive : Prop :=
  ∀ k : Fin 5, k ≠ 0 → ∃ i : Fin 5, truthCyc (i.val + k.val) ≠ truth i

/-- Concrete primitivity certificate for the length-four competitor. -/
def CompetitorPrimitive : Prop :=
  ∀ k : Fin 4, k ≠ 0 → ∃ i : Fin 4, competitorCyc (i.val + k.val) ≠ competitor i

theorem truth_primitive : TruthPrimitive := by decide

theorem competitor_primitive : CompetitorPrimitive := by decide

/-- Starts `0` and `3` in `AABBC` realize exactly the advertised reads. -/
theorem realized_reads : truthWindow3 0 = readAAB ∧ truthWindow3 3 = readBCA := by
  decide

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

/-- Kernel-checked finite-sampling witness: both genomes pass the intrinsic
P1/primitivity checks, the stated sample really comes from the truth, and the
wrong candidate nevertheless has strictly larger exact likelihood. -/
theorem finite_sampling_counterexample :
    TruthP1 ∧ CompetitorP1 ∧ TruthPrimitive ∧ CompetitorPrimitive ∧
      (truthWindow3 0 = readAAB ∧ truthWindow3 3 = readBCA) ∧
      competitorLikelihood / truthLikelihood = 25 / 16 ∧
      truthLikelihood < competitorLikelihood := by
  exact ⟨truth_p1, competitor_p1, truth_primitive, competitor_primitive,
    realized_reads, likelihood_ratio, competitor_strictly_better⟩

end AssemblyP1.FiniteSamplingCounterexample
