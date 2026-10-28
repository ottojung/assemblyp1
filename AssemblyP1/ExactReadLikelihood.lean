import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.FiniteReadRecoveryGenome

/-!
# Shared exact oriented circular-read likelihood

This defines candidate-intrinsic circular read probabilities once, via the
source-faithful Genome.window, including wraparound and L > genome length.
The exact unordered multinomial likelihood includes the observation-only
factorial correction. The fixed-reference-length product-binomial score is
a separate surrogate, never an exact ML claim.
-/

namespace AssemblyP1.ExactReadLikelihood

open AssemblyP1.SourceFaithfulIs
open Finset

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Circular multiplicity of an oriented read, counting start positions. -/
def readCount (S : Genome α) (L : ℕ) (w : Fin L → α) : ℕ :=
  (Finset.univ.filter (fun t : Fin S.len => S.window L t = w)).card

/-- Exact probability of one oriented read under a uniform circular start. -/
def readMass (S : Genome α) (L : ℕ) (w : Fin L → α) : ℚ :=
  (readCount S L w : ℚ) / (S.len : ℚ)

/-- Probability of a given ordered tuple of independent reads. -/
def iidLikelihood (S : Genome α) (L n : ℕ)
    (reads : Fin n → (Fin L → α)) : ℚ :=
  ∏ i : Fin n, readMass S L (reads i)

/-- Observed multiplicity of a read type, not its genome multiplicity. -/
def observedCount {L n : ℕ} (reads : Fin n → (Fin L → α))
    (w : Fin L → α) : ℕ :=
  ∑ i : Fin n, if reads i = w then 1 else 0

/-- Multinomial factor for the unordered observed read multiset. -/
def multinomialFactor (L n : ℕ) (reads : Fin n → (Fin L → α)) : ℚ :=
  (Nat.factorial n : ℚ) /
    ∏ w : Fin L → α, (Nat.factorial (observedCount reads w) : ℚ)

/-- Exact candidate-intrinsic multinomial likelihood. -/
def exactMultinomialLikelihood (S : Genome α) (L n : ℕ)
    (reads : Fin n → (Fin L → α)) : ℚ :=
  multinomialFactor L n reads * iidLikelihood S L n reads

/-- Fixed-reference-length binomial marginal; zero-count read types
still contribute their complement factor. Distinct from exact ML. -/
def binomialMarginal (S : Genome α) (L n N : ℕ)
    (reads : Fin n → (Fin L → α)) (w : Fin L → α) : ℚ :=
  (Nat.choose n (observedCount reads w) : ℚ) *
    ((readCount S L w : ℚ) / (N : ℚ)) ^ observedCount reads w *
    (1 - (readCount S L w : ℚ) / (N : ℚ)) ^ (n - observedCount reads w)

/-- Product of read-type binomial marginals with external length N.
Every read type is included, even if it was not observed. -/
def productBinomialLikelihood (S : Genome α) (L n N : ℕ)
    (reads : Fin n → (Fin L → α)) : ℚ :=
  ∏ w : Fin L → α, binomialMarginal S L n N reads w

omit [Fintype α] in
/-- This rational read mass agrees with the real iid genome-read PMF. -/
theorem readMass_eq_circularReadPMF (S : Genome α) (L : ℕ)
    (w : Fin L → α) :
    (readMass S L w : ℝ) =
      FiniteReadRecoveryGenome.circularReadPMF S L w := by
  rw [readMass, FiniteReadRecoveryGenome.circularReadPMF_eq_count]
  simp only [Rat.cast_div, Rat.cast_natCast, readCount]

end AssemblyP1.ExactReadLikelihood
