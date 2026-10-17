import AssemblyP1.SourceFaithfulIs
import AssemblyP1.FiniteReadRecovery

/-!
# Circular-genome read PMF interface for finite-sample recovery

This module uses the actual SourceFaithfulIs.Genome.window definition,
including wraparound windows for all read lengths, to construct the law
of the oriented read obtained at a uniformly random genomic start.

The primitive-P2 distribution-identifiability and orbit adapters remain
separate obligations; no binomial surrogate is involved here.
-/

namespace AssemblyP1.FiniteReadRecoveryGenome

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteReadRecovery
open Finset
open scoped Classical

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Uniform-start oriented circular read law. Every start is counted,
including multiplicities when different positions spell the same word.
The cyclic window is defined for all read lengths, including L > G. -/
noncomputable def circularReadPMF (S : Genome α) (L : ℕ) : (Fin L → α) → ℝ :=
  fun w => ∑ t : Fin S.len, if S.window L t = w then 1 / (S.len : ℝ) else 0

/-- A uniform start produces a normalized nonnegative read distribution
on the entire finite universe of oriented length-L read words. -/
theorem circularReadPMF_isPmf (S : Genome α) (L : ℕ) :
    IsPmf (circularReadPMF S L) := by
  classical
  constructor
  · intro w
    unfold circularReadPMF
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · positivity
    · exact le_refl _
  · unfold circularReadPMF
    rw [Finset.sum_comm]
    have hsum : (∑ t : Fin S.len, ∑ w : Fin L → α,
          if S.window L t = w then 1 / (S.len : ℝ) else 0)
        = ∑ t : Fin S.len, (1 / (S.len : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t _
      simp
    rw [hsum]
    have hpos : (S.len : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt S.len_pos)
    simp [Finset.sum_const, nsmul_eq_mul, hpos]

/- The genome-derived read probability is exactly the multiplicity of the
circular length-L word divided by the genome length.  Multiple positions
spelling the same word remain separate observations. -/
omit [Fintype α] in theorem circularReadPMF_eq_count (S : Genome α) (L : ℕ)
    (w : Fin L → α) :
    circularReadPMF S L w =
      ((Finset.univ.filter (fun t : Fin S.len => S.window L t = w)).card : ℝ) /
        (S.len : ℝ) := by
  classical
  unfold circularReadPMF
  simp [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The finite-sample pairwise ML bound, now instantiated with the actual
oriented circular read laws for two genomes (possibly of different lengths).
This does not assert identifiability of their read distributions. -/
theorem circular_pairwise_bound (S D : Genome α) (L n : ℕ) :
    eventProb (circularReadPMF S L) n
      (fun t => tupleLikelihood (circularReadPMF D L) n t ≥
        tupleLikelihood (circularReadPMF S L) n t)
      ≤ (hellinger (circularReadPMF S L) (circularReadPMF D L)) ^ n := by
  exact eventProb_pairwise _ _ n (circularReadPMF_isPmf S L)
    (circularReadPMF_isPmf D L)


/-- The (finite) set of oriented read laws induced by a chosen finite
collection of circular-genome candidates. Distinct genomes with an
identical read law are deduplicated at the distribution level. -/
noncomputable def readLawFamily (C : Finset (Genome α)) (L : ℕ) :
    Finset ((Fin L → α) → ℝ) :=
  C.image (fun D => circularReadPMF D L)

/-- Every genome-derived read law is a normalized pmf. -/
theorem readLawFamily_all_pmf (C : Finset (Genome α)) (L : ℕ) :
    ∀ q ∈ readLawFamily C L, IsPmf q := by
  classical
  intro q hq
  change q ∈ C.image (fun D => circularReadPMF D L) at hq
  obtain ⟨D, _, hDq⟩ := Finset.mem_image.mp hq
  rw [← hDq]
  exact circularReadPMF_isPmf D L

/-- A real genome-indexed finite-family exact-ML error bound: the probability
under the true circular read distribution of any alternative candidate
read law tying or beating the truth is bounded by the sum of pairwise
Hellinger affinities. No structural identifiability assumption is used
in this bound: laws equal to the true law simply have affinity one. -/
theorem circular_wrong_le_sum (S : Genome α)
    (C : Finset (Genome α)) (L n : ℕ) :
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L) (readLawFamily C L) n)
    ≤ ∑ q ∈ readLawFamily C L,
        (hellinger (circularReadPMF S L) q) ^ n := by
  have hp := circularReadPMF_isPmf S L
  calc
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L) (readLawFamily C L) n)
        ≤ ∑ q ∈ readLawFamily C L,
            eventProb (circularReadPMF S L) n
              (fun t => tupleLikelihood q n t ≥ tupleLikelihood (circularReadPMF S L) n t) :=
          eventProb_wrong_le_sum _ _ n hp
    _ ≤ ∑ q ∈ readLawFamily C L,
          (hellinger (circularReadPMF S L) q) ^ n := by
      apply Finset.sum_le_sum
      intro q hq
      exact eventProb_pairwise _ _ n hp (readLawFamily_all_pmf C L q hq)

/-- Given any uniform affinity bound for all genomes of a chosen finite
candidate set, the exact iid genome-read ML failure probability is bounded
by the number of distinct read laws times rho_max^n. If rho_max<1, this
is an exponential recovery guarantee. A population identifiability theorem
is needed to establish such rho_max<1 in a concrete structural class. -/
theorem circular_wrong_le_card (S : Genome α)
    (C : Finset (Genome α)) (L n : ℕ) (ρ_max : ℝ)
    (hρ : ∀ D ∈ C,
      hellinger (circularReadPMF S L) (circularReadPMF D L) ≤ ρ_max) :
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L) (readLawFamily C L) n)
    ≤ ((readLawFamily C L).card : ℝ) * ρ_max ^ n := by
  apply eventProb_wrong_le_card _ _ n ρ_max
    (circularReadPMF_isPmf S L) (readLawFamily_all_pmf C L)
  intro q hq
  change q ∈ C.image (fun D => circularReadPMF D L) at hq
  obtain ⟨D, hD, hDq⟩ := Finset.mem_image.mp hq
  rw [← hDq]
  exact hρ D hD

/-- Finite-genome conditional consistency: once every candidate genome's
oriented circular read law is known to have affinity at most rho_max<1
against the true genome's law, the probability of a wrong genome law tying
or beating the true likelihood tends to zero with read count. -/
theorem circular_wrong_tendsto_zero (S : Genome α)
    (C : Finset (Genome α)) (L : ℕ) (ρ_max : ℝ)
    (hρ : ∀ D ∈ C,
      hellinger (circularReadPMF S L) (circularReadPMF D L) ≤ ρ_max)
    (hρnn : 0 ≤ ρ_max) (hρlt : ρ_max < 1) :
    Filter.Tendsto
      (fun n => eventProb (circularReadPMF S L) n
        (wrongEvent (circularReadPMF S L) (readLawFamily C L) n))
      Filter.atTop (nhds 0) := by
  apply eventProb_wrong_tendsto_zero _ _ ρ_max
    (circularReadPMF_isPmf S L) (readLawFamily_all_pmf C L)
    (fun q hq => ?_) hρnn hρlt
  change q ∈ C.image (fun D => circularReadPMF D L) at hq
  obtain ⟨D, hD, hDq⟩ := Finset.mem_image.mp hq
  rw [← hDq]
  exact hρ D hD

/-- Under exactly the same explicit finite-family read-law separation
assumptions, any requested positive error tolerance is eventually met by
the exact iid ML competitor-ties-or-beats probability. -/
theorem circular_exists_n_for_confidence (S : Genome α)
    (C : Finset (Genome α)) (L : ℕ) (ρ_max : ℝ)
    (hρ : ∀ D ∈ C,
      hellinger (circularReadPMF S L) (circularReadPMF D L) ≤ ρ_max)
    (hρnn : 0 ≤ ρ_max) (hρlt : ρ_max < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      eventProb (circularReadPMF S L) n
        (wrongEvent (circularReadPMF S L) (readLawFamily C L) n) ≤ δ := by
  apply exists_n_for_confidence _ _ ρ_max
    (circularReadPMF_isPmf S L) (readLawFamily_all_pmf C L)
    (fun q hq => ?_) hρnn hρlt δ hδ
  change q ∈ C.image (fun D => circularReadPMF D L) at hq
  obtain ⟨D, hD, hDq⟩ := Finset.mem_image.mp hq
  rw [← hDq]
  exact hρ D hD

end AssemblyP1.FiniteReadRecoveryGenome
