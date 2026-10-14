import AssemblyP1.PopulationUniqueness
import AssemblyP1.FiniteReadRecoveryGenome

/-!
# From primitive-P2 population uniqueness to strict finite-read separation

This module connects the actual \`SourceFaithfulIs.Genome.window\` uniform
circular-start read distribution with the kernel-checked primitive-P2
population-uniqueness theorem \`Issue94Complete.population_unique_ML\`.

The result is a direct structural criterion for finite-sample ML reliability:
against every primitive P2-admissible candidate NOT equivalent to the truth
by rotation, the read-distribution Bhattacharyya affinity is strictly
smaller than one.

The family of competitors must still be finite to obtain a UNIFORM
exponential rate. The model here is strictly oriented and error-free.
-/

namespace AssemblyP1.FiniteReadRecoveryP2Bridge

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteReadRecovery
open AssemblyP1.FiniteReadRecoveryGenome
open AssemblyP1.PopulationUniqueness
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTEulerian

open scoped Classical

variable {α : Type} [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- The uniform-start read law used in the finite-sample theorem is
DEFINITIONALLY the normalized spectrum in the population theorem;
both count each cyclic starting position and divide by the genome length. -/
theorem circularReadPMF_eq_popSpectrum (S : Genome α) (L : ℕ) :
    circularReadPMF S L = popSpectrum L S.len_pos S.sym := by
  funext w
  rw [circularReadPMF_eq_count]
  rfl

/-- Equality of actual circular read laws implies rotation equivalence of
primitive-P2 truth and any primitive-P2 admissible candidate, even if their
original genome lengths differ. This is the finite-sample-relevant form
of the completed population ML uniqueness theorem. -/
theorem equal_read_laws_imply_rotation
    (S D : Genome α) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hPevzner : EulerianCycleObstruction (α := α) L)
    (hAdmD : AdmClass L D.len_pos D.sym)
    (hLaw : circularReadPMF S L = circularReadPMF D L) :
    ∃ hSD : S.len = D.len, RotEquiv S.len_pos (hSD ▸ D.sym) S.sym := by
  have hPop : popSpectrum L S.len_pos S.sym =
      popSpectrum L D.len_pos D.sym := by
    rw [← circularReadPMF_eq_popSpectrum S L,
      ← circularReadPMF_eq_popSpectrum D L]
    exact hLaw
  have hTie : PopLogLik (popSpectrum L S.len_pos S.sym)
      (popSpectrum L D.len_pos D.sym) =
        PopLogLik (popSpectrum L S.len_pos S.sym)
          (popSpectrum L S.len_pos S.sym) := by
    rw [← hPop]
  exact (population_unique_ML_up_to_rotation L S.len_pos hL S.sym hPrimS hP2S hPevzner).2
    D.len D.len_pos D.sym hAdmD hTie

/-- The central statistical consequence of primitive-P2 structural
identifiability: an admissible candidate which is NOT a rotation of the
truth has strictly smaller-than-one Hellinger affinity of its oriented
read distribution with the truth.  No prior, feasibility oracle, or
unproved distinguishability premise is used. -/
theorem hellinger_lt_one_of_primitiveP2_not_rotation
    (S D : Genome α) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hPevzner : EulerianCycleObstruction (α := α) L)
    (hAdmD : AdmClass L D.len_pos D.sym)
    (hNotRot : ¬ ∃ hSD : S.len = D.len,
      RotEquiv S.len_pos (hSD ▸ D.sym) S.sym) :
    hellinger (circularReadPMF S L) (circularReadPMF D L) < 1 := by
  apply (hellinger_lt_one_iff_ne (circularReadPMF S L)
      (circularReadPMF D L)
      (circularReadPMF_isPmf S L)
      (circularReadPMF_isPmf D L)).2
  intro hLaw
  exact hNotRot (equal_read_laws_imply_rotation S D L hL
    hPrimS hP2S hPevzner hAdmD hLaw)


/-- On any FINITE set of primitive-P2 admissible nonrotational competitor
genomes, primitive-P2 structural uniqueness forces a *uniform* Hellinger
affinity gap: some ρ_max with 0 ≤ ρ_max < 1 bounds every competitor.
The empty candidate family is handled using ρ_max = 0. -/
theorem finite_primitiveP2_family_affinity_gap
    (S : Genome α) (C : Finset (Genome α)) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hPevzner : EulerianCycleObstruction (α := α) L)
    (hAdm : ∀ D ∈ C, AdmClass L D.len_pos D.sym)
    (hNotRot : ∀ D ∈ C, ¬ ∃ hSD : S.len = D.len,
      RotEquiv S.len_pos (hSD ▸ D.sym) S.sym) :
    ∃ ρ_max : ℝ, 0 ≤ ρ_max ∧ ρ_max < 1 ∧
      ∀ D ∈ C,
        hellinger (circularReadPMF S L) (circularReadPMF D L) ≤ ρ_max := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image C
        (fun E => hellinger (circularReadPMF S L) (circularReadPMF E L)) hC
    refine ⟨hellinger (circularReadPMF S L) (circularReadPMF D L), ?_, ?_, ?_⟩
    · unfold hellinger
      apply Finset.sum_nonneg
      intro w _
      exact Real.sqrt_nonneg _
    · exact hellinger_lt_one_of_primitiveP2_not_rotation S D L
        hL hPrimS hP2S hPevzner (hAdm D hD) (hNotRot D hD)
    · intro E hE
      exact hmax E hE
  · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    refine ⟨0, le_refl _, by norm_num, ?_⟩
    intro D hD
    simp [hempty] at hD

/-- **Finite-sample ML recovery under the structural primitive-P2
hypothesis.** For any finite collection C of admissible competitors none
rotation-equivalent to the true genome S, there is an N such that after
n ≥ N iid oriented circular reads, the probability that ANY competitor
ties or exceeds S's exact likelihood is at most δ. This quantitative
result does not condition on truth-dependent information feasibility. -/
theorem finite_primitiveP2_family_confidence
    (S : Genome α) (C : Finset (Genome α)) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hPevzner : EulerianCycleObstruction (α := α) L)
    (hAdm : ∀ D ∈ C, AdmClass L D.len_pos D.sym)
    (hNotRot : ∀ D ∈ C, ¬ ∃ hSD : S.len = D.len,
      RotEquiv S.len_pos (hSD ▸ D.sym) S.sym)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      eventProb (circularReadPMF S L) n
        (wrongEvent (circularReadPMF S L) (readLawFamily C L) n) ≤ δ := by
  obtain ⟨ρ_max, hρnn, hρlt, hρ⟩ :=
    finite_primitiveP2_family_affinity_gap S C L hL hPrimS hP2S
      hPevzner hAdm hNotRot
  exact circular_exists_n_for_confidence S C L ρ_max
    hρ hρnn hρlt δ hδ

end AssemblyP1.FiniteReadRecoveryP2Bridge
