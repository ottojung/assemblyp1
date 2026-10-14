import AssemblyP1.Issue94Complete
import AssemblyP1.FiniteReadRecoveryP2Bridge

/-!
# Primitive-P2 structure gives finite-sample ML recovery with no new source axiom

This module directly invokes the kernel-checked and SOURCE-PREMISE-FREE
\`Issue94Complete.population_unique_ML\` theorem. Its companion
\`FiniteReadRecoveryP2Bridge\` proves the precise equality of oriented
uniform-circular-start read laws and population normalized spectra,
with a separate theorem spelling out the older Eulerian obstruction.

This is a uniform finite-CANDIDATE theorem, NOT a rate for all arbitrary
unbounded genome lengths; candidate admissibility and non-rotation are
hypotheses checked against the exact P2, primitive, oriented source model.
-/

namespace AssemblyP1.FiniteReadRecoveryP2Complete

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteReadRecovery
open AssemblyP1.FiniteReadRecoveryGenome
open AssemblyP1.FiniteReadRecoveryP2Bridge
open AssemblyP1.PopulationUniqueness
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity
open AssemblyP1.Issue94Complete

open scoped Classical

variable {α : Type} [DecidableEq α] [Fintype α]

/-- A P2/primitive-admissible competitor with an identical oriented read
law must be a rotation of the truth. The existing complete population
ML theorem supplies the structural uniqueness hypothesis automatically. -/
theorem equal_laws_imply_rotation_of_primitiveP2
    (S D : Genome α) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
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
  exact (population_unique_ML L S.len_pos hL S.sym hPrimS hP2S).2
    D.len D.len_pos D.sym hAdmD hTie

/-- **Completed structural-to-informational bridge.** For primitive
P2-admissible candidates, NOT being rotation-equivalent to the true
primitive P2 genome implies strict separation of their length-L read
distributions, hence Hellinger affinity strictly below one. -/
theorem hellinger_lt_one_of_primitiveP2_not_rotation
    (S D : Genome α) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hAdmD : AdmClass L D.len_pos D.sym)
    (hNotRot : ¬ ∃ hSD : S.len = D.len,
      RotEquiv S.len_pos (hSD ▸ D.sym) S.sym) :
    hellinger (circularReadPMF S L) (circularReadPMF D L) < 1 := by
  apply (hellinger_lt_one_iff_ne (circularReadPMF S L)
      (circularReadPMF D L)
      (circularReadPMF_isPmf S L)
      (circularReadPMF_isPmf D L)).2
  intro hLaw
  exact hNotRot (equal_laws_imply_rotation_of_primitiveP2 S D L
    hL hPrimS hP2S hAdmD hLaw)

/-- A finite collection of all admissible NON-ROTATIONAL competitors
has some strictly subunit uniform affinity upper bound. -/
theorem finite_primitiveP2_family_uniform_affinity
    (S : Genome α) (C : Finset (Genome α)) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
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
        hL hPrimS hP2S (hAdm D hD) (hNotRot D hD)
    · intro E hE
      exact hmax E hE
  · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    refine ⟨0, le_refl _, by norm_num, ?_⟩
    intro D hD
    simp [hempty] at hD

/-- **The completed finite-sample conclusion:** primitive-P2 structure
plus a finite candidate family imply that exact maximum likelihood selects
the true genome's rotation class with probability tending to 1. For
every error tolerance δ>0 the wrong-class-ties-or-beats probability is
at most δ for all sufficiently large iid sample sizes. The data-only
observation model is used directly; no truth-feasibility oracle. -/
theorem finite_primitiveP2_ML_confidence
    (S : Genome α) (C : Finset (Genome α)) (L : ℕ) (hL : 1 < L)
    (hPrimS : IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (hAdm : ∀ D ∈ C, AdmClass L D.len_pos D.sym)
    (hNotRot : ∀ D ∈ C, ¬ ∃ hSD : S.len = D.len,
      RotEquiv S.len_pos (hSD ▸ D.sym) S.sym)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      eventProb (circularReadPMF S L) n
        (wrongEvent (circularReadPMF S L) (readLawFamily C L) n) ≤ δ := by
  obtain ⟨ρ_max, hρnn, hρlt, hρ⟩ :=
    finite_primitiveP2_family_uniform_affinity S C L hL hPrimS
      hP2S hAdm hNotRot
  exact circular_exists_n_for_confidence S C L ρ_max
    hρ hρnn hρlt δ hδ

end AssemblyP1.FiniteReadRecoveryP2Complete
