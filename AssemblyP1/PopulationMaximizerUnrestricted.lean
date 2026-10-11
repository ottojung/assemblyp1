import AssemblyP1.PopulationUniqueness

/-! Direct oriented genome endpoints for Antonina #273.
    This file must be audited again against #274 support-inclusion repair
    before the theorem is called a fully source-faithful result. -/

namespace AssemblyP1.PopulationUniqueness

open AssemblyP1.PopulationGibbs
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Every true circular genome maximizes oriented population likelihood among
all other circular genomes, of possibly different positive lengths. This is
solely Gibbs' inequality, with no P2, primitivity or repeat hypothesis. -/
theorem population_maximizer_unrestricted (L G H : ℕ)
    (hG : 0 < G) (hH : 0 < H)
    (S : Fin G → α) (D : Fin H → α) :
    PopLogLik (popSpectrum L hG S) (popSpectrum L hH D)
      ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) := by
  exact popLogLik_le_self' (popSpectrum_isProb L hG S)
    (popSpectrum_isProb L hH D)

/-- A population tie is precisely normalized equality of the oriented read
distributions, not necessarily equality or rotation of the genome sequences. -/
theorem population_tie_iff_distribution_eq_unrestricted (L G H : ℕ)
    (hG : 0 < G) (hH : 0 < H)
    (S : Fin G → α) (D : Fin H → α) :
    PopLogLik (popSpectrum L hG S) (popSpectrum L hH D)
      = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)
      ↔ popSpectrum L hH D = popSpectrum L hG S := by
  exact popTie_iff (popSpectrum_isProb L hG S)
    (popSpectrum_isProb L hH D)

#print axioms AssemblyP1.PopulationUniqueness.population_maximizer_unrestricted
#print axioms AssemblyP1.PopulationUniqueness.population_tie_iff_distribution_eq_unrestricted



private def periodTwo : Fin 2 → Fin 2 := ![0, 1]
private def periodFour : Fin 4 → Fin 2 := ![0, 1, 0, 1]

theorem periodic_read_distribution_tie :
    popSpectrum 2 (by decide : 0 < 2) periodTwo
      = popSpectrum 2 (by decide : 0 < 4) periodFour := by
  have hcounts : ∀ w : Fin 2 → Fin 2,
      specCount (L := 2) (by decide : 0 < 4) periodFour w
      = 2 * specCount (L := 2) (by decide : 0 < 2) periodTwo w := by
    intro w
    fin_cases w <;> decide
  funext w
  have hw := hcounts w
  unfold popSpectrum popProb
  rw [hw]
  push_cast
  ring


/-- A concrete nonrotation tie: lengths two and four differ while their
normalized length-two spectra and population likelihoods coincide. -/
theorem periodic_population_likelihood_tie :
    PopLogLik (popSpectrum 2 (by decide : 0 < 2) periodTwo)
      (popSpectrum 2 (by decide : 0 < 4) periodFour)
    = PopLogLik (popSpectrum 2 (by decide : 0 < 2) periodTwo)
      (popSpectrum 2 (by decide : 0 < 2) periodTwo) := by
  exact (population_tie_iff_distribution_eq_unrestricted (α := Fin 2)
    2 2 4 (by decide) (by decide) periodTwo periodFour).mpr
      periodic_read_distribution_tie.symm

theorem periodic_lengths_differ : (2 : ℕ) ≠ 4 := by decide

#print axioms AssemblyP1.PopulationUniqueness.periodic_read_distribution_tie
#print axioms AssemblyP1.PopulationUniqueness.periodic_population_likelihood_tie

end AssemblyP1.PopulationUniqueness
