import AssemblyP1.Issue94ConcreteAntiderivative
import AssemblyP1.Issue94LongWindowSplit

/-!
# Issue 94: completed population-uniqueness endpoint

This module closes the remaining long-window input with the concrete component
antiderivative construction and combines it with the already-proved short-window
theorem.
-/

namespace AssemblyP1.Issue94Complete

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationUniqueness
open AssemblyP1.Issue94ConcreteAntiderivative
open AssemblyP1.Issue94Split

variable {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}

/-- The complete population maximum-likelihood uniqueness theorem obtained from
the concrete component-antiderivative proof of the long range and the existing
short-window theorem. -/
theorem population_unique_ML
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) := by
  apply population_unique_ML_of_p2LongUnique L hG hL S hPrimS hP2S
  exact concrete_p2LongUnique (α := α) (by omega)

#print axioms AssemblyP1.Issue94Complete.population_unique_ML

end AssemblyP1.Issue94Complete
