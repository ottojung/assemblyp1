import Mathlib

namespace AssemblyP1

/--
An intentionally abstract shell around a genome-assembly statistical model.

This is scaffolding, not yet the Shomorony–Kim–Courtade–Tse / Medvedev–Brudno
model. In particular, `bridgingConditions`, `likelihood`, and genome equivalence
must eventually be replaced or instantiated by definitions justified directly
from the source papers.
-/
structure AssemblyModel where
  Genome : Type
  Reads : Type
  genomeEquiv : Setoid Genome
  likelihood : Genome → Reads → ℝ
  bridgingConditions : Genome → Reads → Prop

namespace AssemblyModel

variable (M : AssemblyModel)

/-- The candidate genome is no less likely than every competing genome. -/
def IsMaximumLikelihood (truth : M.Genome) (reads : M.Reads) : Prop :=
  ∀ candidate : M.Genome,
    M.likelihood candidate reads ≤ M.likelihood truth reads

/--
The candidate is maximum-likelihood and every tie is equivalent to it.
For a circular-genome model, `genomeEquiv` is expected eventually to identify
cyclic shifts (and only whatever further identifications the source model makes).
-/
def IsUniqueMaximumLikelihoodUpToEquiv
    (truth : M.Genome) (reads : M.Reads) : Prop :=
  M.IsMaximumLikelihood truth reads ∧
    ∀ candidate : M.Genome,
      M.likelihood candidate reads = M.likelihood truth reads →
        M.genomeEquiv.r candidate truth

/-- Abstract implication corresponding to the weak, maximizer-only reading. -/
def BridgingImpliesMaximumLikelihood : Prop :=
  ∀ (truth : M.Genome) (reads : M.Reads),
    M.bridgingConditions truth reads → M.IsMaximumLikelihood truth reads

/-- Abstract implication corresponding to uniqueness up to genome equivalence. -/
def BridgingImpliesUniqueMaximumLikelihood : Prop :=
  ∀ (truth : M.Genome) (reads : M.Reads),
    M.bridgingConditions truth reads →
      M.IsUniqueMaximumLikelihoodUpToEquiv truth reads

end AssemblyModel

end AssemblyP1
