import AssemblyP1.Model

namespace AssemblyP1

/-
A namespace for the theorem statement that this project is intended to reach.

At bootstrap time we deliberately do not assert a theorem or axiom here. The
main research task is first to instantiate `AssemblyModel` faithfully from the
published sequencing and maximum-likelihood models, then determine which of the
formal schemas in `AssemblyP1.Model` is the exact open statement.
-/
namespace OpenProblem

/-- The weaker candidate statement: bridging makes the true genome an ML maximizer. -/
def MaximizerSchema (M : AssemblyModel) : Prop :=
  M.BridgingImpliesMaximumLikelihood

/--
The stronger candidate statement: bridging makes the true genome the unique ML
assembly up to the model's genome equivalence.
-/
def UniqueSchema (M : AssemblyModel) : Prop :=
  M.BridgingImpliesUniqueMaximumLikelihood

end OpenProblem

end AssemblyP1
