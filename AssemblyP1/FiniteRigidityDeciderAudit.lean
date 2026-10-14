import AssemblyP1.FiniteRigidityDecider

/-!
# Axiom audit for the finite rigidity decider (issue #257)

Root-reachable axiom audit for `AssemblyP1.FiniteRigidityDecider.lean` (imported
from `AssemblyP1.lean`, and built by the `AssemblyP1` library glob). Every
declaration must depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` from `native_decide`. The examples are proved by kernel
`decide`, so they are included here on purpose.
-/

open AssemblyP1.FiniteRigidityDecider

#print axioms AssemblyP1.FiniteRigidityDecider.le_total_of_feasible
#print axioms AssemblyP1.FiniteRigidityDecider.admissible_iff
#print axioms AssemblyP1.FiniteRigidityDecider.rigid_iff_forall_admissible
#print axioms AssemblyP1.FiniteRigidityDecider.rigid_iff_decider
#print axioms AssemblyP1.FiniteRigidityDecider.card_candidates
#print axioms AssemblyP1.FiniteRigidityDecider.atatat_rigid
#print axioms AssemblyP1.FiniteRigidityDecider.aaaab_nonrigid
#print axioms AssemblyP1.FiniteRigidityDecider.figureEight_rigid
#print axioms AssemblyP1.FiniteRigidityDecider.figureEight_nonrigid
