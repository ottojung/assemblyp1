import AssemblyP1.TwoWalkRoutable

/-!
# Axiom audit for the routing witnesses (issue #257)

Root-reachable axiom audit for `AssemblyP1.TwoWalkRoutable.lean`. Every
declaration must depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` from `native_decide`. The feasibility facts are proved
by kernel `decide`, so they are included here on purpose.
-/

open AssemblyP1.TwoWalkRoutable

#print axioms AssemblyP1.TwoWalkRoutable.atatat_routable
#print axioms AssemblyP1.TwoWalkRoutable.figureEight_routable
#print axioms AssemblyP1.TwoWalkRoutable.atatat_feasible
#print axioms AssemblyP1.TwoWalkRoutable.atatat_rigid
#print axioms AssemblyP1.TwoWalkRoutable.figureEight_no_two_nonneg_circ
#print axioms AssemblyP1.TwoWalkRoutable.figureEight_feasible
#print axioms AssemblyP1.TwoWalkRoutable.figureEight_rigid
