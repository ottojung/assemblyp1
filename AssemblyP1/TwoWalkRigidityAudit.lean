import AssemblyP1.TwoWalkRigidity

/-!
# Axiom audit for the two-closed-walk rigidity criterion (issue #257)

Root-reachable axiom audit for `AssemblyP1.TwoWalkRigidity.lean`. Every
declaration must depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` from `native_decide`. The worked instance
`figureEight_two_walk_witness` is proved by kernel `decide`, so it is included
here on purpose.
-/

open AssemblyP1.TwoWalkRigidity

#print axioms AssemblyP1.TwoWalkRigidity.isCirc_iff_balancedZ
#print axioms AssemblyP1.TwoWalkRigidity.IsCirc.add
#print axioms AssemblyP1.TwoWalkRigidity.IsCirc.sub
#print axioms AssemblyP1.TwoWalkRigidity.nonrigid_of_two_nonneg_circ
#print axioms AssemblyP1.TwoWalkRigidity.exists_two_nonneg_circ_of_nonrigid
#print axioms AssemblyP1.TwoWalkRigidity.rigid_iff_no_two_nonneg_circ
#print axioms AssemblyP1.TwoWalkRigidity.atatat_no_two_nonneg_circ
#print axioms AssemblyP1.TwoWalkRigidity.figureEight_two_walk_witness
