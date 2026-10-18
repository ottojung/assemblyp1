import AssemblyP1.RigidityDoubleTheta

/-!
# Axiom audit for the double-theta rigidity criterion (issue #257, §8.1)

Every declaration of `AssemblyP1/RigidityDoubleTheta.lean` must depend only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityDoubleTheta

#print axioms AssemblyP1.RigidityDoubleTheta.balancedB_iff_eqs
#print axioms AssemblyP1.RigidityDoubleTheta.dtA_balanced
#print axioms AssemblyP1.RigidityDoubleTheta.dtA_total
#print axioms AssemblyP1.RigidityDoubleTheta.phi_balancedB
#print axioms AssemblyP1.RigidityDoubleTheta.phi_sum
#print axioms AssemblyP1.RigidityDoubleTheta.phi_of_balanced
#print axioms AssemblyP1.RigidityDoubleTheta.doubleTheta_nonrigid_iff
#print axioms AssemblyP1.RigidityDoubleTheta.doubleTheta_nonrigid_witness
#print axioms AssemblyP1.RigidityDoubleTheta.doubleTheta_rigid_repetitive
#print axioms AssemblyP1.RigidityDoubleTheta.relaxed_not_sound
