import AssemblyP1.RigidityLength3Bridge

/-!
# Axiom audit for the length-3 antiparallel-bridge criterion (issue #257, §8.1)

Every declaration of `AssemblyP1/RigidityLength3Bridge.lean` must depend only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityLength3Bridge

#print axioms AssemblyP1.RigidityLength3Bridge.balancedL3_iff_eqs
#print axioms AssemblyP1.RigidityLength3Bridge.phi_balancedL3
#print axioms AssemblyP1.RigidityLength3Bridge.phi_sum
#print axioms AssemblyP1.RigidityLength3Bridge.phi_of_balanced
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_nonrigid_iff
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_nonrigid_m1
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_nonrigid_m2
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_nonrigid_f
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_rigid_repetitive
#print axioms AssemblyP1.RigidityLength3Bridge.length3Bridge_rigid_iff
