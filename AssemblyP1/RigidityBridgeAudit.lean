import AssemblyP1.RigidityBridge

/-!
# Axiom audit for the antiparallel-bridge rigidity criterion (issue #257, §8.1)

Every declaration of `AssemblyP1/RigidityBridge.lean` must depend only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityBridge

#print axioms AssemblyP1.RigidityBridge.balancedB_iff_eqs
#print axioms AssemblyP1.RigidityBridge.phi_balancedB
#print axioms AssemblyP1.RigidityBridge.phi_sum
#print axioms AssemblyP1.RigidityBridge.phi_of_balanced
#print axioms AssemblyP1.RigidityBridge.bridge_nonrigid_iff
#print axioms AssemblyP1.RigidityBridge.bridgeA_rigid_iff_trivial
#print axioms AssemblyP1.RigidityBridge.bridgeA_nonrigid_m1
#print axioms AssemblyP1.RigidityBridge.bridgeA_nonrigid_m2
#print axioms AssemblyP1.RigidityBridge.bridgeA_nonrigid_f
