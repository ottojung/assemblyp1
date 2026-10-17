import AssemblyP1.RigidityGeneralBridge

/-!
# Axiom audit for the general `p,q` long-bridge criterion (issue #257, §8.1)

Every declaration of `AssemblyP1/RigidityGeneralBridge.lean` must depend only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityGeneralBridge

#print axioms AssemblyP1.RigidityGeneralBridge.phi_balanced
#print axioms AssemblyP1.RigidityGeneralBridge.phi_sum
#print axioms AssemblyP1.RigidityGeneralBridge.phi_eq_zero_iff
#print axioms AssemblyP1.RigidityGeneralBridge.phi_of_balanced
#print axioms AssemblyP1.RigidityGeneralBridge.gA_balanced
#print axioms AssemblyP1.RigidityGeneralBridge.gA_total
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_iff
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_m2_large
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_m1_large
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_eq_m1
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_eq_m2
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_q3_f
#print axioms AssemblyP1.RigidityGeneralBridge.generalBridge_rigid_repetitive
