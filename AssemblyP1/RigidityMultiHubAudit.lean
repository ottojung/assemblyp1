import AssemblyP1.RigidityMultiHub

/-!
# Axiom audit for the multi-hub rigidity criterion (issue #257, §8.1/§8.2)

Every declaration of `AssemblyP1/RigidityMultiHub.lean` must depend only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityMultiHub

#print axioms AssemblyP1.RigidityMultiHub.balancedB_iff_balancedZ
#print axioms AssemblyP1.RigidityMultiHub.balanced_step
#print axioms AssemblyP1.RigidityMultiHub.path_const
#print axioms AssemblyP1.RigidityMultiHub.phi_of_balanced
#print axioms AssemblyP1.RigidityMultiHub.balanced_of_phi
#print axioms AssemblyP1.RigidityMultiHub.phi_sum
#print axioms AssemblyP1.RigidityMultiHub.mA_total
#print axioms AssemblyP1.RigidityMultiHub.mA_balanced
#print axioms AssemblyP1.RigidityMultiHub.multiHub_nonrigid_iff
#print axioms AssemblyP1.RigidityMultiHub.multiHub_rigid_all_one
#print axioms AssemblyP1.RigidityMultiHub.multiHub_rigid_repetitive_2
#print axioms AssemblyP1.RigidityMultiHub.multiHub_relaxed_not_sound
