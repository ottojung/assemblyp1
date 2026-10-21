import AssemblyP1.RigidityTriHub

/-!
# Axiom audit for the triangular multi-hub rigidity criterion (issue #257, §8.1/§8.2)

Every declaration of `AssemblyP1/RigidityTriHub.lean` must depend only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityTriHub

#print axioms AssemblyP1.RigidityTriHub.balancedB_iff_balancedZ
#print axioms AssemblyP1.RigidityTriHub.balanced_step
#print axioms AssemblyP1.RigidityTriHub.path_const
#print axioms AssemblyP1.RigidityTriHub.phi_of_balanced
#print axioms AssemblyP1.RigidityTriHub.balanced_of_phi
#print axioms AssemblyP1.RigidityTriHub.phi_sum
#print axioms AssemblyP1.RigidityTriHub.mA_total
#print axioms AssemblyP1.RigidityTriHub.mA_balanced
#print axioms AssemblyP1.RigidityTriHub.sum_elim_three
#print axioms AssemblyP1.RigidityTriHub.triHub_nonrigid_iff
#print axioms AssemblyP1.RigidityTriHub.triHub_rigid_all_one
#print axioms AssemblyP1.RigidityTriHub.triHub_rigid_repetitive
#print axioms AssemblyP1.RigidityTriHub.triHub_relaxed_not_sound
