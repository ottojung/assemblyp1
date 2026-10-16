import AssemblyP1.RigidityTargetCycle

/-!
# Axiom audit for the target-cycle / coin reduction (issue #257, §8.1/§8.2)

Every declaration of `AssemblyP1/RigidityTargetCycle.lean` must depend only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityTargetCycle

#print axioms AssemblyP1.RigidityTargetCycle.tcLen_pos
#print axioms AssemblyP1.RigidityTargetCycle.tcG_cast
#print axioms AssemblyP1.RigidityTargetCycle.tc_atot
#print axioms AssemblyP1.RigidityTargetCycle.targetCycle_nonrigid_iff_coin
#print axioms AssemblyP1.RigidityTargetCycle.targetCycle_rigid_iff_not_coin
#print axioms AssemblyP1.RigidityTargetCycle.coin_nonrigid_23_5
#print axioms AssemblyP1.RigidityTargetCycle.coin_rigid_23_1
#print axioms AssemblyP1.RigidityTargetCycle.coin_rigid_33_2
