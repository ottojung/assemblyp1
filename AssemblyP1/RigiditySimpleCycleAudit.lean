import AssemblyP1.RigiditySimpleCycle

/-!
# Axiom audit for directed-cycle sufficiency and the AATT boundary
(issue #257, §22)

Every declaration of `AssemblyP1/RigiditySimpleCycle.lean` must depend only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigiditySimpleCycle

#print axioms AssemblyP1.RigiditySimpleCycle.cycle2_balanced_const
#print axioms AssemblyP1.RigiditySimpleCycle.cycle2_rigid
#print axioms AssemblyP1.RigiditySimpleCycle.cycle2_is_atatat_tail
#print axioms AssemblyP1.RigiditySimpleCycle.cycle2_is_atatat_head
#print axioms AssemblyP1.RigiditySimpleCycle.atatat_of_cycle2
#print axioms AssemblyP1.RigiditySimpleCycle.aatt_rigid
#print axioms AssemblyP1.RigiditySimpleCycle.aatt_search_space
