import AssemblyP1.RigidityBouquet

/-!
# Axiom audit for the bouquet rigidity criterion (issue #257, §8.1)

Every declaration of `AssemblyP1/RigidityBouquet.lean` must depend only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityBouquet

#print axioms AssemblyP1.RigidityBouquet.balancedB_iff_balancedZ
#print axioms AssemblyP1.RigidityBouquet.internal_balance
#print axioms AssemblyP1.RigidityBouquet.balanced_constcyc
#print axioms AssemblyP1.RigidityBouquet.const_balanced
#print axioms AssemblyP1.RigidityBouquet.sum_bedges_const
#print axioms AssemblyP1.RigidityBouquet.bouquet_nonrigid_iff
#print axioms AssemblyP1.RigidityBouquet.len24_mult21_rigid
#print axioms AssemblyP1.RigidityBouquet.len23_mult41_nonrigid
#print axioms AssemblyP1.RigidityBouquet.len233_mult211_real_integer_gap
