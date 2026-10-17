import AssemblyP1.RigidityNoGo

/-!
# Axiom audit for the coin-problem rigidity obstruction (issue #257, §8.1/§8.2)

Every declaration of `AssemblyP1/RigidityNoGo.lean` must depend only on the three
standard axioms `propext`, `Classical.choice`, `Quot.sound` — in particular no
`sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`).
-/

open AssemblyP1.RigidityNoGo

#print axioms AssemblyP1.RigidityNoGo.coin_hlen
#print axioms AssemblyP1.RigidityNoGo.coin_hM
#print axioms AssemblyP1.RigidityNoGo.coin_total
#print axioms AssemblyP1.RigidityNoGo.coin_bouquet_nonrigid_iff
#print axioms AssemblyP1.RigidityNoGo.coin_bouquet_real_nonrigid
#print axioms AssemblyP1.RigidityNoGo.coins23_ge
#print axioms AssemblyP1.RigidityNoGo.coins23_target1_rigid
#print axioms AssemblyP1.RigidityNoGo.coins23_target5_nonrigid
