import AssemblyP1.FiniteBreslerObstructionGap

/-! Axiom audit for the #272 target-5 result that the Bresler--Bresler--Tse
all-unbridged obstruction is **not** the exact necessary-and-sufficient condition
for finite read-only recovery.

Every endpoint below must depend only on the three permitted axioms `propext`,
`Classical.choice`, and `Quot.sound`. -/

#print axioms AssemblyP1.FiniteBreslerObstructionGap.sourceObstruction_necessary_of_bresler
#print axioms AssemblyP1.FiniteBreslerObstructionGap.realizable_aabb
#print axioms AssemblyP1.FiniteBreslerObstructionGap.realizable_aaab
#print axioms AssemblyP1.FiniteBreslerObstructionGap.not_sourceObstruction_aabb
#print axioms AssemblyP1.FiniteBreslerObstructionGap.orbit_aaab_ne_aabb
#print axioms AssemblyP1.FiniteBreslerObstructionGap.not_unambiguous_aabb
#print axioms AssemblyP1.FiniteBreslerObstructionGap.sourceObstruction_not_sufficient_for_readOnly_certainty
#print axioms AssemblyP1.FiniteBreslerObstructionGap.counterexample
#print axioms AssemblyP1.FiniteBreslerObstructionGap.sourceObstruction_not_exact_condition
