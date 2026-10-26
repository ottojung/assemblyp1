import AssemblyP1.SeparableConvexKKTGap263

open AssemblyP1.KKTGap263

-- Axiom audit for the exact-rational KKT-gap witness (#263/259).
-- Every endpoint must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms AssemblyP1.KKTGap263.score_truth
#print axioms AssemblyP1.KKTGap263.kktGap_uniqueMax
#print axioms AssemblyP1.KKTGap263.resid_vals
#print axioms AssemblyP1.KKTGap263.statVec_vals
#print axioms AssemblyP1.KKTGap263.no_equal_multiplier
#print axioms AssemblyP1.KKTGap263.dirV_sum
#print axioms AssemblyP1.KKTGap263.directional_nonzero
