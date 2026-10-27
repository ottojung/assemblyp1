import AssemblyP1.SeparableConvexKKTRefutation263

open AssemblyP1.KKTRefutation263

-- Axiom audit for the unconstrained-KKT refutation (#263).
-- Every endpoint must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms AssemblyP1.KKTRefutation263.hasDerivAt_mlCost
#print axioms AssemblyP1.KKTRefutation263.deriv_mlCost_eq
#print axioms AssemblyP1.KKTRefutation263.mlCost_slope_neg
#print axioms AssemblyP1.KKTRefutation263.mlCost_slope_ne_zero
#print axioms AssemblyP1.KKTRefutation263.mlCost_slope_at_truth
#print axioms AssemblyP1.KKTRefutation263.truthCounts_zero
#print axioms AssemblyP1.KKTRefutation263.truthCounts_one
#print axioms AssemblyP1.KKTRefutation263.truthCounts_two
#print axioms AssemblyP1.KKTRefutation263.truthCounts_three
#print axioms AssemblyP1.KKTRefutation263.truthCounts_pos
#print axioms AssemblyP1.KKTRefutation263.truth_coord_slope
#print axioms AssemblyP1.KKTRefutation263.truth_gradient_ne_zero
