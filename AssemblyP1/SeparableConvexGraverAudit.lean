import AssemblyP1.SeparableConvexGraver

open AssemblyP1.SeparableConvexGraver

-- Axiom audit for the separable-convex Graver optimality certificate (#263).
-- Every endpoint must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms AssemblyP1.SeparableConvexGraver.inc_mono
#print axioms AssemblyP1.SeparableConvexGraver.quad_pos
#print axioms AssemblyP1.SeparableConvexGraver.discConvOn_neg
#print axioms AssemblyP1.SeparableConvexGraver.quad_neg
#print axioms AssemblyP1.SeparableConvexGraver.superadd_list
#print axioms AssemblyP1.SeparableConvexGraver.superadd_separable_list
#print axioms AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving
#print axioms AssemblyP1.SeparableConvexGraver.multiplier_improving
#print axioms AssemblyP1.SeparableConvexGraver.ray_unit_mem_box
#print axioms AssemblyP1.SeparableConvexGraver.multiplier_unit_feasible_improving
#print axioms AssemblyP1.SeparableConvexGraver.ray_unit_mem_fiber
#print axioms AssemblyP1.SeparableConvexGraver.negLog_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.negLog_sub_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.multinomialTerm_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.binomTerm_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.affineExtend_of_le
#print axioms AssemblyP1.SeparableConvexGraver.affineExtend_of_ge
#print axioms AssemblyP1.SeparableConvexGraver.affineExtend_of_mid
#print axioms AssemblyP1.SeparableConvexGraver.affineExtend_of_le_U
#print axioms AssemblyP1.SeparableConvexGraver.inc_affineExtend
#print axioms AssemblyP1.SeparableConvexGraver.affineExtend_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.multinomialTerm_ext_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.binomTerm_ext_discConvOn
#print axioms AssemblyP1.SeparableConvexGraver.binomTerm_degenerate_discConvOn
