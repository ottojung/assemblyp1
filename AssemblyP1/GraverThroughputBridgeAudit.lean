import AssemblyP1.GraverThroughputBridge

open AssemblyP1.GraverThroughputBridge

-- Axiom audit for the edge-flow / vertex-throughput Graver bridge (#263).
-- Every endpoint must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms AssemblyP1.GraverThroughputBridge.flowLin_add
#print axioms AssemblyP1.GraverThroughputBridge.flowLin_sub
#print axioms AssemblyP1.GraverThroughputBridge.flowLin_eq_zero_iff
#print axioms AssemblyP1.GraverThroughputBridge.conformal_same_sign
#print axioms AssemblyP1.GraverThroughputBridge.list_sum_same_sign
#print axioms AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_flow
#print axioms AssemblyP1.GraverThroughputBridge.graver_flowLin_eq_zero
#print axioms AssemblyP1.GraverThroughputBridge.graver_optimal_flow
#print axioms AssemblyP1.GraverThroughputBridge.augLin_eq_zero_iff
#print axioms AssemblyP1.GraverThroughputBridge.T_zero
#print axioms AssemblyP1.GraverThroughputBridge.T_sub
#print axioms AssemblyP1.GraverThroughputBridge.T_list_sum
#print axioms AssemblyP1.GraverThroughputBridge.lift_list_sum
#print axioms AssemblyP1.GraverThroughputBridge.augLin_sub
#print axioms AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_aug
