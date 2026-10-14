import AssemblyP1.Section62FlowCountVectorAdapter

/-!
# Independent axiom audit for MB09 §6.2 throughput-image reduction (#261)

This audits the exact theorems and the instantiated zero-terminal feasibility
domain. It does NOT claim the throughput image equals a class of spelled
genomes or that MB09's binomial and circuit-cost objectives are equal.
-/

#print axioms AssemblyP1.Section62FlowCountVectorAdapter.maximal_of_subset
#print axioms AssemblyP1.Section62FlowCountVectorAdapter.not_maximal_of_subset
#print axioms AssemblyP1.Section62FlowCountVectorAdapter.throughputVec_congr
#print axioms AssemblyP1.Section62FlowCountVectorAdapter.maximal_image_iff
#print axioms AssemblyP1.Section62FlowCountVectorAdapter.feasible_flow_maximal_image_iff
