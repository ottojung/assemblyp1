import AssemblyP1.Section62FullOverlapLift

/-!
# Independent axiom audit: bidirected full-overlap witness threshold transfer

This audit makes the new #262 theorems explicit in root `AssemblyP1.lean`,
so root-level kernel replay and axiom checks cannot accidentally omit them.
The concrete strict likelihood witness is for readLen=3, oMin=2 lowered to 1.
General graph monotonicity is proved for arbitrary lowered thresholds.
-/

#print axioms AssemblyP1.Section62FullOverlapLift.overlapEdges_mono
#print axioms AssemblyP1.Section62FullOverlapLift.fullOverlap_step_survives
#print axioms AssemblyP1.Section62FullOverlapLift.throughput_pre_append
#print axioms AssemblyP1.Section62FullOverlapLift.balCore_pre_append
#print axioms AssemblyP1.Section62FullOverlapLift.feasible62_zeroExtend_of_decomp
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.truth_lifted_feasible62
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.competitor_lifted_feasible62
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.truth_steps_survive_spelling
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.competitor_steps_survive_spelling
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.bridging_lifted_strict_counterexample
