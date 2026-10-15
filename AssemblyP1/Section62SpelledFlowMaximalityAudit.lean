import AssemblyP1.Section62SpelledFlowMaximality

/-!
# Independent axiom audit for the #261 spelled sub-class maximality transfer

Audits the length-universe invariant (`sum_visits_eq_n`, `sum_throughput_eq_n`),
the spelled sub-class inclusion (`spelledVisitSet_subset_image`), and the two
maximality-transfer theorems.  It does NOT claim sufficiency (the spelled
sub-class is a strict sub-class of the feasible throughput image), nor an image
characterization.
-/

#print axioms AssemblyP1.Section62SpelledFlowMaximality.sum_visits_eq_n
#print axioms AssemblyP1.Section62SpelledFlowMaximality.sum_throughput_eq_n
#print axioms AssemblyP1.Section62SpelledFlowMaximality.spelledVisitSet_subset_image
#print axioms AssemblyP1.Section62SpelledFlowMaximality.spelled_maximal_of_flow_maximal
#print axioms AssemblyP1.Section62SpelledFlowMaximality.flow_not_maximal_of_spelled_witness
#print axioms AssemblyP1.Section62SpelledFlowMaximality.spelled_truth_flow_not_maximal_of_spelled_witness
#print axioms AssemblyP1.Section62SpelledFlowMaximality.flow_maximal_iff_spelled_maximal_of_image_eq
