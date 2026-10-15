import AssemblyP1.Section62SpelledFlowAdapter

/-!
# Independent axiom audit for the #261 spelled-circuit → feasible-flow adapter

Audits the general adapter `spelling_flow_feasible`, its two computational halves
(`throughput_eq_visits`, `balCore_eq_zero`), the weighted de-duplication lemma,
and the spelled-throughput image corollary.  It does NOT claim that every
feasible flow is spelled, nor that the §6.1 product-binomial surrogate equals the
exact iid likelihood.
-/

#print axioms AssemblyP1.Section62SpelledFlowAdapter.spelling_flow_feasible
#print axioms AssemblyP1.Section62SpelledFlowAdapter.throughput_eq_visits
#print axioms AssemblyP1.Section62SpelledFlowAdapter.balCore_eq_zero
#print axioms AssemblyP1.Section62SpelledFlowAdapter.weighted_dedup
#print axioms AssemblyP1.Section62SpelledFlowAdapter.visits_mem_throughput_image
