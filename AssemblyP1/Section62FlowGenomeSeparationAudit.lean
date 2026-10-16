import AssemblyP1.Section62FlowGenomeSeparation

/-!
# Independent axiom audit for the §6.2 / genome-likelihood separation (#269)

This audits the exact statements that separate the MB09 §6.2 feasible-flow
objective from the source-faithful circular-oriented-genome likelihood.  It does
**not** claim the §6.1 product-binomial versus exact-iid distinction (that is
`AssemblyP1.GenomeOrbitAdapter.ExactVsSurrogate`) nor the throughput-image
classification of #261 (`AssemblyP1.Section62SpelledFlowImageRefutation`).
-/

#print axioms AssemblyP1.Section62FlowGenomeSeparation.flow_objective_factors_throughput
#print axioms AssemblyP1.Section62FlowGenomeSeparation.flow_maximality_is_throughput_property
#print axioms AssemblyP1.Section62FlowGenomeSeparation.classCount_eq_sum
#print axioms AssemblyP1.Section62FlowGenomeSeparation.classCount_eq_visits
#print axioms AssemblyP1.Section62FlowGenomeSeparation.likelihood_S0_ne_S1
#print axioms AssemblyP1.Section62FlowGenomeSeparation.exactLikelihood_not_factors_throughput
#print axioms AssemblyP1.Section62FlowGenomeSeparation.no_flow_objective_eq_likelihood
#print axioms AssemblyP1.Section62FlowGenomeSeparation.section62_flow_objective_ne_genome_likelihood
