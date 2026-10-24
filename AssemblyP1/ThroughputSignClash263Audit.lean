import AssemblyP1.ThroughputSignClash263

-- Axiom audit for the concrete throughput sign-clash witness (#263).
-- Every endpoint must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms AssemblyP1.ThroughputSignClash263.kernel_decomposition
#print axioms AssemblyP1.ThroughputSignClash263.edge_conformal
#print axioms AssemblyP1.ThroughputSignClash263.naive_lift_throughput_sign_clash
#print axioms AssemblyP1.ThroughputSignClash263.bounded_feasible_pair
