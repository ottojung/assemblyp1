# Issue #261 transfer lemma: spelled-maximal failure transfers upward

Bounded increment on top of `41fbd3c` (ACA/CAC, L=3, o_min=1).

Candidate class: spelled circuits (visit vectors), truth admitted as the spelled
2-circuit (ACA->CAC->ACA), fixed-external-N binomial likelihood with N=3,
sample x=(2,1), length universe n<=4 for spelled candidates.

Partial implication (proved by inclusion, not by image equality):
`AssemblyP1.Section62SpelledFlowMaximality.spelledVisitSet_subset_image` places
every spelled visit vector in the zero-terminal feasible throughput image.
Therefore `flow_not_maximal_of_spelled_witness` transfers the cell's spelled
defeater (throughput (2,1) scoring 16>8) to a proof that the truth's walk flow is
not ML-maximal over the full feasible-flow set. Full-overlap failures transfer
only under such inclusion; positive statements do not.

What stays OPEN: general maximality criterion, throughput-image characterization,
non-vacuous transitive reduction, other RC supports, real LP relaxation.
