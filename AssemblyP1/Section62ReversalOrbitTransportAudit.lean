import AssemblyP1.Section62ReversalOrbitTransport

/-!
# Axiom audit for the reversal-orbit transport module (#255/#261)

Audits every new declaration of
`AssemblyP1.Section62ReversalOrbitTransport`.  The expected axiom set is a
subset of `[propext, Classical.choice, Quot.sound]` (the `decide`/`ring`/`omega`
lemmas use none; the quotient lemmas use `Quot.sound`), with no `sorryAx`.  No
`sorry` / `admit` / `axiom` / `native_decide`.
-/

/-! ## Reversal-symmetric flows and the transport identities -/

#print axioms AssemblyP1.Section62ReversalOrbitTransport.RevSymm
#print axioms AssemblyP1.Section62ReversalOrbitTransport.throughput_pair_cls
#print axioms AssemblyP1.Section62ReversalOrbitTransport.throughput_pair_selfloop
#print axioms AssemblyP1.Section62ReversalOrbitTransport.throughput_pair_selfloop_symm
#print axioms AssemblyP1.Section62ReversalOrbitTransport.throughput_pair_selfloop_symm_even

/-! ## The minimal witness -/

#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixedRev
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixedRev_ne_mixedLoop
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixedRev_same_orbit
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixedLoop_selfloop
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixedLoop_cls_sx
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixed_physical_visit_one
#print axioms AssemblyP1.Section62ReversalOrbitTransport.mixed_physical_visit_one_rev
#print axioms AssemblyP1.Section62ReversalOrbitTransport.no_revsymm_throughput_one
#print axioms AssemblyP1.Section62ReversalOrbitTransport.no_revsymm_flow_realizes_unit_loop
#print axioms AssemblyP1.Section62ReversalOrbitTransport.symmetric_discipline_refuted
