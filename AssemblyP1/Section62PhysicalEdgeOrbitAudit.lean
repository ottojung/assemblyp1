import AssemblyP1.Section62PhysicalEdgeOrbit

/-!
# Axiom audit for the physical edge-orbit flow module (#261)

Audits every new declaration of
`AssemblyP1.Section62PhysicalEdgeOrbit`.  The expected axiom set is a subset of
`[propext, Classical.choice, Quot.sound]` (the `decide`/structural lemmas use
none; the quotient lemmas use `Quot.sound`), with no `sorryAx`.  No `sorry` /
`admit` / `axiom` / `native_decide`.
-/

/-! ## Reversal setoid -/

#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.revRel_refl
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.revRel_symm
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.revRel_trans
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physMk_reverse
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.revRel_len
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.not_revRel_of_len_ne

/-! ## Well-defined physical half-incidences -/

#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physPos_mk
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physNeg_mk
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physPos_reverse
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physNeg_reverse

/-! ## Orbit-indexed flow totals -/

#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physPosTotal_reverse
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physNegTotal_reverse
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.physBalanced_reverse

/-! ## ATAT witness -/

#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.reverse_E1
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.reverse_E2
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.reverse_E3
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.reverse_E4
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.orbit_E1_E4
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.physMk_E2_ne_E1
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.physMk_E3_ne_E1
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.physMk_E3_ne_E2
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.mixedLoop_posHalf
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.mixedLoop_negHalf
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.positiveLoop_posHalf
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.negativeLoop_negHalf
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.orbit_balanced
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.orbit_visit_one
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.orbit_visit_one_neg
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.inherited_throughput_two
#print axioms AssemblyP1.Section62PhysicalEdgeOrbit.Atat.inherited_throughput_not_physical
