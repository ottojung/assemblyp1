import AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness

/-!
# Axiom audit for uniqueness transport of the physical edge-orbit objective (#255/#261, L3)

Audits every new declaration of
`AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness`.  The expected axiom set
is a subset of `[propext, Classical.choice, Quot.sound]` (the `decide`-style
witness lemmas use none; the quotient/`funext` lemmas use `propext`), with no
`sorryAx`.  No `sorry` / `admit` / `axiom` / `native_decide`.
-/

/-! ## Uniqueness transport -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.UniqueMaximal
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.physUniqueMaximal_image_of_flow
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.physUniqueMaximal_of_injective
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.physUniqueMaximal_iff_of_injective

/-! ## The non-injective witness -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.twoIds
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.twoRep
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.flowA
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.flowB
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.physMk_twoRep_eq
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.physVisitVec_twoRep_eq
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.flowA_ne_flowB
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.candSet
#print axioms AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness.MixedLoop.physUniqueMaximal_not_transported
