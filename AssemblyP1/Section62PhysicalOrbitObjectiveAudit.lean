import AssemblyP1.Section62PhysicalOrbitObjective

/-!
# Axiom audit for the physical edge-orbit objective transport (#255/#261, L3)

Audits every new declaration of
`AssemblyP1.Section62PhysicalOrbitObjective`.  The expected axiom set is a
subset of `[propext, Classical.choice, Quot.sound]` (the structural and `decide`
lemmas use none; the quotient/`funext` lemmas use `propext`), with no `sorryAx`.
No `sorry` / `admit` / `axiom` / `native_decide`.
-/

/-! ## The physical visit-count vector -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physVisitVec
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physVisitVec_apply
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physVisitVec_reverse
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physPosTotal_add
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physVisitVec_add

/-! ## The transported vertex lower bound -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjective.PhysVertexBound
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physVertexBound_reverse

/-! ## The ML objective transport -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physMaximal_image_iff
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.physMaximal_reverse_iff

/-! ## Mixed-sign loop witness -/

#print axioms AssemblyP1.Section62PhysicalOrbitObjective.Witness.mixed_visit_one
#print axioms AssemblyP1.Section62PhysicalOrbitObjective.Witness.mixed_physical_ne_departure
