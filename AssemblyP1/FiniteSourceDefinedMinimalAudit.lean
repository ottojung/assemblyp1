import AssemblyP1.FiniteSourceDefinedMinimal

/-! Axiom audit for the #272 minimum / minimal sufficient promise results.

Every endpoint below must depend only on the three permitted axioms
`propext`, `Classical.choice`, and `Quot.sound`. -/

#print axioms AssemblyP1.FiniteSourceDefinedMinimal.minimum_vacuous
#print axioms AssemblyP1.FiniteSourceDefinedMinimal.TwoCandidate.sufficient_iff_not_both
#print axioms AssemblyP1.FiniteSourceDefinedMinimal.TwoCandidate.nonvacuous_sufficient_is_designation
#print axioms AssemblyP1.FiniteSourceDefinedMinimal.TwoCandidate.designation_nonvacuous_sufficient
#print axioms AssemblyP1.FiniteSourceDefinedMinimal.TwoCandidate.designations_incomparable
#print axioms AssemblyP1.FiniteSourceDefinedMinimal.TwoCandidate.three_way_distinction
