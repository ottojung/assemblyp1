import AssemblyP1.PrimitiveP2FiniteClassTight

/-!
# Axiom audit and non-vacuity for the `K = 1` tightness result (issue #281)

`AssemblyP1.PrimitiveP2FiniteClassTight.exists_primitive_P2_at_bound_K1`
proves that for every finite alphabet of cardinality `q ≥ 2` the doubled
alphabet word `0 0 1 1 ... (q-1)(q-1)` is a primitive P2-admissible genome of
length exactly `2 * q = maxLen 2`, so the length bound of
`AssemblyP1.PrimitiveP2FiniteClass.primitive_P2_len_le` is attained for every
`q ≥ 2` at `K = 1`.

This module only re-checks the axiom dependencies of the endpoints. Nothing
here adds a hypothesis or restates a result.
-/

#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.pairWord_eq_iff
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.no_triple
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.window_two_injective
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.repeat_consec
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.not_interleaved
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.pairWord_primitive
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.pairWord_P2
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.exists_primitive_P2_at_bound_K1
#print axioms AssemblyP1.PrimitiveP2FiniteClassTight.maxLen_two
