import AssemblyP1.PrimitiveP2ExponentInsertion

/-!
# Axiom audit for the insertion-affinity lemmas (issue #265)

Every endpoint of `AssemblyP1.PrimitiveP2ExponentInsertion` is expected to
depend only on the three standard Lean/Mathlib axioms `propext`,
`Classical.choice` and `Quot.sound`, with no `sorry`, `admit` or new `axiom`.
This file records that audit mechanically.
-/

#print axioms AssemblyP1.PrimitiveP2ExponentInsertion.hellinger_convex_delta
#print axioms AssemblyP1.PrimitiveP2ExponentInsertion.one_sub_hellinger_convex_delta
#print axioms AssemblyP1.PrimitiveP2ExponentInsertion.one_sub_hellinger_insertion
#print axioms AssemblyP1.PrimitiveP2ExponentInsertion.insertion_gap_ge_half_over_succ
