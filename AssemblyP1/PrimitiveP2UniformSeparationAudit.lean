import AssemblyP1.PrimitiveP2UniformSeparation

/-!
# Axiom audit for the uniform primitive-P2 separation / exponential bound
  (issue #281)

Every endpoint of `AssemblyP1.PrimitiveP2UniformSeparation` is expected to
depend only on the three standard Lean/Mathlib axioms
`propext`, `Classical.choice` and `Quot.sound`, with no `sorry`, `admit` or
new `axiom`. This file records that audit mechanically.
-/

#print axioms AssemblyP1.PrimitiveP2UniformSeparation.one_le_abs_cast_sub
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.readLaw_separation
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.abs_sub_le_two_abs_sqrt_sub
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.one_sub_hellinger_ge_of_gap
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.hellinger_le_of_length_bound
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.exp_error_bound_of_length_bound
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.card_mul_exp_neg_div_le
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.primitiveP2_ML_confidence_explicit
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.card_shortGenomes_le
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.readLawFamily_card_le
#print axioms AssemblyP1.PrimitiveP2UniformSeparation.separation_gap_strict_at_L2

namespace AssemblyP1.PrimitiveP2UniformSeparationAudit

open AssemblyP1.PrimitiveP2UniformSeparation

/-! ## Non-vacuity of the separation constant

At `L = 2` over a two-letter alphabet the primitive-P2 length bound is
`B = 4`, and the uniform affinity gap is `1 - 1/(8 * 4^4) = 1 - 1/2048`,
strictly below the trivial bound `1`. The candidate class itself is nonempty:
`AssemblyP1.PrimitiveP2FiniteClassAudit` exhibits `1100 ∈ primitiveP2Candidates 2`
with `maxLen Bool 2 = 4`, so the theorem's hypotheses are satisfiable. -/

example : (1 : ℝ) - 1 / (8 * (4 : ℝ) ^ 4) = 2047 / 2048 := by norm_num

example : (1 : ℝ) - 1 / (8 * (4 : ℝ) ^ 4) < 1 := separation_gap_strict_at_L2

end AssemblyP1.PrimitiveP2UniformSeparationAudit
