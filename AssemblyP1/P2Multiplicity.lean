import AssemblyP1.P2RepeatResidual

/-!
# P2 multiplicity interface (compatibility import)

This file formerly redeclared three public lemmas already present in
P2RepeatResidual:
* IsPrimitive.shiftPrimitive
* P2.imp_nodeCount_le_two
* P2.imp_nodeCount_le_two_of_powerPrimitive

Importing both modules into AssemblyP1 caused Lean duplicate-declaration
errors. The exact statements and their certified proofs now have a single
canonical implementation in P2RepeatResidual; existing imports of this
module continue to bring those theorems into scope.
-/
