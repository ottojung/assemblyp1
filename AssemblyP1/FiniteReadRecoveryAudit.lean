import AssemblyP1.FiniteReadRecovery

/-! # Independent kernel axiom audit for finite iid recovery (#270)

Statements are generic finite read-distribution theorems.  No claim is made
that the genome sampling-model adapter or unbounded candidate class has yet
been formalized. -/

#print axioms AssemblyP1.FiniteReadRecovery.hellinger_sq_identity
#print axioms AssemblyP1.FiniteReadRecovery.hellinger_le_one
#print axioms AssemblyP1.FiniteReadRecovery.hellinger_lt_one_iff_ne
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_pairwise
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_sum
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_card
#print axioms AssemblyP1.FiniteReadRecovery.exp_pow_nat_eq
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_exp
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_exp_of_identifiable
#print axioms AssemblyP1.FiniteReadRecovery.eventProb_wrong_tendsto_zero
#print axioms AssemblyP1.FiniteReadRecovery.exists_n_for_confidence
#print axioms AssemblyP1.FiniteReadRecovery.il_confidence_99
