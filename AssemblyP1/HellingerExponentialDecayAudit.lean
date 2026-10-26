import AssemblyP1.HellingerExponentialDecay
import AssemblyP1.HellingerSingleCompetitor
import AssemblyP1.HellingerTwoCompetitor
import AssemblyP1.HellingerNoDecay

/-! # Independent kernel axiom audit for the generic Hellinger-affinity
exponential decay of exact-ML error (issue #281)

`AssemblyP1.HellingerExponentialDecay` supplies the generic
Hellinger-affinity contraction step and the finite-family exponential
exact-ML error bound, reusing the merged `FiniteReadRecovery` endpoints.  The
statements are generic finite-read-distribution theorems; no genome or
candidate-class structure is assumed. -/

#print axioms AssemblyP1.HellingerExponentialDecay.hellinger_pow_eq_exp_neg
#print axioms AssemblyP1.HellingerExponentialDecay.hellinger_pow_le_exp_neg
#print axioms AssemblyP1.HellingerExponentialDecay.eventProb_wrong_eq_zero_of_affinity_zero
#print axioms AssemblyP1.HellingerExponentialDecay.eventProb_wrong_le_exp_neg
#print axioms AssemblyP1.HellingerExponentialDecay.exists_uniform_affinity_lt_one
#print axioms AssemblyP1.HellingerExponentialDecay.eventProb_wrong_le_exp_neg_identifiable
#print axioms AssemblyP1.HellingerSingleCompetitor.eventProb_wrong_single_le_exp_neg
#print axioms AssemblyP1.HellingerTwoCompetitor.eventProb_wrong_pair_le_two_mul_exp
#print axioms AssemblyP1.HellingerNoDecay.eventProb_wrong_eq_one_of_mem
