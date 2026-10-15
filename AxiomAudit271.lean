import AssemblyP1.ConditionalVsOrdinaryMLSeparation
import AssemblyP1.ConditionalVsOrdinaryMLBoundary271
import AssemblyP1.W1W2SeparationCompatibility
import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.ConditionalBayesEImpliesB271

open AssemblyP1.ConditionalVsOrdinaryMLSeparation

-- Abstract separation witness (#271): the two recovery guarantees are
-- logically incomparable in one shared generative model.
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.condRecoveryCertain_iff
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.condPosterior_one_imp
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.condPosterior_of_fibre
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.separation_A_not_B
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.separation_B_not_A
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.condPosterior_E_certifies_wrong_r1
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.condPosterior_dataOnly
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.sideInfo_not_dataOnly
#print axioms AssemblyP1.ConditionalVsOrdinaryMLSeparation.posteriorSeq_A_r0_ne_posterior_A_r0

-- Tiny-table sanity regressions (#271): ties, zero-likelihood competitors, MAP vs ML.
#print axioms AssemblyP1.ConditionalVsOrdinaryMLBoundary271.tie_maximizer_posterior_not_certain
#print axioms AssemblyP1.ConditionalVsOrdinaryMLBoundary271.zero_likelihood_overlap
#print axioms AssemblyP1.ConditionalVsOrdinaryMLBoundary271.post_zero_B_r0_skew
#print axioms AssemblyP1.ConditionalVsOrdinaryMLBoundary271.map_ne_ml_nonuniform
#print axioms AssemblyP1.ConditionalVsOrdinaryMLBoundary271.prior_flips_MAP_not_ML

-- Historical W1/W2 (B)-side instantiation by reuse of merged theorems.
#print axioms AssemblyP1.W1W2SeparationCompatibility.w1_truth_not_maximizer_binomial
#print axioms AssemblyP1.W1W2SeparationCompatibility.w1_truth_not_maximizer_exact
#print axioms AssemblyP1.W1W2SeparationCompatibility.w2_truth_not_maximizer_binomial
#print axioms AssemblyP1.W1W2SeparationCompatibility.w2_truth_not_maximizer_exact

-- Genome-level adapter in the exact AssemblyP1 finite read model (#271):
-- normalized per-candidate read pmf, orbit-class prior, and the candidate-specific
-- latent-start information-feasibility predicate E built from the exact source
-- predicate SourceFaithfulIs.InformationFeasible; separation (A ∧ ¬B) and
-- converse (B ∧ ¬A).
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.p_sum_one
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.prior_sum_one
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.orbit_injective
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.informationFeasible_two_no_tripleRepeat
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.feasible_genOf_one
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E_one_00
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E_zero_00
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E_two_00
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E_not_dataOnly
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.sep_posteriorMass_one
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.sep_posteriorMass_one_excluded
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.sep_truth_not_ml
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.sep_ordinary_not_certain
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.separation_genome
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.conv_ml_unique
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.conv_ordinary_not_certain
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.converse_genome
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.postCandidate_sep
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.postCandidate_conv
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.map_ml_agree_uniform

-- General finite-candidate refinement of the (A)-boundary (#271 goal 5):
-- conditional recovery implies ordinary ML recovery exactly when the side
-- information is ML-sound; `E = MLMax` makes A and B coincide; the merged toy's
-- `sideInfo` is exactly *not* ML-sound.
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.condCertain_imp_E
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.condCertain_imp_MLMax_of_MLsound
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.condCertain_imp_MLMax_exists_of_MLsound
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.not_MLsound_of_witness
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.posteriorE_eq_one_imp
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.posteriorE_of_fibre
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.condCertain_iff
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.mlSound_EML
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.condCertain_EML_iff_unique
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.toy_sideInfo_not_MLsound
#print axioms AssemblyP1.ConditionalBayesEImpliesB271.genome_E_not_MLsound
