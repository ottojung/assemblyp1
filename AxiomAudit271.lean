import AssemblyP1.ConditionalVsOrdinaryMLSeparation
import AssemblyP1.ConditionalVsOrdinaryMLBoundary271
import AssemblyP1.W1W2SeparationCompatibility
import AssemblyP1.W1W2RcOrientedRepresentation271
import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.ConditionalBayesEImpliesB271
import AssemblyP1.InformationFeasibleRotation271
import AssemblyP1.ConditionalVsMLFullReadSet271

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

-- W1/W2 reverse-complement molecule vs oriented read-string representation
-- (#271 goal 3): the collapse cls is non-injective and RC-invariant, so the
-- molecule likelihood is a function of a strict quotient of the oriented
-- read-string observable.
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.rc_involutive
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.cls_rc
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.cls_not_injective
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.exists_rc_pair_same_class
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.window2_ne_window3
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.window3_eq_rc_window2
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.window_cls_eq
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.molCount_map_rc
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.obs_eq_molCount
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.orientedReads_ne_rc
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.molCount_orientedReadsRc_eq
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.lik_rc_blind
#print axioms AssemblyP1.W1W2RcOrientedRepresentation271.rc_vs_oriented_verdict

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

-- Rotation invariance of the source information-feasibility predicate `I_s`
-- (#271): `InformationFeasible` commutes with rotating the genome and the
-- placement set, so the latent-start predicate `E` descends to rotation-orbit
-- classes; the orbit-level (A ∧ ¬B) separation follows.
#print axioms AssemblyP1.SourceFaithfulIs.rotGenome
#print axioms AssemblyP1.SourceFaithfulIs.informationFeasible_rotGenome
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.EGenome_rotGenome
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.toGenome_rotWord
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.E_rotWord
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.Eorb
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.Eorb_orbit
#print axioms AssemblyP1.ConditionalVsMLGenomeAdapter271.separation_orbit

-- Full-read-set weighted placement mass for the #271 witness (#271 open item 2):
-- the literal historical event `HistoricalInformationFeasibleLiteral` is a
-- concrete `ConditionalIdentifiability.PlacementModel`; at the full read set
-- `Y1` the weighted placement mass is supported on the truth orbit and recovery
-- is certain, while the single-read observation carries zero literal mass and
-- the witness's `InformationFeasible` placement is not literal.
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.coverage_window_mem
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.coverage_iff
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullFeasible_zero
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullDecode_correct
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullModel
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullJoint_eq_zero_of
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullJoint_Y1_zero_zero
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullJoint_Y1_zero_two
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullJoint_Y1_pos_one
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullReadSet_support
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullReadSet_orbit_mass_eq_total
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullReadSet_posterior_eq_one
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.witness_placement_not_literal
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullJoint_singleton_eq_zero
#print axioms AssemblyP1.ConditionalVsMLFullReadSet271.fullReadSet_boundary
