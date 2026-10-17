import AssemblyP1.GenomeOrbitAdapter

/-!
# Independent axiom audit for the assembly-specific MAP orbit adapter (#269)

This audits the exact statements that connect the merged finite-Bayes/MAP
decision theorem (`AssemblyP1.FiniteBayesDecision`, PR #174) and its exact iid
`n → n+1` monotonicity bridge (`AssemblyP1.IidMapMonotonicity`, PR #193) to the
concrete AssemblyP1 circular oriented read model
(`AssemblyP1.GenomeOrbitAdapter`, PR #200).  It does **not** reprove any of the
merged generic finite-sum lemmas, and it does **not** claim:

* the §6.1 product-binomial versus exact-iid distinction as a *separation from
  §6.2 flow* (that is `AssemblyP1.Section62FlowGenomeSeparation`, PR #286);
* the throughput-image classification of #261
  (`AssemblyP1.Section62SpelledFlowImageRefutation`);
* truth-dependent coverage conditioning (Antonina #266; only the unconditional
  separation `CoverageConditional.conditionalSuccess_univ_eq` is audited here);
* a reverse-complement or dihedral orbit quotient (the adapter quotients by
  rotation only; `quotient_likelihood_well_defined_iff` states the exact
  invariance hypothesis an RC quotient would need).

Every audited theorem must depend only on `propext`, `Classical.choice`, and
`Quot.sound` (the CI axiom audit enforces this allow-list library-wide).
-/

#print axioms AssemblyP1.GenomeOrbitAdapter.sum_mult
#print axioms AssemblyP1.GenomeOrbitAdapter.readPmf_sum_one
#print axioms AssemblyP1.GenomeOrbitAdapter.readPmf_rotWord
#print axioms AssemblyP1.GenomeOrbitAdapter.orbitReadPmf_sum_one
#print axioms AssemblyP1.GenomeOrbitAdapter.quotient_likelihood_well_defined_iff
#print axioms AssemblyP1.GenomeOrbitAdapter.orbit_map_success_monotone
#print axioms AssemblyP1.GenomeOrbitAdapter.uniformOrbitPrior_sum_one
#print axioms AssemblyP1.GenomeOrbitAdapter.orbitSize_pos
#print axioms AssemblyP1.GenomeOrbitAdapter.sum_orbitSize
#print axioms AssemblyP1.GenomeOrbitAdapter.spellingPushforwardPrior_sum_one
#print axioms AssemblyP1.GenomeOrbitAdapter.spellingPushforward_eq_uniform_iff_constant_orbitSize
#print axioms AssemblyP1.GenomeOrbitAdapter.uniform_orbit_prior_ML
#print axioms AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_one
#print axioms AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_two
#print axioms AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops
#print axioms AssemblyP1.GenomeOrbitAdapter.CoverageConditional.conditional_MAP_optimal
#print axioms AssemblyP1.GenomeOrbitAdapter.CoverageConditional.conditionalSuccess_univ_eq
#print axioms AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff
#print axioms AssemblyP1.GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial
