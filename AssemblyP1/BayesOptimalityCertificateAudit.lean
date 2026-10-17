import AssemblyP1.BayesOptimalityCertificate

/-!
# Independent axiom audit for the finite Bayes/MAP optimality certificate (#269)

This audits the exact statements of `AssemblyP1/BayesOptimalityCertificate.lean`,
the necessary-and-sufficient certificate closing Antonina #269 target B and the
posterior-one boundary of target D for the concrete AssemblyP1 read model.  It
does **not** reprove any merged generic finite-sum lemma, and it does **not**
claim:

* the §6.1 product-binomial versus exact-iid distinction as a separation from
  §6.2 flow (`AssemblyP1.Section62FlowGenomeSeparation`);
* the throughput-image classification of #261
  (`AssemblyP1.Section62SpelledFlowImageRefutation`);
* truth-dependent coverage conditioning (Antonina #266;
  `AssemblyP1.ConditionalIdentifiability`) — the certificate here is
  unconditional prior-average optimality;
* a reverse-complement or dihedral orbit quotient (the orbit instantiation uses
  rotation classes only);
* per-truth success monotonicity (that is refuted by the merged
  `AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops`).

Every audited theorem must depend only on `propext`, `Classical.choice`, and
`Quot.sound` (the CI axiom audit enforces this allow-list library-wide).
-/

#print axioms AssemblyP1.BayesOptimalityCertificate.pointwiseMAP_imp_bayesOptimal
#print axioms AssemblyP1.BayesOptimalityCertificate.bayesOptimal_imp_pointwiseMAP
#print axioms AssemblyP1.BayesOptimalityCertificate.pointwiseMAP_iff_bayesOptimal
#print axioms AssemblyP1.BayesOptimalityCertificate.not_pointwiseMAP_imp_strict_loss
#print axioms AssemblyP1.BayesOptimalityCertificate.pointwiseMAP_forces_strictMax
#print axioms AssemblyP1.BayesOptimalityCertificate.strictMax_unique
#print axioms AssemblyP1.BayesOptimalityCertificate.posterior_eq_one_iff_singleton_support
#print axioms AssemblyP1.BayesOptimalityCertificate.posterior_ne_one_iff_not_singleton_support
#print axioms AssemblyP1.BayesOptimalityCertificate.iid_certificate
#print axioms AssemblyP1.BayesOptimalityCertificate.orbit_certificate
#print axioms AssemblyP1.BayesOptimalityCertificate.orbit_posterior_eq_one_iff_singleton_support
#print axioms AssemblyP1.BayesOptimalityCertificate.TieWitness.both_optimal
#print axioms AssemblyP1.BayesOptimalityCertificate.TieWitness.policies_distinct
#print axioms AssemblyP1.BayesOptimalityCertificate.StrictLossWitness.not_pointwise
#print axioms AssemblyP1.BayesOptimalityCertificate.StrictLossWitness.strict_loss
