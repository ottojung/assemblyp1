import AssemblyP1.DihedralOrbitQuotient

/-!
# Independent axiom audit for the dihedral orbit quotient (#269)

This audits the exact statements of `AssemblyP1/DihedralOrbitQuotient.lean`, the
conditional kernel-checked extension of the merged Bayes/MAP optimality
certificate from rotation orbits to the full dihedral (rotation +
reverse-complement) orbit quotient, together with the precise obstruction that
makes the RC-invariance hypothesis necessary.

It does **not** claim:

* an RC or dihedral quotient for the *raw oriented* read pmf without the
  RC-invariance hypothesis — that is refuted here by
  `Obstruction.readPmf_not_rcInvariant` / `Obstruction.no_dihedral_descent`;
* per-truth success monotonicity (refuted by the merged
  `AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops`);
* the MB09 fixed-`N` product-binomial pseudo-likelihood or the §6.2
  feasible-flow objective (`AssemblyP1.Section62FlowGenomeSeparation`);
* truth-dependent event-conditional inference (Antonina #266;
  `AssemblyP1.ConditionalIdentifiability`).

Every audited theorem must depend only on `propext`, `Classical.choice`, and
`Quot.sound` (the CI axiom audit enforces this allow-list library-wide).
-/

#print axioms AssemblyP1.DihedralOrbitQuotient.rcWord_rotWord
#print axioms AssemblyP1.DihedralOrbitQuotient.rcWord_involutive
#print axioms AssemblyP1.DihedralOrbitQuotient.rcOrbit_involutive
#print axioms AssemblyP1.DihedralOrbitQuotient.orbitScore_rcOrbit
#print axioms AssemblyP1.DihedralOrbitQuotient.dihedralScore_sum_one
#print axioms AssemblyP1.DihedralOrbitQuotient.dihedral_map_success_monotone
#print axioms AssemblyP1.DihedralOrbitQuotient.uniformDihedralPrior_sum_one
#print axioms AssemblyP1.DihedralOrbitQuotient.uniform_dihedral_prior_ML
#print axioms AssemblyP1.DihedralOrbitQuotient.dihedral_certificate
#print axioms AssemblyP1.DihedralOrbitQuotient.dihedral_tie_all_optimal
#print axioms AssemblyP1.DihedralOrbitQuotient.readPmf_rotInvariant
#print axioms AssemblyP1.DihedralOrbitQuotient.readPmf_dihedral_map_success_monotone
#print axioms AssemblyP1.DihedralOrbitQuotient.readPmf_uniform_dihedral_prior_ML
#print axioms AssemblyP1.DihedralOrbitQuotient.readPmf_dihedral_certificate
#print axioms AssemblyP1.DihedralOrbitQuotient.symReadPmf_rotInvariant
#print axioms AssemblyP1.DihedralOrbitQuotient.symReadPmf_rcInvariant
#print axioms AssemblyP1.DihedralOrbitQuotient.symReadPmf_sum_one
#print axioms AssemblyP1.DihedralOrbitQuotient.sym_dihedral_map_success_monotone
#print axioms AssemblyP1.DihedralOrbitQuotient.sym_uniform_dihedral_prior_ML
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.comp2_involutive
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.mult_S3_w00
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.mult_rcS3_w00
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.readPmf_S3_w00
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.readPmf_rcS3_w00
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.readPmf_not_rcInvariant
#print axioms AssemblyP1.DihedralOrbitQuotient.Obstruction.no_dihedral_descent
