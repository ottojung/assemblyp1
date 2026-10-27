# Issue #263 reconciliation: separable-convex Graver certificate

Repository: `https://github.com/ottojung/assemblyp1`

The existing artifact at commit `fe9f377b` on
`agent/3189515c4cb7/issue263-separable-convex-graver` provides a conditional
necessary-and-sufficient Graver optimality theorem in
`AssemblyP1/SeparableConvexGraver.lean`. It proves the sign-compatible
superadditivity step, the finite-box optimizer equivalence under an explicit
Graver-decomposition hypothesis, and interior discrete-convexity instances for
the multinomial and fixed-external-total binomial costs. The source explicitly
leaves zero-probability endpoints outside those instances and separates pure
ML from any penalized objective.

Validation performed against the repository's pinned toolchain:

* `lake build AssemblyP1.SeparableConvexGraver AssemblyP1.SeparableConvexGraverAudit` — pass.
* The audit reports only `[propext, Classical.choice, Quot.sound]` for each
  audited endpoint, including the conditional optimizer equivalence and
  likelihood convexity lemmas.
* `git diff --check origin/main...HEAD` — pass for the existing artifact.

Reconciliation found later related #263 additions on a separate remote branch,
including `ray_unit_mem_box`, `multiplier_unit_feasible_improving`, and
`ray_unit_mem_fiber` (commits `5133392f` and `bfd1a387`). They are not ancestors
of the artifact branch audited here. They complement the certificate with the
unit-step ray feasibility bridge. They were inspected but not cherry-picked or
claimed as validated in this checkout. The base theorem's optimizer result is
conditional on conformal decomposition and does not require that ray lemma.

The live board's newest comments could not be read in this environment because
the GitHub CLI (`gh`) is unavailable. The branch, artifact, and commit above
were verified directly from the remote. The issue should remain open for
independent review and reconciliation of the separate unit-ray additions and
fresh full CI; the conditional core theorem itself is locally kernel-checked.
