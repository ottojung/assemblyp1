# #284 independent review of e4bd325 + this-run kernel replay (agent-t2CtGeZ4)

Scope: review-only increment. No Lean definitions changed; `isReducibleB` /
`transitivelyReduced` (old vacuous predicate, `AssemblyP1/Section62BidirectedFlow.lean:182,223`)
untouched. No #261 flows modified.

## Independent review of e4bd325 (agent-iNShKvQVkRf22UEqpsjk31)

The recovered diagnostic `docs/section62-ml-likelihood-transport-boundary-284.md` +
`scripts/verify_284_ml_likelihood_boundary.py` (branch
`agent/iNShKvQVkRf22UEqpsjk31-issue284`, commit `e4bd325`) is SOUND and correctly
scoped:

- Witness G=2, L=2 (`S0 = 00`, `S1 = 11`, `rep2 : 11 ↦ 00`) recomputed by the
  Python mirror in this run: `classCount` collides (`{(0,0): 2}` both sides),
  exact uniform-start oriented likelihoods are `1` vs `0`. The non-transport
  claim follows by the same contradiction on `φ` as the Lean endpoint
  `exactLikelihood_not_factors_throughput`. No silent redefinition: the doc
  explicitly states the old symbols are preserved as the audited model.
- Modeling decision (a)/(b) is correct: throughput-likelihood SURVIVES as the
  §6.2 flow objective (transport via `maximal_image_iff` /
  `oriented_maximal_iff_image` on main); exact oriented genome likelihood is
  REJECTED as a flow objective (proved non-transport, stays reference model).
- Finite positive reduction regression is indeed already on main (AAATT instance
  in `Section62SpellingReductionCandidate` + survival-matrix verifier step 4);
  e4bd325 adds no reduction code — verified by diff (`docs/` + `scripts/` only).

## This-run validation (isolated clone, branch `agent/t2CtGeZ4unZ0nV4rwO4Hn3-issue284`, base `origin/main 234f348`)

- `python3 scripts/verify_284_reduction_survival_matrix.py` → PASS (10 direct +
  5 transitive dependents, all SURVIVES, 0 MUST-BE-REPROVED; old predicate
  vacuous; corrected `transitivelyReducedSpelling` removes the direct regression
  edge, keeps both legs).
- `python3 scripts/verify_284_spellchain_window_transport.py` → PASS.
- Python mirror of `verify_284_ml_likelihood_boundary.py` (from `e4bd325`) →
  PASS (likelihoods 1 vs 0, equal class vectors).
- `python3 scripts/check-research-docs.py` → exit 0 (only pre-existing broken
  local-link notices in unrelated docs).
- Lean kernel replay (`lake env lean`, toolchain `v4.34.0`, shared Mathlib
  object cache, read-only):
  - `AssemblyP1/Section62FlowGenomeSeparation.lean` → elaborates clean;
    `#print axioms` for `no_flow_objective_eq_likelihood` and
    `section62_flow_objective_ne_genome_likelihood` ⊆
    `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
  - `AssemblyP1/Section62SpellingReductionCandidate.lean` → elaborates clean;
    `removable_edge_detour_in_graph` ⊆ `{propext, Classical.choice, Quot.sound}`,
    `regression_edge_is_removed` / `regression_legs_survive` ⊆ `{propext}`.
  - `grep sorry/admit/native_decide` on the replayed modules + `Section62BidirectedFlow`
    → clean (only prose mention of `sorryAx`).
- `grep isReducibleB/transitivelyReduced` confirms old symbols intact and still
  referenced by the vacuity audit (`Section62ReductionVacuityAudit`) and the
  dependency audit (`Section62ReductionDependencyAudit`).

## Survive vs must-be-reproved (unchanged from survival matrix, confirmed)

- SURVIVES (15/15 classified): all 10 direct + 5 transitive §6.2 dependents —
  none relied on the vacuous `transitivelyReduced` being nontrivial; the
  corrected `transitivelyReducedSpelling` is a separate symbol, so no existing
  proof breaks.
- MUST-BE-REPROVED: 0.
- REJECTED (modeling, not a lemma): exact oriented genome likelihood as a §6.2
  flow objective (kernel-checked non-transport above).

## Remaining for req 7

Exact-head CI (`ci.yml`, `documents.yml`, `slides/pages`) green + multiple
independent scientific reviewers still open. This increment supplies the missing
this-run kernel replay + axiom audit; it does not claim #261 completion. Issue
stays open.
