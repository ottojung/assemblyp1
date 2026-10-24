# §6.2 exact ML-likelihood transport boundary (#284, delegated check)

Status: diagnostic only. No normative definitions changed. No PR #389 duplication.

## Question

Does the spelling-preserving §6.2 transitive reduction transport the exact
ML likelihood for the source-faithful graph model, i.e. is the exact
uniform-start oriented-window likelihood a function of the physical
§6.2 throughput likelihood?

## Answer: NO — smallest counterexample already kernel-checked on main

`AssemblyP1.Section62FlowGenomeSeparation` (Antonina #269 landing, present on
`origin/main` at `234f348`):

- Candidates: circular genomes `S0 = 00`, `S1 = 11` (`ZMod 2 → Fin 2`), `G=2, L=2`.
- Molecule-class map `rep2`: `11 ↦ 00`, else identity (MB09 §4.1 one representative
  per RC class).
- Visit vector `classCount S v` = number of starts whose window has representative `v`.
- Sample: one oriented read `x0 = [w00]`.
- Exact likelihood `exactLikelihood 1 S x0 = ∏ᵢ readPmf S (x0 i)`,
  `readPmf S w = mult S w / G`.

Kernel endpoints (all `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`,
no `sorryAx`):

- `classCount_S0_eq_S1 : classCount S0 = classCount S1` (by `decide`).
- `likelihood_S0 : exactLikelihood 1 S0 x0 = 1` (both windows spell `00`).
- `likelihood_S1 : exactLikelihood 1 S1 x0 = 0` (no window spells `00`).
- `likelihood_S0_ne_S1`.
- `exactLikelihood_not_factors_throughput`:
  `¬ ∃ φ, ∀ S, exactLikelihood 1 S x0 = φ (classCount S)`.
- `section62_flow_objective_ne_genome_likelihood` (headline).
- `no_flow_objective_eq_likelihood` (abstract form for any `Θ` with the same
  collision).
- Bridge `classCount_eq_visits : classCount S v = Spelling.visits rep2 ...`
  (`rfl`), so `classCount` IS the §6.2 visit/throughput vector via
  `Section62SpelledFlowAdapter.throughput_eq_visits`.

Hence no score of the form `score ∘ Θ` with `Θ = classCount/throughputVec`
can equal the exact oriented likelihood. This is the smallest case (`G=2`):
any RC-collapsed throughput loses orientation, while the oriented model keeps it.

## What DOES transport (scoped, conditional)

`AssemblyP1.Section62SpellChainWindowTransport`:

- `reduction_preserves_language_windows`: if `spellChain … es = spellDirect …`,
  then `windows L (spellChain …) = windows L (spellDirect …)` (rewrite only).
- `spellChain_eq_spellWalk` (bridge, needs `e.len ≤ (toList e.sy).length`).
- `genuineChain_visited_dominated`: visited reads are a SUB-multiset of the
  window multiset (`Dominates`), strict in general
  (`Section62VisitWindowBridge.witness_bound_strict`, seam window `34120`).

Consequence: the CONDITIONAL uniform-start ordered-product likelihood
`∏ᵢ (M(uᵢ)/n)` with `M` = window multiplicity of the spelled word is invariant
under a spelling-preserving detour (equal multisets ⇒ equal products). This is
a statement about the spelled-word window object, NOT about realized physical
visits or §6.2 `throughputVec`: visits are only dominated, and the RC quotient
additionally collapses orientation (`Section62ObservedMoleculeCount`,
`Section62GlobalSkippedBridge`). `Section62OrientedMLClassification` explicitly
scopes its classification to throughput-factoring scores and excludes the exact
oriented genome likelihood (#269 separation).

## Precise kernel-checkable route for the failure (no new Lean needed)

1. `decide` both `mult_S0_w00 = 2`, `mult_S1_w00 = 0` (already in module).
2. `decide` `classCount_S0_eq_S1`.
3. Rewrite `likelihood_S0/S1` via `readPmf` unfolding + `norm_num`.
4. `exactLikelihood_not_factors_throughput` by contradiction on `φ`.

Python mirror of the arithmetic (this diagnostic): `scripts/../docs` check
below recomputes `M/n` products `1` vs `0` with equal class vectors `(2,0,0,…)`.

## Validation in this invocation (isolated checkout, no shared-tree edits)

- `python3 scripts/check-research-docs.py` → pass.
- `python3 scripts/verify_284_spellchain_window_transport.py` → pass.
- `python3 scripts/verify_284_reduction_survival_matrix.py` → pass
  (10 direct + 5 transitive SURVIVES, 0 MUST-BE-REPROVED).
- `grep sorry/admit/axiom/native_decide` on the two modules → clean
  (only prose mention of `sorryAx`).
- Lean kernel replay / axiom-audit NOT rerun in the prior invocation (no warm
  Mathlib cache then; prior handoffs record green whole-library `leanchecker` +
  axiom audit on merged heads; not claimed as that-run evidence).
- Addendum 2026-10-24 (agent-Hehlv9XnJBj6iL55xyBzVe-paternal, isolated clone at
  `origin/main` 234f348 + this branch): `lake build
  AssemblyP1.Section62FlowGenomeSeparation
  AssemblyP1.Section62SpellingReductionCandidate
  AssemblyP1.Section62SimultaneousReduction` → **Build completed successfully
  (8932 jobs)**. `#print axioms` endpoints: `no_flow_objective_eq_likelihood`,
  `section62_flow_objective_ne_genome_likelihood`,
  `exists_irreducible_expansion`, `reduction_preserves_language` all depend
  only on `{propext, Classical.choice, Quot.sound}`; `cascade_spell` on
  `{propext}`; no `sorry`/`admit`/`axiom`/`native_decide` introduced
  (this diagnostic touches no `AssemblyP1/` source). Standalone `leanchecker`
  replay attempted but exceeded the invocation time budget; the `lake build`
  elaboration above is itself a kernel check of all three modules.

## Modeling decision (recovered 2026-10-24, agent-iNShKvQVkRf22UEqpsjk31)

Recovered from prior isolated diagnostic (agent-yWVrQ8jtwb1wIMzNcwPDux-awful,
local commit 76326b7, never merged); rerun on verified issue-owned branch
`agent/iNShKvQVkRf22UEqpsjk31-issue284` at `origin/main` 234f348.

Decision recorded for #261/#262 handoff:

- (a) SURVIVES for §6.2 flow work: the RC-collapsed throughput likelihood as
  the §6.2 objective. Transport holds by `maximal_image_iff` /
  `oriented_maximal_iff_image` (already on main). #261/#262 must use this
  objective, with the explicit caveat that it is NOT the exact oriented
  genome likelihood.
- (b) REJECTED as a §6.2 flow objective: the exact oriented genome likelihood.
  `exactLikelihood_not_factors_throughput` + `section62_flow_objective_ne_genome_likelihood`
  (kernel-checked on main, G=2 witness above) prove no throughput-factoring
  §6.2 score can equal it. It stays the reference model for stating the
  separation, not a transport target.
- Finite positive regression for the corrected spelling-preserving reduction
  itself is already merged on main (AAATT instance in
  `Section62SpellingReductionCandidate` + `verify_284_reduction_survival_matrix.py`
  step 4: old predicate vacuous, corrected predicate removes the direct edge
  while keeping both detour legs); this increment adds no new reduction code
  and does not redefine `isReducibleB`/`transitivelyReduced`.

## Remaining blocker

The exact ML-likelihood transport to §6.2 feasible flows is therefore NOT a
missing proof — it is a PROVED NON-TRANSPORT for the oriented model. What
remains open is a modeling decision, not a lemma: either (a) adopt the
RC-collapsed throughput likelihood as the §6.2 objective (then transport holds
by `maximal_image_iff`/`oriented_maximal_iff_image` but the objective is not
the exact oriented genome likelihood), or (b) keep the exact oriented
likelihood (then no throughput-factoring §6.2 flow objective can equal it, per
above). Requirement (7) breadth (independent reviews, exact-head CI/docs/slides)
is also still open per prior handoffs.
