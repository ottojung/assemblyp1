# #284 single-dependent reevaluation: `Section62NonSpelledFlow.graph_reduction_vacuous_literal` (agent HxEMplt1)

Date (UTC): 2026-10-25. Base: `7ee3253955d96d609169dd5ee294ae6450441c87`
(signed, Good EDDSA 08AF2726; parent diff docs-only).
Isolated checkout: `/tmp/opencode/agent-HxEMplt1-issue284/repo`, branch
`agent/HxEMplt1-issue284`. No existing symbol redefined.

## Dependent reevaluated (exactly one)

`Section62NonSpelledFlow.graph_reduction_vacuous_literal`
— `AssemblyP1/Section62NonSpelledFlow.lean:583`.

- States `transitivelyReduced … graph1 = graph1` (old literal predicate is the
  identity on the `AAATT` witness graph), proved by `decide`.
- This is the single genuinely nontrivial case in the survival matrix: at
  `oMin = 1` the graph contains length-`1` edges, so unlike the full-overlap
  (`oMin = readLen - 1 = 2`) witnesses the corrected reduction is NOT the
  identity here.

## Verdict: SURVIVES (as audited-model fact; corrected analogue nontrivial)

- Old-predicate identity fact stands unchanged (requirement 1: old predicate
  preserved as the model being audited). No re-proof needed; `decide`
  certificate untouched.
- Corrected counterpart is kernel-checked alongside, not in place of it:
  `Section62ReductionDependencyAudit.nonspelled_reduction_spelling_eq`
  (`AssemblyP1/Section62ReductionDependencyAudit.lean:103`) proves
  `transitivelyReducedSpelling … graph1 = reducedList` by `decide` — the
  sixteen length-`1` edges spelled through an observed read are removed,
  leaving the longer-overlap `reducedList`.
- The flow certificates transfer across that graph equality
  (`star21_feasible62_spelling_reduced` :113,
  `truth_feasible62_spelling_reduced` :122,
  `star31_feasible62_spelling_reduced` :131), so the non-spellable
  countermodel survives under the corrected reduction.
- Consistent with the pre-existing classification in
  `docs/section62-reduction-survival-matrix-284.md:128` (SURVIVES) and
  `docs/section62-reduction-dependent-reevaluation-284.md:39` (survives).
  This note adds an independent file:line-backed re-verification of that row;
  it changes no Lean symbol and introduces no `sorry`/`admit`/`axiom`.

## Validation performed in this pass

- `git verify-commit 7ee32539`: Good EDDSA 08AF2726 (Otto Jung).
- `git diff 37c1d11..7ee32539 --stat`: docs-only +56 lines (unchanged from
  prior checkpoint).
- `python3 scripts/verify_284_myers_ideal_scope.py`: PASS.
- `python3 scripts/verify_284_reduction_survival_matrix.py`: PASS
  (10 direct + 5 transitive SURVIVES, 0 MUST-BE-REPROVED).
- `python3 scripts/verify_284_spellchain_window_transport.py`: PASS.
- `python3 scripts/verify_284_ml_likelihood_boundary.py`: PASS.
- `python3 scripts/check-research-docs.py`: PASS.
- `git diff --check` on this note: clean.
- Scoped `lake build` NOT rerun here (no `.lake`/Mathlib cache in this fresh
  isolated clone); prior checkpoint records scoped build of
  `AssemblyP1.Section62MyersIdealTransitivity` PASS with kernel replay +
  `#print axioms` on the same head.
