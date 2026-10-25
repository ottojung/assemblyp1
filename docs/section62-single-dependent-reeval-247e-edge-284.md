# #284 single-dependent reevaluation: `Section62VariableOverlap247e.edgeAAB_BAB_not_reducibleB` (agent pLEqIhE3dR8hcu2U8Sn4cg)

Date (UTC): 2026-10-25. Base: `a2306d6fb54dd31691e9b5839502d74975ce95c0`
(parent `7ee3253955d96d609169dd5ee294ae6450441c87`, signed, Good EDDSA 08AF2726).
Isolated checkout: `/tmp/opencode/agent-pLEqIhE3dR8hcu2U8Sn4cg-284/repo`, branch
`agent/pLEqIhE3dR8hcu2U8Sn4cg-issue284` tracking `origin/agent/HxEMplt1-issue284`.
No existing symbol redefined; no Lean file touched.

## Dependent reevaluated (exactly one)

`Section62VariableOverlap247e.edgeAAB_BAB_not_reducibleB`
— `AssemblyP1/Section62VariableOverlap247e.lean:132`.

- States `Section62Flow.isReducibleB … edgeAAB_BAB = false` (old literal
  predicate is `false` on the overlap-`1` edge `AAB → BAB`), proved by `decide`.
- The old predicate (`Section62BidirectedFlow.lean:182`) demands
  `0 < len₁ < e.len ∧ 0 < len₂ < e.len`; here `e.len = 1`, so the bound is
  arithmetically unsatisfiable. The theorem is a pure-arithmetic audited-model
  fact; no re-proof needed.

## Verdict: SURVIVES (as audited-model fact; corrected predicate is TRUE here)

- Old-predicate `= false` fact stands unchanged (requirement 1: old predicate
  preserved as the model being audited). `decide` certificate untouched.
- This dependent is the mirror image of the previously reevaluated nontrivial
  case: under the corrected spelling-preserving reduction
  (`Section62SpellingReductionCandidate.isReducibleSpellingB`, :181) this edge
  **is** reducible. Independent check in this pass (replicating the corrected
  predicate over `strandsOf rc readVerts`, `readLen = 3`, `oMin = 1`) finds the
  unique witness `m = ABA`, `l₁ = l₂ = 2`: genuine overlaps
  (`suf AAB 2 = AB = pre ABA 2`, `suf ABA 2 = BA = pre BAB 2`),
  `1 ≤ 2`, composition law `2 + 2 = 3 + 1`. The overlap genuineness and the
  spelling identity `AABAB` are already kernel-checked alongside as
  `edgeAAB_BAB_longer_witness` (:146, `decide`), and the repository's
  longer-overlap reading agrees (`edgeAAB_BAB_reducibleLonger = true`, :138).
  `ABA` is observed both directly (`readVerts`, :114; `ABA_is_observed`, :250)
  and as `rc BAB` (`ABA_eq_rc_BAB`, :256).
- So the row keeps its matrix verdict SURVIVES, with the sharpened reading:
  the old identity-fact survives *as a fact about the audited model*, while the
  operative corrected reduction removes this edge — exactly the
  finite-positive-regression behavior requirement (4) needs.
- Consistent with `docs/section62-reduction-survival-matrix-284.md:125`
  (SURVIVES; "the corrected predicate is `true` here") and the sibling rows
  `:278`/`:309` (`D_full`/`S_full_spelled_feasible62`, full-overlap
  `fullOverlapMin = 2` graphs, SURVIVES via `fullOverlap_not_reducible` +
  general transfer — not re-verified here, left for later passes).
- Changes no Lean symbol; introduces no `sorry`/`admit`/`axiom`.

## Validation performed in this pass

- `git verify-commit HEAD~1` (7ee32539): Good EDDSA 08AF2726 (Otto Jung);
  `HEAD` (a2306d6) unsigned docs-only note, as handed off.
- `git ls-remote https://github.com/ottojung/assemblyp1.git`: HEAD `234f3480`,
  branch `agent/HxEMplt1-issue284` at `a2306d6` — matches checkout.
- `python3 scripts/verify_284_reduction_survival_matrix.py`: PASS
  (10 direct + 5 transitive SURVIVES, 0 MUST-BE-REPROVED).
- `python3 scripts/verify_284_myers_ideal_scope.py`: PASS.
- Independent corrected-predicate recomputation on the 247e instance: exactly
  one witness `(ABA, 2, 2)`; old-predicate bounds unsatisfiable. PASS.
- `lake env lean AssemblyP1/Section62VariableOverlap247e.lean` (shared-cache
  checkout `/workspace/assemblyp1`, read-only typecheck): EXIT 0; `#print
  axioms` output as committed in-file.
- `python3 scripts/check-research-docs.py`: PASS.
- `git diff --check` on this note: clean.
- Full `lake build` NOT rerun (no `.lake`/Mathlib cache in fresh isolated
  clone); scoped kernel evidence above plus prior checkpoint's scoped build
  PASS on the same Lean head.
