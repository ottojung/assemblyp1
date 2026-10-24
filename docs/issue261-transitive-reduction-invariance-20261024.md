# Issue #261 OPEN-4 note: transitive-reduction invariance probe (2026-10-24)

Bounded increment only. Does not duplicate the AGA/CTC or ACA/CAC verifiers.
Candidate classes, truth admission, likelihood, and length universe are as
stated in `docs/issue261-general-bidirected-flow-ml.md`; this note only
addresses the transitive-reduction axis (OPEN-4).

## Claims (exact, checkable)

1. **Literal `isReducibleB` is vacuous.** The system
   `0<l1, 0<l2, l1<L, l2<L, l1<l, l2<l, l1+l2-L=l` with `l<L` is
   unsatisfiable: `l1<l, l2<l` gives `l1+l2<2l`, while the composition law
   gives `l1+l2=l+L>2l`. Exhaust over `L=2..8` finds zero witnesses.
   Consequence: the literal reduction removes nothing, hence is trivially
   ML-invariant (vacuous invariance, not a structural criterion).
2. **Longer-only reading (`isReducibleLongerB`) is not ML-invariant without a
   spelling-equality side condition.** Witness at `L=4`, verts
   `AAAC, ACCA, CAAA`: direct overlap `AAAC->CAAA` is length 1 and spells
   `AAACAAA`; legs `AAAC->ACCA`, `ACCA->CAAA` have overlaps `(2,2)` and spell
   `AAACCAAA`. Both legs are strictly longer, so the longer reading deletes
   the direct edge, but the replacement spells a different molecule. Deleting
   it changes the spelled language and hence the feasible spelled set.
3. **Status.** OPEN-4 stays OPEN: neither reading yields a
   necessary-and-sufficient ML maximality condition. Result (1) is a checked
   lemma; result (2) is a rigorous small-instance counterexample to naive
   invariance under the longer reading. A Myers-2005-style
   spelling-preserving reduction with signed-endpoint compatibility is the
   natural next step, out of scope here.

## Artifact

- `scripts/verify_261_transitive_reduction_invariance.py`: exact
  integer/string arithmetic; exit 0 = all checks pass.
