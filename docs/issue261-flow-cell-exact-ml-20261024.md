# Issue #261 bounded flow cell, exact-likelihood axis (2026-10-24)

Child of #255. Companion to the fixed-`N` binomial cell
`docs/issue261-flow-cell-acac-20261023.md` (branch
`research/261-flow-cell-Xy3YrTZ7lgb021RsyXwJHh-savage`, commit `41fbd3c`)
on the same source-faithful MB09 Sec. 6.2 instance; this note changes only
the likelihood axis. Exact-integer witness; verifier:
[`scripts/verify_261_flow_cell_exact_ml.py`](../scripts/verify_261_flow_cell_exact_ml.py).

## Fixed instance (shared with the fixed-`N` cell)

* Alphabet `A=0,C=1,G=2,T=3`; strands `ACA=(0,1,0)`, `CAC=(1,0,1)`,
  `TGT=(3,2,3)=rc(ACA)`, `GTG=(2,3,2)=rc(CAC)`; RC verified against the
  Watson-Crick complement in the verifier.
* Observed molecule support `verts={ACA,CAC}` (two RC classes, no palindromes);
  `readLen L=3`, `o_min=1`; complete `overlapEdges` graph: 8 edges (4 of length
  1, 4 of length 2); literal `isReducibleB` vacuous on this instance (checked),
  so the reduced graph equals the complete graph -- no reduction-ambiguity
  caveat applies here. (The literal predicate's general vacuity is separately
  Lean-audited in `Section62ReductionVacuityAudit`; the longer-overlap reading
  and a same-spelling reduction stay OPEN per
  `docs/section62-reduction-vacuity-20261012.md`.)
* Candidate objects: integer `BdFlow`s with zero-terminal `Feasible62`
  (`edgeLB=0`, `vertexLB=1`, signed-incidence balance `0` at both vertices),
  throughput `d` per molecule class. Terminal convention: `noTerminals`.

## Candidate class pinned for this cell (differs from the companion cell)

* **Flow vs spelled vs genome:** candidates are integer feasible *flows*
  (not restricted to spelled circuits or single circular genomes); the spelled
  visit vectors form a named sub-class. Truth admitted as the spelled
  2-circuit walk flow `(ACA->CAC->ACA)`, throughput `d*=(1,1)`.
* **Likelihood:** the EXACT iid multinomial core
  `E(d;x) = prod_i (d_i/T)^{x_i}` with `T = sum_i d_i`, sample `x=(2,1)`.
  The multinomial coefficient is constant across candidates (fixed `x`) and
  omitted; comparison is ranking-valid. Exact `Fraction` arithmetic.
* **Length universe:** ALL zero-terminal feasible flows (unbounded total mass).
  There is no external `N` and hence no binomial probability-domain exclusion:
  every throughput with `T>0` is comparable. This removes the companion cell's
  `d_i<=N` restriction caveat along this axis.
* Unobserved molecule coordinates fixed at `0` for all candidates (common
  factor; the support-adjudication convention choice itself stays OPEN).

## Proven statements (exact, finite)

1. **Truth candidate status.** Same as the companion cell: the spelled
   2-circuit uses maximal overlaps (len 2), satisfies `BidirectedCircuit`,
   visits both observed vertices; its walk flow is zero-terminal feasible with
   throughput `(1,1)`.
2. **Spelled-maximal (tie).** The spelled visit set visiting both vertices at
   `n<=4` is exactly `{(1,1),(2,2)}`; under `E(.;x)` both score `1/8`
   (`(1/2)^3`), so the truth is spelled-maximal (tied, not unique).
3. **Strict flow defeater.** The integer flow
   `f=(3->3 len1)+(0->1 len2)+(2->3 len2)` is zero-terminal feasible with
   throughput `(2,1)` (non-spelled) and scores `E=4/27>1/8`
   (`32/216>27/216`). Hence the spelled-maximal truth is **not** flow-maximal
   under the exact likelihood either.
4. **Inclusion premise checked finitely.** Both spelled visit vectors are
   realized by explicit feasible flows (`F_TRUTH` for `(1,1)`, its double for
   `(2,2)`), witnessing `spelledVisitSet_subset_image` on this cell. The
   Lean transfer lemmas (`flow_not_maximal_of_spelled_witness`,
   `spelled_truth_flow_not_maximal_of_spelled_witness` in
   `AssemblyP1.Section62SpelledFlowMaximality`, likelihood-independent) apply
   to the exact score `E` unchanged.

## Conclusion for the cell

Spelled-maximality does not imply flow-maximality under the exact multinomial
likelihood either, on the same reduction-vacuous genuine `o_min=1` bidirected
graph with a feasible spelled truth. The fixed-`N` failure is therefore not an
artifact of the binomial surrogate or its probability-domain restriction.
No positive maximality statement is transferred (positive statements do not
transfer across likelihoods without proof).

## What stays OPEN

General necessary-and-sufficient flow-maximality conditions, throughput-image
characterization, non-vacuous (same-spelling) transitive reduction, other RC
supports, the real LP relaxation, sample realizability at arbitrary overlap,
and the unobserved-coordinate convention all stay OPEN. #261 and #255 stay
open.
