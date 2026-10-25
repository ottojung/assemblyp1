# Issue #261: transitive-reduction scope cell (AAT/TAA, L=3, o_min=1)

## Candidate class (fixed; graph varied)

- (F) Integer edge-multiplicity flows, edge lower bound 0, vertex throughput
  lower bound 1, zero signed-incidence balance, zero terminal usage,
  multiplicities 0..2, over the same 4 RC-completed strands (AAT/TAA/ATT/TTA).
- Two graphs: COMPLETE (all 10 o_min=1 overlap edges, the audited parent
  graph) vs REDUCED (MB09-style transitive reduction keeping only the 4
  maximal-overlap L-1=2 edges AAT->ATT->TTA->TAA->AAT). Every dropped
  overlap-1 edge has a 2-step overlap->=1 witness path (machine-checked in
  the verifier, T1), so the reduction is genuine: 10 -> 4 edges.
- Likelihoods: fixed-N (N=4) product-binomial core and exact variable-length
  multinomial, same sample x=(1,2) and box universe convention as the
  likelihood-sensitivity cell. Truth (2,2) is admitted (spelled, feasible)
  under both graphs.

## Result

- Complete: 78-image census; fixed-N winner {(1,3)} K=81; exact winners
  {(1,2),(2,4)} K=4/27 (disjoint -- reproduces the parent sensitivity cell).
- Reduced: exactly 4 images {(1,3),(2,2),(3,1),(4,4)}; fixed-N winner {(1,3)}
  K=81; exact winner {(1,3)} K=9/64. The likelihood-sensitivity VANISHES.
- Hence transitive reduction is NOT a neutral preprocessing step for ML
  maximality on this cell: it changes the exact-likelihood answer from
  {(1,2),(2,4)} to {(1,3)}. Any future maximality criterion must therefore
  state whether the graph is complete at o_min or transitively reduced;
  results proved on one do not transfer to the other without an explicit
  inclusion/preservation argument.
- Truth (2,2): Kfix=64 < 81; Kex=1/8 below both exact maxima (4/27 complete,
  9/64 reduced). Maximal under neither objective on either graph.

## Reproduction

Run `python3 scripts/verify_261_transitive_reduction_scope.py` (exit 0 on
PASS; both embedded mutants -- wrong reduced census and swapped-sample exact
claim -- exit non-zero). All arithmetic is exact (integers / Fractions);
enumerations are exhaustive (3^10 = 59049 and 3^4 = 81 cases).

## Scope

One bounded cell only. No general maximality criterion is stated. No transfer
from full overlap is assumed. RC/orientation classes beyond this support,
half-integral/real comparison, and coordinate adjudication stay OPEN. Keep
#261 and #255 open.
