# Issue #261: disconnected-flow cell (AAT/TAA, L=3, o_min=1)

## Candidate classes

- (F) Integer edge-multiplicity flows on the complete bidirected overlap graph
  (10 edges at o_min=1): edge lower bound 0, vertex throughput lower bound 1,
  zero signed-incidence balance, zero terminal usage.
- (C) Spelled circuits: maximal-overlap (L-1=2) opposite-incidence closed walks
  visiting both observed classes; bounded spelling lengths 2..4.
- (G) Single circular genomes: single closed walks; any such walk has connected
  edge support, so a flow with disconnected support is in (F) but not in (G).
- Truth (2,2) is admitted: it is spelled (hence feasible).

## Likelihood and length universe

Fixed external N=4 product-binomial core on the two observed coordinates with
sample x=(1,2), n=3 reads: K(d)=d1^1 d2^2 (4-d1)^2 (4-d2)^1. Unobserved-class
coordinates use the stated omit/fix-at-zero convention; this finite cell does
not adjudicate the source interpretation of those coordinates.

## Result

- Spelled images: exactly {(2,2)}, K=64 (spelled-maximal truth).
- Explicit feasible integer flow f=(0,0,0,0,2,1,0,1,0,0) (multiplicities <= 2)
  with throughput image (1,3), K=81 > 64, outside the spelled set.
- Edge support of f is disconnected ({TAA,ATT} + {TTA,AAT}), so f cannot be
  realized by any single closed walk: it separates (F) from (G) as well as
  from (C).
- The image (1,3) already occurs among 0/1 feasible flows, so the separation
  is not a multiplicity->=2 artefact.

## Reproduction

Run `python3 scripts/verify_261_disconnected_flow_cell.py` (exit 0 on PASS;
a balance-breaking mutant exits non-zero). All arithmetic is integral.

## Scope

One bounded cell only. No general maximality criterion is stated. No transfer
from full overlap is assumed; the graph here is the complete o_min=1 graph, not
a transitive reduction. General maximality, half-integral/real comparison,
RC/orientation classes beyond this support, and coordinate adjudication stay
OPEN. Keep #261 and #255 open.
