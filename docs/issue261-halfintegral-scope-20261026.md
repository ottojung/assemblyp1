# Issue #261: half-integral relaxation cell (reduced AAT/TAA graph, L=3, o_min=1)

## Candidate classes (fixed reduced graph; class varied)

Reduced graph: the 4 maximal-overlap (L-1=2) edges of the audited AAT/TAA
support (AAT/ATT/TTA/TAA strands), as in
`docs/issue261-transitive-reduction-scope-20261025.md`.
- (I) Integer flows: multiplicities 0..2, edge lower bound 0, vertex
  throughput lower bound 1, zero signed-incidence balance.
- (H) Half-integral relaxation: same constraints, multiplicities in
  {0, 1/2, 1, 3/2, 2} (exact `Fraction` arithmetic).
- Likelihoods: fixed-N (N=4, sample x=(1,2)) product-binomial core and exact
  variable-length multinomial, same box-universe convention as the parent
  cells. For (H) the exact score is the formal fractional-mass extension
  Kex(d) = (d0/T)^x0 (d1/T)^x1 with T = d0+d1; Kfix needs no extension
  (polynomial in d). Truth (2,2) is admitted (integer-feasible, spelled)
  throughout.

## Result

- (I) census: exactly 4 images {(1,3),(2,2),(3,1),(4,4)}; fixed-N winner
  {(1,3)} K=81; exact winner {(1,3)} K=9/64 (parent cell).
- (H) census: exactly 10 images (all Fractions): (1,1), (1,3), (3/2,5/2),
  (2,2), (5/2,3/2), (5/2,7/2), (3,1), (3,3), (7/2,5/2), (4,4) -- a strict
  superset of (I). New images are genuinely fractional: e.g. (1,1) is
  realized only by the all-1/2 flow, infeasible integrally.
- Half-integral defeater f* = (1, 3/2, 1/2, 1) (edge order of the verifier's
  reduced list) has image (3/2,5/2): Kfix = 5625/64 > 81 and
  Kex = 75/512 > 9/64 = 72/512. So the half-integral relaxation changes the
  ML answer under BOTH likelihoods: integer winner {(1,3)} is defeated in
  (H) by a non-integer flow.
- Truth (2,2): Kfix=64 < 5625/64; Kex=1/8=64/512 < 75/512. Maximal under
  neither objective in either class.
- Hence the half-integral (a fortiori real) relaxation is NOT a neutral
  enlargement for ML maximality on this cell. Maximality criteria must
  declare integer vs half-integral vs real candidate class; integer-flow
  results do not transfer upward without an explicit preservation argument.

## Reproduction

Run `python3 scripts/verify_261_halfintegral_scope.py` (exit 0 on PASS;
both embedded mutants -- dropped-image census claim and swapped-sample
exact claim -- exit non-zero). All arithmetic exact (integers/Fractions);
enumerations exhaustive (3^4 = 81 and 5^4 = 625 cases).

## Scope

One bounded cell on the reduced graph only. No general maximality criterion
is stated. RC/orientation classes beyond this support and the full-real
comparison stay OPEN. Keep #261 and #255 open.
