# Issue #261: half-integral x spelled-circuit interaction cell (reduced AAT/TAA graph, L=3, o_min=1)

## Candidate classes (fixed reduced graph; class varied)

Reduced graph: the 4 maximal-overlap (L-1=2) edges of the audited AAT/TAA
support, as in the half-integral and spelled-circuit scope cells.
- (I) Integer feasible flows: multiplicities 0..2, edge lower bound 0,
  vertex throughput lower bound 1, zero signed-incidence balance.
- (H) Half-integral relaxation: same constraints, multiplicities in
  {0, 1/2, 1, 3/2, 2} (exact `Fraction` arithmetic).
- (S) Integer spelled-circuit flows: feasible flows whose edge multiset
  admits a closed trail using every unit exactly once (Eulerian circuit in
  the directed strand multigraph: balanced indeg==outdeg at every strand
  node plus weak connectivity over used edges).
- (H-spelled) Half-integral flows admitting such a certificate. Since a
  certificate consumes integral edge units, any flow with a strictly
  fractional multiplicity is non-spelling by definition; (H-spelled) is a
  priori a subset of (H) containing (S).
- Likelihoods: fixed-N (N=4, sample x=(1,2)) product-binomial core and
  exact variable-length multinomial (formal fractional-mass extension for
  H), same box-universe convention as the parent cells. Truth (2,2) is
  admitted throughout.

## Result

- (H) census: exactly the 10 parent images; fixed-N and exact winners both
  {(3/2,5/2)} with Kfix=5625/64 > 81, Kex=75/512 > 9/64 (parent result
  reproduced). Witness flow (1,3/2,1/2,1).
- The (H) winner witness is fractional (3/2, 1/2 entries), hence
  non-spelling by definition -- verified by the spelling predicate, not
  merely asserted.
- (H-spelled) census: exactly {(2,2),(4,4)}, witnessed by (1,1,1,1) and
  (2,2,2,2) -- identical to the integer spelled class (S). Exhaustive
  check over all 625 half-integral cases: no fractional feasible flow
  passes the spelling predicate.
- Spelled-class ML answer unchanged by the relaxation: fixed-N winner
  {(2,2)} K=64 (the truth); exact winners {(2,2),(4,4)} tied at K=1/8.
- Hence on this cell the half-integral relaxation adds no new spelled
  candidates while changing the unrestricted-flow answer: spelling and
  relaxation do not commute. Maximality criteria must declare both axes
  jointly (integer/half-integral AND flow/spelled-circuit); neither
  parent result transfers across the other axis without this joint check.

## Reproduction

Run `python3 scripts/verify_261_halfintegral_spelled_scope.py` (exit 0 on
PASS; both embedded mutants -- dropped-(4,4) census claim and swapped-sample
winner claim -- exit non-zero). All arithmetic exact (integers/Fractions);
enumerations exhaustive (5^4 = 625 cases); Eulerian test from scratch.

## Scope

One bounded cell on the reduced graph only. No general maximality criterion
is stated. RC/orientation classes beyond this support and the full-real
comparison stay OPEN. Keep #261 and #255 open.
