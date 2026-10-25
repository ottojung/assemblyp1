# Issue #261: likelihood-sensitivity cell (AAT/TAA, L=3, o_min=1)

## Candidate class (fixed; likelihood varied)

- (F) Integer edge-multiplicity flows on the complete bidirected overlap graph
  (10 edges at o_min=1, the audited graph of the disconnected-flow cell):
  edge lower bound 0, vertex throughput lower bound 1, zero signed-incidence
  balance, zero terminal usage. Multiplicities 0..2 exhaustively enumerated
  (3^10 = 59049 cases; exact 78-image census).
- Truth (2,2) is admitted: it is spelled (hence feasible), Kfix = 64.
- This cell does NOT separate spelled (C) from flows (F) -- that is the parent
  cell (docs/issue261-disconnected-flow-cell-20261025.md). It fixes (F) and
  varies the likelihood, addressing the issue's required axis "which likelihood
  (exact vs fixed-N binomial) and length universe is used".

## Shared finite universe and the two objectives

Universe U: flow throughput images inside the box {0..4}^2 (the fixed-N
universe, N=4). Exactly 16 images. Sample x=(1,2), n=3 reads on the two
observed coordinates; unobserved-class coordinates use the omit/fix-at-zero
convention of the parent cell (no source-interpretation adjudication here).

- Fixed-N product-binomial core: Kfix(d) = d1^1 d2^2 (4-d1)^2 (4-d2)^1.
  This is the separable-binomial core of the #259/#260 count-vector criterion
  (`Section62BinomialCriterion` on main; linked, not forked).
- Exact variable-length multinomial: Kex(d) = (d1/T)^1 (d2/T)^2, T=d1+d2.
  This is the project-objective likelihood (`GeneralBidirectedFlowML`
  `varLengthCriterion`), restricted to the same candidate image set.
  Both are evaluated in exact arithmetic (integers / Fractions).

## Result

- Fixed-N argmax over U is the singleton {(1,3)}, K=81.
- Exact-multinomial argmax over U is {(1,2),(2,4)}, K=4/27 (a genuine tie:
  both lie on the (k,2k) ray matching the sample ratio).
- The winner sets are DISJOINT: the ML winner over one fixed feasible-flow
  class depends on which likelihood (exact vs fixed-N binomial) is used.
  Truth (2,2) is maximal under neither.
- N-sensitivity check: fixed-N with N=5 picks {(2,3)} (K=324), so even the
  fixed-N answer is N-dependent; the exact answer is N-free.

## Reproduction

Run `python3 scripts/verify_261_likelihood_sensitivity.py` (exit 0 on PASS;
both embedded mutants -- fixed-N N=5 winner claim and swapped-sample exact
winner claim -- exit non-zero). All arithmetic is exact.

## Scope

One bounded cell only. No general maximality criterion is stated. No transfer
from full overlap is assumed. Transitive-reduction invariance, RC/orientation
classes beyond this support, half-integral/real comparison, and coordinate
adjudication stay OPEN. Keep #261 and #255 open.
