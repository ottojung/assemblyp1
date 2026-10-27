# Issue #261: explicit fixed-`N` half-flow witness from feasible endpoints

## Exact cell and conclusion

This note isolates the fixed-external-`N` binomial-relaxation subclaim on
the existing `AAATT`, read-length-3, `o_min=1` flow witness.  It makes the
flow construction explicit: the half-integral flow is the coordinatewise
midpoint of two feasible integer flows, so feasibility follows from the
linear edge-nonnegativity, balance, and throughput-lower-bound constraints.

The edge order is
`AAA->AAA` (length-2 self-loop), `AAA->AAT` (length 2),
`AAT->TAA` (length 1), `TAA->AAA` (length 2), with signed incidences
`(+1,-1)` at each directed edge's endpoints in this representation.  The
integral flows are
`f2=(1,1,1,1)` and `f3=(2,1,1,1)`.  Their throughput vectors are respectively
`(2,1,1)` and `(3,1,1)` on `(AAA,AAT,TAA)`.  Both are nonnegative, have zero
signed-incidence balance, and meet every vertex lower bound 1.  Their midpoint
`h=(3/2,1,1,1)` is also nonnegative and balanced; its throughput is
`(5/2,1,1)`, again meeting the lower bounds.

For the observed counts `x=(2,1,1)` and external `N=5`, all factors except the
AAA marginal agree between these candidates.  The candidate-dependent part of
that marginal is `d^2(5-d)^2`: its value is `36` at `d=2` and `d=3`, and
`625/16` at `d=5/2`.  Thus the full fixed-`N` product-binomial score ratio is
`625/576 > 1`.  The exact verifier checks feasibility and the complete ratio
with rational arithmetic.

This is an explicit **flow-level** strict relaxation gap on this finite cell;
it is stronger than comparing the scalar function without supplying feasible
flows.  It is not an unrestricted theorem about all §6.2 graphs or a general
maximality criterion.  The source-faithful transitive-reduction interpretation
of this witness is still open, so the result does not establish a general
reduction-invariant MB09 claim.  It concerns the fixed-external-`N` separable
binomial, not the scale-invariant exact variable-length multinomial.  See
`docs/issue261-half-integral-source-ml.md` for the separate exact-likelihood
no-gap theorem for half-integral flows.

## Validation artifact

`scripts/verify_261_binomial_half_flow_aaatt.py` independently checks the four
edge values, incidence balance, vertex lower bounds, throughput, and ratio.
It does not invoke Lean and is a finite exact-arithmetic certificate, not a
proof of source/reduction fidelity.
