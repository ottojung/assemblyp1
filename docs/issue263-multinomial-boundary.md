# Issue #263: exact fixed-total multinomial boundary

The source-oriented coefficient-free fixed-total multinomial likelihood term
for read-class count `x` and candidate multiplicity `d`, with total `G > 0`,
is `(d/G)^x`. Its negative log is `-x log(d/G)` on positive support. With the
usual extended-real convention `-log 0 = +∞`, the boundary is therefore

* `d = 0, x > 0`: likelihood zero and negative-log cost `+∞`;
* `d = 0, x = 0`: likelihood factor `0^0 = 1` (the empty product), cost `0`.

The finite affine-tail Graver certificate in `ExactMLOptimizerTransfer.lean`
uses `multinomialExt`, whereas the true objective is `multinomialExact`. The
file proves the conditional transfer when the certified minimizer lies in the
positive interior. This boundary distinction explains why that interior
hypothesis cannot simply be dropped using the current pointwise domination
argument: at zero-count coordinates the exact cost is finite, so equality with
the extension must be shown; at positive-count coordinates the exact cost is
infinite and domination is automatic, but agreement at a candidate minimizer
on that boundary fails.

For `x=0`, the endpoint `d=0` agrees with the exact cost: both are zero,
as also proved by `multinomialExt_zero_eq`. For `x>0`, e.g. `G=2,x=1`, the
endpoint `d=0` has exact cost `+∞`, while the finite affine extension assigns
the secant value `2 log 2`; this shows the extension is a regularized
surrogate at a zero-likelihood boundary.

The repository definition `multinomialExact` uses `⊤` for `d≤0 ∧ x>0`, and
returns finite `multinomialCost` otherwise. At `x=0,d=0`, the product
`0 * Real.log 0` is zero in Lean's real semantics, and the existing theorem
`multinomialExt_zero_eq` proves agreement with the extension. Thus for this
exact multinomial definition, the candidate endpoint cases are already
accounted for by the generic pointwise-domination transfer; the positive-count
endpoint has exact cost `⊤`, and the zero-count endpoint agrees. These
statements concern pure fixed-total likelihood only, not any penalized solver
objective. The remaining boundary question is whether one can formulate and
use this transfer uniformly for feasible box minima without assuming the
candidate itself interior (and similarly for the product-binomial endpoint
pair).

## Scope

This note records the exact endpoint semantics and the logical gap. The
existing Lean `multinomialExact` definition explicitly models the positive-
count zero-support case, and its zero-count endpoint agrees with the affine
extension. A useful next formal step is therefore a theorem allowing a
boundary candidate in `graver_exact_optimal_of_no_improving`, whose current
interior agreement hypothesis is stronger than needed for these endpoint
cases. Product-binomial endpoints require their own two-sided support analysis
and are not covered here.
