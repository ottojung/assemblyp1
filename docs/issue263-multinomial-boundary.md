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
positive interior. At a boundary candidate, equality with the extension must
be checked coordinatewise; for the multinomial objective this holds at
zero-count coordinates, while positive-count coordinates have exact cost
infinite.

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
endpoint has exact cost `⊤`, and the zero-count endpoint agrees. Hence the
generic transfer's domination and agreement hypotheses do not require
interiority for `multinomialExact` when the candidate is in `[0,G]` (for
`G ≥ 2`): use the extension equality on `1 ≤ d ≤ G`, the zero-count endpoint
lemma at `d=0`, and `le_top` at positive-count `d=0`. These statements concern
pure fixed-total likelihood only, not any penalized solver objective. The
analogous product-binomial endpoint pair needs separate analysis.

## Scope

This note records the exact endpoint semantics and the narrow formal gap: the
existing generic theorem carries a stronger interior-agreement hypothesis than
the multinomial endpoint facts require. Formalize the coordinatewise agreement
and invoke the generic transfer without the interior assumption for this
objective. Product-binomial endpoints require their own two-sided support
analysis and are not covered here.
