# Issue #259: balanced-family likelihood ratio

## Scope

This note proves one restricted claim only: for truth spectrum
`A=(0,m,m,0)` and a nonnegative integer balanced competitor
`B=(u,t,t,v)` with `u+v+2t=2m`, the stated fixed-external-`N` product-
binomial likelihood ratio is at most one, with equality only for `B=A`.
It does not establish the general realizable-spectrum iff or the
sample-uniform maximality classification.

## Source model and ratio

In the MB09 §6.1 product-binomial approximation, a coordinate with
probability `p` and observed count `x` contributes
`p^x (1-p)^(n-x)`. Here the equal candidate length and fixed external
normalizer are `N=2m`; the four probabilities are the corresponding
coordinates divided by `N`. The observation is the full true spectrum
`x=A`, so `n=2m` and its counts sum to `2m`. Thus the ratio of the
competitor likelihood to the truth likelihood is

```
R = [(2m-u)/(2m)]^(2m) [(2m-v)/(2m)]^(2m)
    [t(2m-t)/m^2]^(2m).
```

The truth's positive-count coordinates have probability `1/2`; its
zero-count coordinates have probability zero. Zero powers are interpreted
as `p^0=1`, including `0^0` in the likelihood product (the continuous
likelihood-factor convention); positive powers of zero are zero. The truth
likelihood is therefore positive. If a competitor gives probability zero
to either positive-count coordinate, its ratio is zero, in agreement with
the displayed formula.

## Proof

Set `a=u/(2m)` and `b=v/(2m)`. Feasibility gives `a,b >= 0` and
`t/m = 1-a-b`, hence `a+b <= 1`. The product of the three bracketed
factors inside `R` is

```
(1-a)(1-b) (t/m)(2-t/m)
= (1-a)(1-b)(1-(a+b)^2).
```

All three factors on the right lie in `[0,1]`: `a,b` are nonnegative,
`a,b <= 1`, and `a+b <= 1`. Therefore their product lies in `[0,1]`,
and raising it to the positive integer `2m` proves `R <= 1`. Equality
requires every factor to equal one, in particular `1-a=1-b=1`, so `u=v=0`.
The balance equation then forces `t=m`, which is exactly `B=A`. Conversely
that competitor gives `R=1`. This includes boundaries (`a=1`, `b=1`, or
`a+b=1`), where the product and likelihood ratio are zero.

## Evidence boundary

This is an algebraic proof for the specified family and observation, not a
proof of the all-observations theorem. `scripts/verify_fixedx_product_binomial_259.py`
checks the underlying fixed-`x` formulas and boundary cases. A bounded
exact-rational census may additionally test this lemma but is not needed
for its proof.
