# Binary length-2 balanced competitors around the alternating truth (issue #259)

## Scope

This is an algebraic parameterization of **all nonnegative integer balanced
spectra**, not a classification of circular-genome realizability and not a
likelihood theorem. Coordinates are ordered `(AA, AB, BA, BB)`. The truth is
`A=(0,m,m,0)`, its total/candidate length is `N=2m`, and balance means outgoing
count equals incoming count at each letter. In the MB09 §6.1 surrogate, `N`
would be the fixed external length. The exact surrogate contains both
`d(w)/N` and the extra `(1-d(w)/N)` factors; nothing below replaces it with the
joint multinomial objective. The §6.2 bidirected-flow setting (#260/#261) is
outside scope.

## Complete parameterization

Write a competitor as `B=(a,b,c,d)`. Flow balance at `A` is
`2a+b=a+c`, hence `c=a+b`; balance at `B` gives the same equality. Total mass
`2m` then gives `a+d+2b=2m`. Equivalently, put `t=a+b=c` to obtain

```
B = (a, t-a, t-a, 2m-2t+a)
```

with integer parameters satisfying the exact bounds

```
0 ≤ t ≤ 2m,       max(0, 2t-2m) ≤ a ≤ t.
```

Proof of bounds: nonnegativity of the four displayed coordinates is exactly
`a≥0`, `t-a≥0`, and `2m-2t+a≥0`; these combine to the stated interval.
Conversely every integer pair in the interval makes all coordinates
nonnegative, has total `2m`, and has `AB=BA`, which is precisely balance.
Thus this is bijective and complete. The number of parameter pairs (hence
balanced vectors) is `sum_{t=0}^{2m}(t-max(0,2t-2m)+1)=(m+1)^2`.

The truth itself is `(a,t)=(0,m)`. Its support is `{AB,BA}`. The `a` and `BB`
coordinates measure off-support mass; they are linked, not independent:
`BB=2m-2t+a`. In particular the previous restricted search with both
off-support coordinates zero only sees `a=0,t=m`, so its uniqueness result
does not characterize the full balanced competitor space.

## What remains before likelihood maximality

1. **Realizability:** balance and total length are necessary but not sufficient
   for a vector to be the 2-mer spectrum of a single circular word. The
   parameterized set must be intersected with that realizable candidate class;
   alternatively, if the issue's candidate class is all balanced spectra, that
   choice must be explicit. This note makes no such identification.
2. **Objective:** for each actual competitor and observed count vector `x`,
   compare the exact §6.1 product-binomial factors, including every modeled
   coordinate with `x(w)=0` and boundary weights 0 or 1. A candidate-independent
   normalization may be canceled, but the `1-d(w)/N` factors may not be
   dropped. Sample size `n=sum_w x(w)` is not presumed equal to `N`.
3. **Quantifiers:** a fixed-`x` comparison and “for every realizable complete-
   support `x`” are distinct claims. The parameterization alone proves neither
   maximality nor necessity/sufficiency of graph rigidity for either claim.

## Exact finite check

The companion verifier `scripts/verify_binary_L2_balanced_parameterization_259.py`
checks the formulas by independent enumeration for `m=1..100`, including
balance, total, nonnegativity, bijection, and the `(m+1)^2` count. This finite
check is a regression check; completeness for arbitrary `m` follows from the
algebra above, not extrapolation from the enumeration.
