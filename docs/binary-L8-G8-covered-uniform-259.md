# Binary L8/G8 covered-sample uniformity extension (#259)

This extends the existing binary `L=G=N=8` realizable truth census with a
decision over all covered count vectors. It is a finite exact computation,
not a general rigidity theorem.

For candidate spectra `A,B` of the same circular binary genome length `G=8`,
the k-mer length is `L=8`, the fixed external normalization is `N=8`, and the
truth sample in the fixed-x part is `x=A` with `n=sum(A)=8`. The alphabet
universe contains all `2^8=256` types. Every truth and competitor is a
realizable circular spectrum, and `supp(A)` is the set of observed truth
types. The MB09 §6.1 fixed-external-N product-binomial numerator is

```
F_B(x) = product_e B_e^x_e (N-B_e)^(n-x_e),
```

over the complete 256-type universe, including zero-count types and boundary
probabilities 0 and 1. This is the product-binomial approximation discussed
in §6.1; it is not the exact multinomial likelihood from #256 and is not the
general bidirected-flow model in §6.2 (#260/#261).

## Covered-sample criterion

For any integer sample `x>=A` (coordinatewise), let
`q_e(B)=B_e product_{j!=e}(N-B_j)`. Factoring `N` powers gives

```
F_B(x)/F_A(x) = C(A,B) * product_{e in supp(A)} (q_e(B)/q_e(A))^x_e,
```

when all ratios are positive. If a denominator effective weight is zero, the
truth has zero likelihood on every covered sample and cannot be an ML
maximizer; the implementation's direct integer comparisons include this
boundary case. In the positive case, the ratio is at most one for every
integer `x>=A` iff every `q_e(B)<=q_e(A)` on `supp(A)`: sufficiency follows
factorwise, and if one coordinate ratio is greater than one, increasing that
coordinate makes the ratio unbounded. This criterion is checked in addition
to the independent literal integer comparison at `x=A`.

## Result

The 36 distinct realizable spectra yield 1,260 ordered distinct truth /
competitor pairs. All 1,260 fixed-truth comparisons and all 1,260 covered-
uniform comparisons pass, with 36 rigid truths classified maximal and no
nonrigid truths in this length-8 census. Thus it provides no test of rigidity
necessity and does not establish sufficiency generally. A separate mutation
control confirms that dropping zero-count complement factors changes an exact
score when the competitor has an intermediate unobserved coordinate count.

Reproduce with `python3 scripts/verify_binary_L8_G8_259.py`. Scores and
effective-weight comparisons use arbitrary-precision integers. Other lengths,
alphabets, samples omitting a truth-supported type, and the general
necessary/sufficient classification remain open.
