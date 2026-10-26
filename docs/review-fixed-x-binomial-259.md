# Fixed-observation MB09 §6.1 comparison: independent review (#259 axis A)

This note records the fixed-observation result separately from the
sample-uniform rigidity question. The fixed-x comparison itself is
tautological once the exact objective is written down; it is still useful to
state the exact score and boundary conventions, and to separate them from
structural conditions intended to hold uniformly over observations.

## Model and exact criterion

Let `E` be the finite universe of all read types of a fixed read length `L`.
For a candidate circular genome of length `G`, let `C:EN` be its
length-`L` circular spectrum. Candidates compared here have the same length
`G`, hence the same total spectrum mass `sum_e C(e)=G`. In MB09 §6.1's
fixed-external-normalizer product-binomial approximation set `N=G` (or, more
generally, keep an explicitly fixed external `N` with `0 ≤ C(e) ≤ N` for every
candidate and type). The read sample is a nonnegative count vector `x:E→N`,
with sample size `n=sum_e x(e)`; `n` is not required to equal `G` or `N`.

After dropping factors independent of the candidate, the score is

```text
F_C(x) = product_{e in E} [ C(e)^(x(e)) (N-C(e))^(n-x(e)) ].
```

Thus for a truth spectrum `A` and any one equal-length candidate `B`, the
necessary-and-sufficient fixed-`x` criterion for truth to be an ML maximizer
against `B` is exactly

```text
product_e B(e)^(x(e)) (N-B(e))^(n-x(e))
    ≤ product_e A(e)^(x(e)) (N-A(e))^(n-x(e)).
```

For a candidate class `Cset`, truth is a maximizer iff this inequality holds
for every `B in Cset`; ties are included (`≤`), and uniqueness requires strict
inequality against every distinct candidate. This is the separable identity
`fixedX_eq_separable` and iff `fixedX_le_iff` in
`AssemblyP1/FixedXProductBinomialMaximality.lean`. The iff is arithmetic
rewriting, not an independent graph-structure classification.

All exponents are nonnegative integers. Use `0^0=1`, as in the polynomial
score: a zero-observation factor contributes one even when its probability is
zero. At an observed coordinate (`x(e)>0`), `C(e)=0` makes the score zero;
at an unobserved coordinate (`x(e)=0`), `C(e)=N` makes its failure factor
`(N-C(e))^n` zero iff `n>0`, and contributes one if `n=0`. Likewise `C(e)=N`
with `x(e)>0` yields a zero success factor. These conventions include boundary
probabilities 0 and 1 without logarithms or divisions. If an admissible
candidate has `C(e)>N`, it is outside this binomial model and must not be
silently evaluated using the truncated natural-number difference.

MB09 §6.1 also presents the exact multinomial likelihood, whose candidate
dependent numerator is only `product_e C(e)^x(e)` with the candidate-intrinsic
normalizer `sum C=G`; conditioning on total counts creates cross-coordinate
coupling. The approximation replaces it by independent binomial marginals
with fixed external `N`, retaining the extra `(N-C(e))^(n-x(e))` terms,
including zero-count types. Therefore an exact-multinomial iff cannot be
transferred to this criterion. This note concerns neither §6.2 bidirected
flows nor variable-length candidates.

## Structural distinction and checked application

For one fixed observation, the product inequality above is the full criterion;
any simpler structural hypothesis is only sufficient unless separately proved
necessary. In particular, the finite exact witness reviewed here demonstrates
that support rigidity is not sufficient for this fixed observation when
new-support equal-length candidates are permitted:

* alphabet size 5, read length `L=3`, genome length `G=6`, fixed `N=6`;
* truth circular word `000001`, spectrum `A=(000:3,001:1,010:1,100:1)`;
* candidate circular word `000101`, spectrum `B=(000:1,001:1,010:2,100:1,101:1)`;
* `A` has unique positive same-support balanced circulation `(3,1,1,1)` of
  total six, while `B` is an equal-length realizable candidate with new type
  `101`;
* observed vector has `x=(000:3,001:33,010:1,100:1)` on `supp(A)` and zero
  elsewhere; its sample size is `n=38`, not `N=6`.

Direct exact arithmetic over all 125 types gives

```text
F_B(x)/F_A(x) =
  2000000000000000000000000000000000000 /
  1824800363140073127359051977856583921 > 1.
```

This says `A` loses at this one covered observation; it does not establish a
minimal counterexample or classify all observations/candidates. A separate
question, axis B, quantifies the comparison over every realizable complete-
support observation; the fixed-`x` iff alone says nothing structural about
that quantifier.

## Verification and limits

On the verified repository remote `https://github.com/ottojung/assemblyp1.git`,
`main` at `1a51baa7f6d9b6a4c43cf94a6a3676ac302974b5`, I independently ran
`scripts/verify_fixedx_product_binomial_259.py`: PASS (separable identity,
144,355 cases; fixed-`x` iff, 40,000 random cases; boundary and finite examples
included; pointwise-sufficient and concentrated-sample checks also pass).
The source quinary witness script was absent from current `main`, so I fetched
the advertised branch at signed commit
`bbeadd3b79cdd4a7d3b2a1646684221baffea068` and inspected its verifier. Its
implementation directly constructs both circular spectra, tests all positive
same-support circulations of total six, and computes the exact rational ratio
over the complete 125-type universe. The independently posted prior review
reports that verifier passing; I did not execute that absent script from the
branch in this run. This is a bounded exact witness, not an all-length census.

No claim is made here about graph rigidity being necessary for sample-uniform
maximality, about arbitrary non-realizable spectra, or about #260/#261's
general bidirected-flow model.
