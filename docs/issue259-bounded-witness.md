# Bounded exact witness for product-binomial maximality (#259)

This note records a tiny realizable instance of the MB09 §6.1 fixed-external-
`N` product-binomial surrogate, independently checked with exact integers by
`scripts/verify_issue259_bounded_witness.py`.

## Fully specified instance

Use alphabet `{0,1}`, length-1 reads, and circular candidate strings
`T=01` (truth) and `C=00` (competitor), both of length `N=2`. The complete
length-1 read universe is `{0,1}`. Their cyclic spectra are respectively
`d_T=(1,1)` and `d_C=(2,0)`, hence both spectra normalize to `N=2`.

Take the observed count vector `x=(1,1)`, with sample size `n=2`; this is
complete support and realizable under the truth (one occurrence of each
length-1 word in the circular string). For a spectrum `d`, the exact §6.1
objective, omitting candidate-independent binomial coefficients and powers of
`N`, is

```text
L(d;x,n,N) = ∏_w (d(w)/N)^x(w) (1-d(w)/N)^(n-x(w)).
```

Thus `L(T)= (1/2)^1(1/2)^1(1/2)^1(1/2)^1 = 1/16`, while
`L(C)=1^1·0^1·0^1·1^1=0` (the `w=1`
coordinate has boundary success probability zero and positive observed count).
The truth is therefore the unique maximizer among these two candidates, and
the truth is admitted. In the integer-scaled convention the scores are 16 and
0 respectively; common denominators cancel.

This intentionally narrow comparison is not the exact multinomial objective:
the multinomial probabilities for `T` and `C` are both normalized over the
read universe and the zero probability likewise rules out `C` here, but its
formula has no per-coordinate failure factors. Nor is it a §6.2 bidirected-flow
relaxation: candidates are the two specified circular strings, not arbitrary
flows. The model choice follows Medvedev–Brudno (2009), J Comput Biol §6.1,
which uses product binomial marginals with fixed external genome length; it
does not assert that this surrogate is the exact joint sampling law.

The verifier also checks a neighboring boundary case with `x=(1,0)`, `n=1`:
the competitor has likelihood 1 and truth likelihood 1/4, demonstrating why
the verdict depends on the fixed observation and why zero-count coordinates
still contribute failure factors. It computes both the product-binomial and
multinomial numerators directly with `fractions.Fraction`.
