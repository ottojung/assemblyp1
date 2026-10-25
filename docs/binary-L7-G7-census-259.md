# Binary L=7, G=7 exact realizable census (#259)

This bounded cell extends the earlier L=6 work to one genuinely new k-mer
length. It is computational evidence only; it makes no claim about arbitrary
genome lengths or alphabets.

## Model and conventions

Candidates are binary circular genomes of length `G=7`, represented by their
128-coordinate 7-mer count spectra (`L=7`). The normalization is fixed
externally at `N=7`; the truth sample is its complete observed spectrum
`x=A`, of sample size `n=sum(A)=7`. Truths and competitors range over all
realizable binary length-7 circular spectra. Each truth has support equal to
its positive 7-mer coordinates; candidate support may differ, including new
types.

For a candidate `B`, the MB09 §6.1 fixed-external-`N` product-binomial
numerator is

```
F_B(x) = product_e B_e^(x_e) (N-B_e)^(n-x_e).
```

In particular, `(N-B_e)^(n-x_e)` remains for every zero-count coordinate.
This is the product of marginal binomials approximation, not the exact joint
multinomial likelihood used in #256, whose candidate-dependent numerator is
`product_e B_e^(x_e)` and omits unobserved-type factors. Boundary values 0 and
`N` are handled using exact integer powers, including exponent zero.

The sample-uniform comparison uses effective weights
`q_e(B)=B_e product_{j != e}(N-B_j)`, over the full 128-type universe. For
covered samples `x >= A`, the established criterion checks `q_e(B) <= q_e(A)`
on every `e` in `supp(A)` (a zero competitor weight cannot beat the truth).
This criterion decides all covered sample sizes, rather than extrapolating
from the single truth sample. At `x=A`, the verifier separately computes the
full fixed-sample integer numerator.

## Result

There are 20 distinct circular truth spectra in the cell. Exact enumeration
and comparison of all 380 distinct truth/competitor pairs found:

| outcome | count |
|---|---:|
| rigid and sample-uniform maximal | 20 |
| rigid and not maximal | 0 |
| non-rigid and maximal | 0 |
| non-rigid and not maximal | 0 |

No maximality counterexample or rigidity-necessity counterexample occurs in
this cell. This small negative cell does not establish rigidity sufficiency.
The largest truth support has seven types; the full 128-type universe is still
included in each likelihood weight.

## Reproduction and scope

Run `python3 scripts/verify_binary_L7_G7_259.py`. It uses only Python integer
arithmetic, regenerates the circular spectra, checks rigidity by enumerating
positive integer circulations on each truth support, verifies the fixed-truth
scores, and applies the covered-sample effective-weight criterion. The
mutation control confirms that omitting zero-count coordinate factors changes
the score for a constructed pair with a strictly intermediate competitor
weight on an unobserved type.

The general sample-uniform theorem and broader candidate universe remain
open. This result does not cover `G>7`, larger alphabets, non-realizable
competitors, or MB09 §6.2 bidirected flows (#260/#261).
