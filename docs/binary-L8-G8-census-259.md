# Binary L=8, G=8 exact realizable census (#259)

This is a bounded follow-up to the binary `L=G=N=7` census. It is
computational evidence only and does not establish a general maximality or
rigidity theorem.

## Model

Candidates are binary circular genomes of length `G=8`, encoded by their
256-coordinate 8-mer spectra (`L=8`). The fixed external normalization is
`N=8`; at the truth sample `x=A`, the sample size is `n=sum(A)=8`. Truths and
competitors are all realizable binary length-8 circular spectra. The observed
support is `supp(A)={e:A_e>0}`; competitors can differ on this support and on
unobserved coordinates.

For MB09 §6.1's fixed-external-`N` PRODUCT-BINOMIAL approximation, the
candidate-dependent numerator is

```
F_B(x) = product_e B_e^(x_e) (N-B_e)^(n-x_e).
```

All 256 coordinates are included, including zero-count types. Integer
exponentiation handles probabilities at the boundary 0 and 1 (zero exponent
contributes 1). This is not the exact multinomial objective from #256: that
objective's candidate-dependent numerator is `product_e B_e^(x_e)` and has no
unobserved-type complement factors. It is also not MB09 §6.2's bidirected-flow
model (#260/#261).

For each pair, the verifier compares the exact integer score at `x=A`. It also
tests sample-uniform comparisons over covered samples `x>=A` with the
effective weight numerator
`q_e(B)=B_e product_{j!=e}(N-B_j)` on each `e` in `supp(A)`. Thus the printed
classification includes both the truth sample and all covered count vectors
by the coordinatewise product-binomial comparison criterion; it does not
claim maximality over samples omitting any truth-supported type.

## Result

There are 36 distinct circular spectra and 1,260 ordered distinct truth /
competitor pairs. The exact census reports:

| truth class | sample-uniform maximal | not maximal |
|---|---:|---:|
| rigid | 36 | 0 |
| nonrigid | 0 | 0 |

The rigidity check enumerates positive integer circulations supported on the
truth's 8-mer types, with total 8; rigid means the observed circulation is the
only such circulation. Consequently this cell offers no test of necessity
against nonrigid truths. The result is a negative finite cell, not evidence
that rigidity is sufficient in general. The largest support has eight types,
but likelihood products still include the full 256-type universe.

## Reproduction and limitations

Run `python3 scripts/verify_binary_L8_G8_259.py`. It regenerates circular
spectra, uses exact Python integers for every likelihood product, enumerates
truth-support circulations for rigidity, and checks a non-vacuous mutation:
for a multi-type truth and a realizable competitor with an intermediate count
on an unobserved type, omitting zero-count-coordinate factors changes the
score. The census does not address other lengths, alphabets, or samples not
covering the truth support. The general necessary-and-sufficient
classification remains open.
