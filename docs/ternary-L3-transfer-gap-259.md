# Ternary length-3 transfer-gap census (#259)

**Status:** exact bounded computational evidence; not a general theorem.
Verifier: `scripts/verify_ternary_L3_transfer_gap_259.py`.

## Model and scope

The alphabet is `{0,1,2}`, read length is `L=3`, and a candidate is a
circular word of length `G` with its full cyclic length-3 spectrum `A`.
Thus the coordinate universe has 27 words and `N=G` is the fixed external
normalizer in MB09 §6.1. For `G=3,...,7`, the census ranges over every
distinct spectrum of a circular word (necklaces identify rotations).
The likelihood compared is the exact product-binomial objective

`F_D(x) = product_w (D(w)/N)^x(w) (1-D(w)/N)^(n-x(w))`.

This is the §6.1 product of binomial marginals, not the exact joint
multinomial likelihood. The common binomial coefficients cancel in
candidate comparisons. To classify whether truth `A` is maximal for some
sample, the verifier uses the fixed-`N` covered-sample criterion on the
truth support: a competing spectrum `B` beats for some integral `x>=A`
there iff every effective factor `q_B(w)` on `supp(A)` is positive and at
least one exceeds `q_A(w)`, where
`q_D(w)=D(w) product_{v!=w}(N-D(v))`. This handles zero and unit boundary
probabilities without logarithms or floating point.

For a one-unit transfer `B=A-e_j+e_i` between supported coordinates, its
directed-flow balance residual is zero exactly when
`{pre(i),suf(j)} = {pre(j),suf(i)}` as multisets. The script checks both
directions of this elementary identity on every transfer enumerated.

## Census (G <= 7 only)

| G | Distinct spectra | maximal both | beaten both | full-beaten / realizable-max gap | skipped |
|---:|---:|---:|---:|---:|---:|
| 3 | 11 | 11 | 0 | 0 | 0 |
| 4 | 24 | 21 | 0 | 3 | 0 |
| 5 | 51 | 39 | 0 | 12 | 0 |
| 6 | 127 | 86 | 18 | 23 | 0 |
| 7 | 300 | 174 | 66 | 60 | 0 |
| **Total** | **513** | **331** | **84** | **98** | **0** |

Transfer-balance check: 918 transfers, 6 preserve balance, no mismatch with
the endpoint-multiset condition.

## Smallest exact gap witness

At `G=N=4`, the truth word `1212` has nonzero spectrum coordinates
`A(212)=2` and `A(121)=2`. The full-class transfer `B` changes these to
`B(212)=1`, `B(121)=3`; it is unbalanced (and hence not a circular-word
spectrum), while exhaustive comparison finds no realizable spectrum that
beats `A` for any covered sample. Choose `x(212)=2`, `x(121)=4`, all other
counts zero. The sample size is `n=sum_w x(w)=6`, while the external normalizer is
still `N=G=4`. Direct evaluation gives
`F_A(x)=1/4096`, `F_B(x)=6561/16777216`, hence
`F_B(x) / F_A(x) = 6561/4096 > 1`.

The witness is also cross-checked by integer powers of the scaled effective
factors. Thus the gap is an exact bounded witness to failure of the
full-simplex converse after restricting competitors to realizable spectra;
it is not evidence that the same gap persists at every length.

## Remaining scope

This census establishes neither a theorem for all ternary `G` nor a
classification for `G>=8`. Alphabets of size at least four and the
non-alternating infinite-family question remain open. The exact multinomial
objective and general bidirected flows (#260–#261) are outside this census.

Run with:

```sh
python3 scripts/verify_ternary_L3_transfer_gap_259.py
```
