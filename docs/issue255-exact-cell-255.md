# Exact finite cell: AAABBB, `x=(1,0,0,5)`

This is finite exhaustive evidence for one fixed-sample cell, not a general
classification of when truth is a finite maximum-likelihood candidate.

## Model and source correspondence

The checked cell uses oriented adjacent-pair molecule types `AA`, `AB`, `BA`,
`BB`, the circular genome candidate space `{A,B}^6`, truth `AAABBB`, and observed
counts `(1,0,0,5)` in that order. Its objective is the exact same-length
multinomial likelihood. The Lean definition in
`AssemblyP1/OrientedSameLengthML.lean` is
`exactLik = ∏_w (specCount(w)/G)^(x(w))`; the omitted factor
`n!/∏_w x(w)!` depends only on the observation and so cannot change
maximizers. For this cell, the score is
`(count(AA)/6)^1 (count(BB)/6)^5`. Zero-count types contribute exponent zero.

This is the oriented, fixed-length, spelled-genome cell. It is not reverse
complement-collapsed, a product of binomial marginals, variable length, or a
MB09 §6.2 bidirected-flow candidate universe.

## Exact enumeration

All 64 binary circular words of length six were enumerated with exact
`fractions.Fraction` arithmetic. The truth score is `1/729`; the maximum is
`1/192`, so the maximum-to-truth ratio is `243/64 > 1`. The six maximizing
words are `AABBBB`, `ABBBBA`, `BBBBAA`, `BBBAAB`, `BBAABB`, and `BAABBB`.
They are rotations of `AABBBB`, so these are one circular genome modulo
rotation, but truth is not a maximizer even under that equivalence.

Independent reproducer: `scripts/verify_issue255_exact_multinomial_cell.py`
on branch `issue255-exact-multinomial-cell`, commit `0a7569202b4ffd161f572128f78d7e4010809efd`.
Run:

```sh
python3 scripts/verify_issue255_exact_multinomial_cell.py
```

It checks candidate count, exact truth and maximum scores, ratio, and the full
maximizer set. The Lean source `AssemblyP1/FixedXExactML.lean` additionally
proves its distinct finite cell census: the four feasible oriented spectra for
this truth are `B1`–`B4`, all four are genome-realizable, and at
`x=B4=(1,2,1,2)` the truth loses. These source theorems do not themselves
assert this `x=(1,0,0,5)` result; the Python enumerator supplies the finite
check here.

## Scope boundary

This computation neither settles a sample-family iff nor classifies any other
sample, strand convention, likelihood, length regime, or flow model. The
umbrella research question remains open.
