# Sample-uniformity is a distinct quantifier

For circular oriented same-length genomes under the exact multinomial
objective, a single likelihood comparison does not decide whether the truth
maximizes for every finite observation. Take `S = AAABBB`,
`D = AABBBB`, read length two, and order types as `AA, AB, BA, BB`. Their
spectra are `A=(2,1,1,2)` and `B=(1,1,1,3)`, each of total six. For any fixed
count vector `x`, the multinomial coefficient and `6^{-sum x}` cancel, so

`L(D;x)/L(S;x) = (1/2)^{x_AA+x_AB+x_BA} (3/2)^{x_BB}`.

This gives exact rational checks at sample vectors: at `(1,0,0,5)` the ratio is
`243/64 > 1`; at `(3,1,2,1)` it is `3/16 < 1`; and at `(0,0,0,6)` it is
`729/64 > 1`. Thus the same candidate loses on one fixed sample and wins on
others. It does not follow from a fixed-x witness that sample-uniform truth
maximality fails or holds for a given truth/candidate *family*.

The scoped sample-uniform criterion in `AssemblyP1/RobustSameLengthIff.lean`
is stronger: for the oriented exact multinomial, same-length positive
circulation family, truth is maximal for every finite sample iff its spectrum
is the unique feasible spectrum. This is a bounded-model theorem, not a
classification for reverse-complement molecule types, variable lengths,
§6.2 bidirected flows/overlap floors, or historical read-string `I_s`.

## Exact-rational check

The displayed ratios were computed directly with Python `fractions.Fraction`
from the two spectra above; all comparisons are exact, not floating point.
The existing bounded AAABBB verifier covers the six-length finite census.
No new census is claimed here. The prior branch artifact
`docs/issue255-fixedx-loss-ratio.md` is present at commit
`74b557f6de7e1d4875eaddc1490c859fdcaef350`, but was not integrated into
`main`; this note records the independently verified quantifier distinction
and points to the already merged general scoped iff.
