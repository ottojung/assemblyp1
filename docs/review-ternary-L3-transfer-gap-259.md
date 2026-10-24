# Independent review: ternary L=3 transfer-gap census (#259)

**Review status:** verifier and finite census independently rerun; claim scope
checked. This is bounded computational evidence, not a theorem for arbitrary
length or alphabet.

## Reproduction

Against commit `b9ebf486398f85d28bd05682d8a0813b8678c8aa`, the following passed:

```text
python3 scripts/verify_ternary_L3_transfer_gap_259.py
  513 distinct necklace spectra for ternary L=3, G=3..7
  918 one-unit transfers; 6 preserve flow balance; 0 mismatches
  totals: 331 both-max, 84 both-beaten, 98 gap, 0 skipped
  ALL OK
python3 scripts/check-research-docs.py
  research documentation integrity checks passed
python3 scripts/verify_signed_commits.py --base origin/main --head HEAD
  signed-commit gate PASSED (1/1)
git diff --check
  passed
```

An independently written exact `fractions.Fraction` evaluation of the
smallest displayed witness used `N=4`, `n=6`, truth `A(212)=2,A(121)=2`,
competitor `B(212)=1,B(121)=3`, and counts `x(212)=2,x(121)=4`. It returns
`F_A=1/4096`, `F_B=6561/16777216`, hence `F_B/F_A=6561/4096`.

## Quantifier and scope clarification

The displayed `B` is unbalanced, so it is not a realizable circular-word
spectrum. Its likelihood ratio establishes that this `x` is beatable in the
full coordinate simplex. The separate finite enumeration is what reports
that the truth `A` is maximal against every *realizable* spectrum for every
covered sample `x >= A` (with `N=G=4`); the single displayed ratio alone does
not establish that sample-uniform statement. Conversely, the witness shows
that the full-simplex covered-sample obstruction does not suffice to decide
maximality after restricting competitors to realizable spectra.

For these coordinates, `supp(A)={212,121}` and the two likelihoods compare
`F_D(x) = product_w (D(w)/N)^x(w) (1-D(w)/N)^(n-x(w))`, with all 27
length-3 coordinates included. In particular, zero-count coordinates
contribute their `(1-D(w)/N)^n` factors. The objective is MB09 §6.1's
product of binomial marginals, not the joint multinomial objective. This
finite census does not prove sample-uniform maximality or a rigidity
classification beyond its enumerated ternary `L=3`, `G=3..7` cases.

No conclusion about general bidirected flows in #260/#261 is drawn here.
