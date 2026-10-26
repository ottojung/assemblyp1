# Issue #261: `o_min=2` fixed-length exact-multinomial spelled census

_Status: exact bounded enumeration, 2026-10-26. This tests a separate
objective/candidate slice from the prior `o_min=2` nonspelled fixed-N-binomial
rule-out and `o_min=1` variable-length exact-iid failure._

## Scope

- Alphabet `{A,T}`, reverse complement `A↔T`; `L=3`, `o_min=2=L−1`.
- Observed molecule panel `{AAA,AAT,TAA}`. Truth `S=AAATT`, length and external
  universe size `N=5`; sample `x={AAA:2,AAT:1,TAA:1}` (`n=4`).
- **Candidates:** circular genomes of fixed length 5 whose every length-3
  window belongs to the observed molecule panel. Their consecutive windows
  induce an `o_min=2` closed walk. This is the spelled-circuit/genome image,
  not every abstract feasible bidirected flow.
- **Truth admission:** yes; its five cyclic windows are `AAA,AAT,ATT,TTA,TAA`,
  all in the panel after reverse-complement molecule identification; all
  transitions have overlap 2.
- **Likelihood:** exact multinomial `n!/∏x! · ∏(d_w/N)^x_w`, with fixed `N=5`
  for the candidate universe. This is not the §6.1 product-binomial
  approximation.
- The graph has 10 oriented proper-overlap pairs on the six observed strands;
  the candidate walks use maximal overlap 2. No conclusion about the disputed
  source transitive-reduction implementation is needed for the listed walks;
  the exhaustive universe is explicitly the observed-panel spelled class.

## Exact result

The truth spectrum is `{AAA:1,AAT:2,TAA:2}` and its exact multinomial
probability is `48/625`. Exhaustive enumeration of all `2^5` binary circles,
quotiented only for reporting (not needed for score comparison), finds 12
panel-supported candidates. Their maximum score is `48/625`; there are no
strict beaters. This is a finite **rule-out**, not a maximality theorem for
unbounded lengths, other observations, or the full flow domain.

This differs materially from the earlier two cells: it does not reuse the
`o_min=1` exact-iid variable-length beater, nor the `o_min=2` nonspelled
fixed-N-binomial bounded search. It documents a third objective/candidate
combination and a small exact counterexample-to-transfer check: the known
`o_min=2` full-flow nonspelled search result cannot by itself be read as a
statement about exact-multinomial spelled genomes.

The data are sampled start positions `(0,0,1,4)` on `AAATT`; thus the sample
is realizable under the circular uniform-start read model. Each truth window
has molecule-class identity among the three observed vertices. The result
does not claim genome inclusion in a *general flow* candidate set; it only
compares the enumerated spelled subclass, and no candidate-set inclusion is
used to import a prior full-overlap failure.

## Reproduce

```sh
python3 scripts/verify_261_omin2_spelled_exact.py
```

The verifier uses Python `Fraction` arithmetic and exits nonzero if the
admission, spectrum, candidate census, or score comparison changes. It does
not prove completeness for abstract flows. Keep the unbounded flow/spelling
bridge, transitive-reduction equivalence, and the remaining #261/#255 axes open.
