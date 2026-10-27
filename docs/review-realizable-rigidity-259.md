# Review note: realizability blocks the rigidity argument (#259)

## Reviewed artifact and scope

This is an independent review of the exact bounded ternary, read-length-three
census in `scripts/verify_ternary_L3_transfer_gap_259.py` (source commit
`b9ebf486398f85d28bd05682d8a0813b8678c8aa`). The model is circular words of
length `G`, full oriented length-3 spectra, and MB09 §6.1's fixed external
normalizer `N=G` product of marginal binomials. It is not the joint
multinomial objective and says nothing about §6.2 bidirected flows.

The source issue's phrase “every realizable complete-support observation”
requires an additional restriction beyond `x >= A` on the true support: `x`
must itself be the spectrum of an admissible circular read sample (with its
actual sample length `n=sum(x)`). A general integer vector in that orthant is
not necessarily a circular spectrum.

## Independently replayed results

The verifier passed unchanged:

```
ternary L=3, G=3..7: 513 distinct necklace spectra
transfer-balance: 918 one-unit transfers; 6 preserve; 0 mismatches
totals: both maximal 331, both beaten 84, full-beaten/realizable-max gap 98,
        skipped 0
smallest gap: G=N=4; truth word 1212; x(212)=2, x(121)=4; n=6;
             full-class B is unbalanced; F_B/F_A=6561/4096
```

All likelihood arithmetic in the script is integer or `Fraction` arithmetic.
The witness explicitly illustrates the obstruction: the unrestricted
one-coordinate transfer gives a strict full-class product-binomial improvement,
but that transferred vector violates directed-flow balance and is not a
circular spectrum. In this finite family the truth is nevertheless maximized
against every realizable truth spectrum, for every covered integral observation
tested via the fixed-`N` effective-weight criterion.

## Precise failed lemma

The broad covered-vector argument has the form

```
non-rigid supported spectrum A
  -> a distinct balanced B with same support
  -> a supported coordinate where q_B > q_A
  -> some integer x >= A for which the product-binomial ratio exceeds 1.
```

The last implication is valid when `x` ranges over the entire integer
orthant. The missing step is:

> For every non-rigid circular spectrum `A` and every resulting improving
> direction, there exists a **realizable circular observation spectrum** `x`
> in the covered set whose exact product-binomial likelihood ratio is > 1.

The ternary L=3, G=4 witness disproves the naive transfer-level version of this
step: the naturally improving transfer is not balanced, and no realizable
competitor beats the truth in the complete bounded census. It does not
disprove the quantified lemma for every possible realizable observation
family; it shows that neither the full-simplex effective-weight theorem nor a
single coordinate transfer proves that lemma. Consequently, this review does
not claim a general necessity theorem or a general counterexample to it.

## Check and status

Independent replay command:

```sh
python3 scripts/verify_ternary_L3_transfer_gap_259.py
```

Result: `ALL OK`, including all 513 spectra, all 918 transfer checks, and the
exact `6561/4096` witness. This is bounded computational evidence only. The
general realizable tangent/cone characterization, and therefore whether
same-support graph rigidity is necessary for sample-uniform maximality over
all realizable complete-support observations, remains open.
