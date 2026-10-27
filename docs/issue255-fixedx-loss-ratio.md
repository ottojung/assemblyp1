# Exact oriented fixed-sample loss ratio (bounded genome witness)

For a circular genome `C` and oriented adjacent-pair counts `x`, write
`P(C;x) = ∏_e (spec_C(e)/6)^(x_e)`, omitting the candidate-independent
multinomial coefficient. Let truth `S = AAABBB` have spectrum
`(2,1,1,2)` and candidate `D = AABBBB` have spectrum `(1,1,1,3)` in type
order `AA,AB,BA,BB`. For observed counts `x=(1,0,0,5)`,

`P(D;x)/P(S;x) = (1/2)·(3/2)^5 = 243/64 > 1`.

The truth likelihood is `1/729`; the candidate likelihood is `1/192`.
This is a hand-checkable strict loss for one fixed sample in the oriented,
exact multinomial, same-length spelled-genome model. It does not require an
exhaustive census. The exact-rational finite census in
`scripts/verify_issue255_exact_multinomial_cell.py` additionally reports the
global maximum among all 64 binary length-six circular words (`1/192`, six
rotational maximizers), but that computation is bounded evidence, not a
general theorem.

The same truth and candidate also lose at `x=(1,0,1,4)`: truth likelihood
`1/1458`, candidate likelihood `1/576`, ratio `81/32`. The verifier
`scripts/verify_255_fixedx_second_witness.py` checks both ratios using Python
exact fractions.

These witnesses do not classify arbitrary fixed `x`. No inference is made
about every-sample maximality, reverse-complement molecule types, fixed-`N`
product-binomial likelihood, variable genome lengths, MB09 §6.2 bidirected
flows/overlap floors, or either reading of `I_s`. Those distinctions and the
broader open status remain in `docs/remaining-open-matrix-255.md`.
