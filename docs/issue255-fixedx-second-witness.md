# Second exact fixed-sample loss witness

This is a second hand-checkable sample for the same bounded oriented,
exact-multinomial, same-length spelled-genome comparison recorded in
`docs/issue255-fixedx-loss-ratio.md`. Keep oriented pair types ordered as
`AA, AB, BA, BB`. The truth `S = AAABBB` has spectrum `(2,1,1,2)` and the
same-length candidate `D = AABBBB` has spectrum `(1,1,1,3)`. For the distinct
fixed observation `x = (1,0,1,4)`, all six observed reads are on the truth's
support, and

`P(S;x) = (2/6)(1/6)(2/6)^4 = 1/1458`,

`P(D;x) = (1/6)^2(3/6)^4 = 1/576`,

so `P(D;x)/P(S;x) = 81/32`. The candidate strictly beats the truth for this
particular sample; the multinomial coefficient cancels in the ratio. The
independent exact-rational check is `python3
scripts/verify_255_fixedx_second_witness.py`.

This is a pairwise witness, not an exhaustive maximum computation or a
criterion. It uses oriented types, exact multinomial likelihood, equal spelled
length six, and a truth-admissible sample with replacement. It does not imply
anything about reverse-complement molecule types, the fixed-`N` product-
binomial surrogate, variable lengths, MB09 §6.2 bidirected flow feasibility or
`I_s`. In particular, it changes no general fixed-`x` classification status.

## Bounded sample-family census for this truth

As a separate bounded result, `python3
scripts/verify_255_aaabbb_truth_never_wins.py` exactly enumerates all 84
histograms of six draws supported on the four pair types present in `S`.
Against all 6-compositions of length six (a larger candidate spectrum domain
than spelled circular genomes), it finds exactly one sample where `S`
maximizes and a largest competitor/truth ratio of `46656` at `x=(0,0,6,0)`.
The maximized sample is the all-`AA` observation, where the truth itself scores
`1/729` and is a maximum. This census settles only this one `S`, length, and
oriented multinomial model, with the relaxed composition candidate domain; it
is finite computation, not a classification theorem for other truths or model
axes.
