# Exact oriented fixed-sample loss ratio (bounded genome witness)

For a circular genome `C` and oriented adjacent-pair counts `x`, write
`P(C;x) = ∏_e (spec_C(e)/6)^(x_e)`, omitting the candidate-independent
multinomial coefficient. In the finite witness from the #255 matrix,
`S = AAABBB`, `x_AA = 1`, `x_AB = x_BA = 0`, and `x_BB = 5`. Compare the
same-length circular candidate `D = AABBBB`:

| type | `AA` | `AB` | `BA` | `BB` |
|---|---:|---:|---:|---:|
| truth spectrum `spec_S` | 2 | 1 | 1 | 2 |
| candidate spectrum `spec_D` | 1 | 1 | 1 | 3 |
| observed count `x` | 1 | 0 | 0 | 5 |

Therefore the exact multinomial likelihood ratio is

`P(D;x)/P(S;x) = (1/6)/(2/6) · ((3/6)/(2/6))^5 = 3^5/2^6 = 243/64`.

Thus this candidate strictly beats the truth for this *fixed* sample. This
algebraic certificate is a hand-checkable lemma for one oriented, exact
multinomial, same-length spelled-genome instance; it does not depend on the
exhaustive census to establish the strict loss. The separate exact-rational
enumeration in `scripts/verify_issue255_exact_multinomial_cell.py` reports the
global maximum among all 64 binary length-six genomes (`1/192`, six rotational
maximizers), but that broader finite computation is not needed for this
pairwise witness.

No inference is made about every-sample maximality, reverse-complement molecule
types, fixed-`N` product-binomial likelihood, variable genome lengths, MB09
§6.2 bidirected flows/overlap floors, or either reading of `I_s`. General
fixed-`x` classification beyond scoped criteria remains open.
