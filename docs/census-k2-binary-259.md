# Bounded circular 2-mer census for #259

This is an exact-integer computational extension of the earlier circular
binary k=1 census, not a theorem. The executable is
`scripts/census_circular_binary_k2_259.py`.

## Scope and objective

For each binary circular word length `L=2,...,16`, the program enumerates
rotation representatives, forms cyclic 2-mer count vectors over the complete
class universe `(00,01,10,11)`, and deduplicates spectra. It compares every
realizable same-length candidate `B` with every realizable truth `A` using the
fixed-external-`N` product-binomial integer numerator

```
q_N(B,i) = B_i * product_{j != i}(N-B_j),
F_N(B,x) = product_i q_N(B,i)^x_i,
N = L.
```

The product includes zero-observation coordinates. This is the MB09 §6.1
product-binomial approximation; the count-free constants are omitted. It is
not the exact joint multinomial likelihood, and it is not the §6.2
bidirected-flow objective. Every truth and candidate has the same genome
length `L`; observed samples are complete-support vectors `x >= A`, with
sample size `n=sum(x)`. The finite-box query restricts `sum(x-A) <= 8`, so it
does not establish the unbounded sample-uniform property.

## Results

| L | distinct spectra | truths maximal at x=A | maximal for all tested x >= A, excess <= 8 |
|---:|---:|---:|---:|
| 2 | 3 | 3 | 3 |
| 3 | 4 | 4 | 2 |
| 4 | 6 | 6 | 1 |
| 5 | 8 | 8 | 0 |
| 6 | 11 | 11 | 0 |
| 7 | 14 | 14 | 0 |
| 8 | 18 | 18 | 0 |
| 9 | 22 | 22 | 0 |
| 10 | 27 | 27 | 0 |
| 11 | 32 | 32 | 0 |
| 12 | 38 | 38 | 0 |
| 13 | 44 | 44 | 0 |
| 14 | 51 | 51 | 0 |
| 15 | 58 | 58 | 0 |
| 16 | 66 | 66 | 0 |

The sole `L=4` survivor is `(1,1,1,1)`. At `L=3`, the two survivors are
`(0,1,1,1)` and `(1,1,1,0)`; at `L=2`, all three realizable spectra survive.
The data support checking the all-sample necessary/sufficient inequalities
against realizable balanced 2-mer spectra, but do not prove a general
realizability-constrained transfer theorem. In particular, failure to survive
the finite excess box is only a bounded witness search; survival is not proof
of unbounded maximality.

## Reproduction

```
python3 scripts/census_circular_binary_k2_259.py
python3 -m py_compile scripts/census_circular_binary_k2_259.py
```

All score computations and comparisons use Python arbitrary-precision
integers; no floating point or external package is used.
