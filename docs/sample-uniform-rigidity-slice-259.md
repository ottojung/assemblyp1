# Sample-uniform rigidity slice: binary L=2, G=3..6 (#259 axis B)

Minimal exact-rational slice toward the open axis-B question (every
realizable complete-support observation), complementing the fixed-x review
(`docs/review-fixed-x-binomial-259.md`, commit `c521769`) and the merged
covered-sample (same-support) necessity theorem (PR #293). Nothing here
imports the exact-multinomial iff (#256).

## Setup (all spelled out)

* Candidate length: circular genomes of fixed length `G`; read length `L=2`
  over `{0,1}`, universe `U` = 4 two-mers `(00,01,10,11)`.
* Normalization: fixed external `N = G` (MB09 §6.1 product-binomial
  approximation, not the exact multinomial with intrinsic normalizer).
* Support: `supp(C) = {e : C_e > 0}` for a spectrum `C`.
* Sample size: `n = G` (observations are realizable same-`G` spectra).
* Observation class: `X(A)` = realizable same-`G` spectra `x` with
  `x_e >= 1` on all of `supp(A)` (complete support).
* Candidate class: all distinct realizable same-`G` spectra, **including
  new-support competitors** (this is what PR #293 does not cover).
* Exact objective: `F_C(x) = prod_e C_e^x_e (N-C_e)^(n-x_e)` as integers
  with `0^0 = 1`. At an observed coordinate (`x_e > 0`), `C_e = 0` scores
  zero; at an unobserved coordinate (`x_e = 0`), the factor is one even at
  boundary `C_e in {0, N}`. The MB09 §6.1 approximation keeps the extra
  `(N-C_e)^(n-x_e)` failure factors over every type, including zero-count
  types; the exact multinomial conditions on totals instead (kept separate).
* Rigidity: uniqueness of the positive balanced circulation of total `G`
  on the truth-support de Bruijn subgraph.

## Result (verifier: `scripts/verify_sample_uniform_rigidity_slice_259.py`)

| G | spectra | maximal truths | nonrigid maximal |
|---|---------|----------------|------------------|
| 3 | 4 | 2 | 0 |
| 4 | 6 | 1 (`(1,1,1,1)`, word `0011`) | 0 |
| 5 | 8 | 0 (vacuous) | 0 |
| 6 | 11 | 0 (vacuous) | 0 |

Necessity holds in this slice: **0 nonrigid-but-maximal truths**.
Cells G=3,4 hold it non-vacuously (maximal truths exist and are rigid);
cells G=5,6 hold it vacuously (every truth loses somewhere, so there is
nothing whose rigidity needs checking). This is a bounded census, **not**
a general necessity theorem: varying-`n` pools already beat every truth
in the G=5 cell (checked during development), and larger alphabets/lengths
are untested here.

Sufficiency fails at the smallest cell (exact integers):
rigid truth `A = (3,0,0,0)` (word `000`, unique circulation `(3,)`),
beaten at realizable complete-support `x = (1,1,1,0)` (word `001`) by
`B = x`, with `F_A(x) = 0` (observed `01` kills the `A_01 = 0` factor)
versus `F_B(x) = 1*2^2 * 1*2^2 * 1*2^2 * 1*3^3 = 1728`
(`B_11 = 0` unobserved contributes `0^0 = 1`).

## Scope

General sample-uniform classification and rigidity necessity stay OPEN;
#260/#261 (genuine general bidirected flows) untouched.
