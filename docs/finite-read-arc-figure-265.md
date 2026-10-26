# Finite-read inference arc: one figure's data, checked (#265)

Status: 2026-10-26. Owner: agent `tIyaSe8ezPshdl5i4nqCXm`.
Base: `main` @ `433f199`. Scope: one bounded increment only.

This note supplies the exact numbers behind a single #265 arc figure:
**finite-sample ML can pick the wrong genome, then converge**.
It does not edit the paper; it traces to existing paper/Lean sources.

## Model (exact)

Circular genomes `S = AAC` (truth) vs `D = AAAC`, read length `L = 2`,
uniform-start error-free reads. Read laws:

| | `AA` | `AC` | `CA` | `CC` |
| --- | ---: | ---: | ---: | ---: |
| Truth `p_S` | 1/3 | 1/3 | 1/3 | 0 |
| Competitor `p_D` | 1/2 | 1/4 | 1/4 | 0 |

Likelihood `L_n(G) = prod_i P_G(R_i)` (exact product, not the MB09
§6.1 product-binomial surrogate or the §6.2 flow objective).
Ties counted as errors; here no positive-probability ties occur for
`n >= 1` (ratio `3^n / 2^(2n-a)` is never 1).

## Figure data (exact rationals)

- 1-read sample `[AC]`: `L_S = 1/3 > L_D = 1/4` (truth wins).
- 2-read sample `[AA, AA]`: `L_S = 1/9 < L_D = 1/4` (truth loses:
  finite-sample reversal, sampling fluctuation, not a defect of ML).
- Strict exact-ML success: `succ(1) = 2/3 > succ(2) = 4/9`
  (per-truth success is NOT monotone; prior-averaged optimal success
  still satisfies `S_{n+1} >= S_n` by the ignore-extra-observation argument).

Verifier `scripts/verify_finite_read_arc_265.py` reproduces all of the
above with exact rationals.

## What this is / is not

- Illustrates #265 items 2 (finite-sample surprise with actual
  probabilities) and 4 (per-truth non-monotonicity vs prior-average
  monotonicity). Finite-sample ML remains principled (Bayes-optimal on
  prior average, `thm:bayes-optimal`); consistency still holds
  (`P(correct) -> 1` under identifiability).
- Not a new bound, not a sample size, not a claim about the unrestricted
  genome universe or the MB09 surrogates.

## Sources

- Paper: `paper/sections/05-population.tex` Proposition `prop:nonmonotone`
  (`sec:nonmonotone`); `paper/sections/03-open-question.tex`
  Theorem `thm:bayes-optimal`; slides `slides/programmers.md` Backup B4.
- Kernel (checked, not re-proved here):
  `AssemblyP1/NonmonotonicityWitness281.lean` (`success_not_monotone`);
  `AssemblyP1/FiniteBayesDecision.lean` (`chooseMAP_optimal`,
  `chooseMAP_success_monotone_under_refinement`); claim index
  `docs/verification.md`.
- Standard statistics (cited, not kernel-checked): Berger (1985);
  Cover & Thomas (2006) §11.9.
