# PR #157 Review Verdict — Agent 0e9941718c09

**PR:** https://github.com/ottojung/assemblyp1/pull/157
**Branch:** `research/issue255-mb09-source-20261011`
**Commit:** `48cf0b275dbed1dfc420dab7842e7a0194c1e2f6`
**Base:** `f17a1739cb8568bf4cff552bafb58f5fed1dd026` (current main HEAD)
**Verdict:** APPROVE — all review gates pass

## Review checklist

### 1. MB09 §6.1 quote verification — PASS

The exact sentence was verified against the original authors' PDF
(https://www.cs.toronto.edu/~brudno/medvedev_MLA.pdf), paper page 11:

> "However, as the number of trials goes to inﬁnity, the Xi random variables become independent."

The PR normalizes the fi-ligature "inﬁnity" to "infinity", which is the correct
Unicode normalization. The quote is verbatim and the page citation (p.11, §6.1)
is accurate.

Context verified: the sentence sits between "When taken together, their joint
distribution is exactly the multinomial distribution" and "Because the number
of trials (sampled k-molecules) is typically large, we can approximate the
multinomial distribution as the product of the individual binomial
distributions of each X_i."

### 2. Covariance/correlation algebra — PASS

For a multinomial with fixed category probabilities `p_i`:

- `Cov(X_i, X_j) = -n·p_i·p_j` — standard multinomial result, verified.
- `Corr(X_i, X_j) = -sqrt(p_i·p_j/((1-p_i)(1-p_j)))` — verified computationally
  for multiple probability values; the n cancels in the ratio.
- Independent of `n` — verified for n=10, 100, 10000.
- Only normalized frequencies `X_i/n` have covariance `-p_i·p_j/n → 0` — verified.
- Two-category example `X_2 = n - X_1` for every `n` — trivially true.

### 3. Multinomial vs approximate binomial separation — PASS

The PR explicitly separates:
- The exact multinomial joint likelihood (Def. 1.2)
- The product-of-binomial-marginals as a "deliberate approximate pseudo-likelihood"
- States it is "not the exact joint likelihood, and not a generally asymptotically exact factorization"
- No conclusions imported into the exact multinomial objective

### 4. Zero changed theorem statuses — PASS

- Only 2 documentation files changed: `docs/fixed-length-binomial-counterexample.md`
  and `docs/remaining-open-matrix-255.md`
- No Lean files changed
- The matrix explicitly states: "No status is flipped by this source-fidelity correction"
- #259 (A)/(B) remains OPEN
- All landed/refuted/OPEN entries unchanged

### 5. Docs integrity check — PASS (local)

- `scripts/check-research-docs.py`: passed
- `scripts/verify_historical_coverage_audit.py`: PASS
- `scripts/verify_247c_historical_witnesses.py`: W1/W2 fully validated
- `scripts/verify_261_binomial_extreme_samples.py`: PASS

### 6. CI status — ALL GREEN

- CI workflow:
  - `research-docs`: success
  - `build` (Lean): success (build + kernel replay + axiom audit all passed)
  - `deploy`: skipped (expected for PR)
- Documents workflow: success
- Slides and Pages workflow: success

### 7. Commit signature — PASS

Commit `48cf0b2` is GPG-signed by Otto Jung (EDDSA key `08AF2726...`).
`git verify-commit` confirms: "Good signature".

### 8. Base commit — PASS

Updated from `02406aa` to `f17a173` (current main HEAD), correctly reflecting
the rebase on current green main.

## Summary

This is a clean, well-scoped documentation-only correction that faithfully
records the historical MB09 §6.1 independence sentence with exact quote and page
citation, correctly explains why the asymptotic claim licenses no finite-sample
conclusion, verifies the covariance/correlation algebra, and changes no theorem
statuses. All review gates pass. Recommend merge.

## Remaining open (umbrella #255 stays open)

- #258: fixed-x sample classification — OPEN
- #259: MB09 §6.1 fixed-external-N product-binomial (A)/(B) — OPEN
- #261: general MB09 §6.2 bidirected flows — OPEN
- #262: full-overlap edge irreducibility — OPEN
- #263: separable convex discrete Graver criterion — IN PROGRESS
- #264: integer-kernel conformal Graver decomposition — OPEN
