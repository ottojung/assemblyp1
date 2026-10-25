# Fixed-x vs sample-uniform gap on realizable binary-L6 truths (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_fixedx_gap_realizable_L6_259.py` (no Lean import, no floats
in any comparison). Companion to `docs/realizable-census-L6Q4-259.md`._

## 1. What is classified

For the MB09 §6.1 fixed-external-`N` product-binomial surrogate, the issue
asks for maximality at (A) a fixed observed count `x` and (B) every
realizable complete-support `x`. These regimes differ: pointwise
effective-weight domination is sufficient but not necessary at a fixed `x`
(`fixedX_weaker_than_pointwise`), while quantifying over all covered `x`
recovers the pointwise condition (`sampleUniform_iff_pointwise`).

This note evaluates both verdicts on the 30 rigid-but-beaten realizable
truths of the binary-`L6` census cell:

| regime | necessary and sufficient inequality (exact integers) | result on the 30 |
|--------|------------------------------------------------------|------------------|
| (A) fixed `x = A` | `F_B(A) <= F_A(A)` iff `prod_e B_e^A_e (N-B_e)^(n-A_e) <= prod_e A_e^A_e (N-A_e)^(n-A_e)` (separable form) | **30/30 win** |
| (B) every covered `x` | `A` beats `B` everywhere iff `B` has a zero effective weight on `supp A` or `q(B) <= q(A)` pointwise there | **30/30 lose** (all beaten by new-support candidates) |

So every rigid-but-beaten binary-L6 truth is a live fixed-x/uniform gap
instance: it wins at its own truth sample yet is not a sample-uniform
maximizer. The two classification axes are both non-vacuous on realizable
genome spectra, not just on abstract small vectors.

## 2. Conventions (explicit)

* **Candidate length:** same-length binary genomes, read length `L = 6`,
  universe `E` of `2^6 = 64` k-mer classes; genome lengths `G = 6..12`.
* **Normalization `N`:** fixed external, `N = G` (genome length).
* **Support:** truth support `supp A`; competitors range over all
  same-length spectra (new-support candidates admitted). Reduced
  comparisons run over `supp A ∪ supp B` (outside classes contribute
  factor `N` on both sides and cancel exactly).
* **Sample size `n`:** for axis A at the truth sample, `n = sum(A) = G`;
  for axis B, free covered samples `n >= N` with `x >= A` coordinatewise.
* **MB09 §6.1 vs exact objective:** the surrogate retains
  `(N - B_e)^(n - x_e)` for every class including zero-observed ones;
  the exact multinomial (`#256`) has numerator `prod_e B_e^(x_e)` with no
  unobserved factors. Nothing here is imported from `#256`; the gap above
  is a property of the surrogate alone.

## 3. Verification

`scripts/verify_fixedx_gap_realizable_L6_259.py` re-enumerates the
binary-L6 cells with the census's exact reduced arithmetic, and for each
rigid truth beaten sample-uniformly decides the separable fixed-x
inequality at `x = A` with exact `int`s. It asserts the census count
(30 rigid-but-beaten: mismatch fails), cross-checks each gap instance
against a strict beating coordinate (necessity-lemma instance), and
carries the same self-comparison mutation control as the census.

Observed output: `rigid-but-beaten truths=30 (match=True)`,
`win at own sample=30`, `lose at own sample=0`, `OK`
(runs in ~2 min; same cost class as the census cell).

## 4. Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Axis A | fixed-`x` verdict at truth samples for all 30 binary-L6 gap truths | fixed-`x` verdicts on ternary-L6 / quaternary-L4 beaten truths |
| Axis B | sample-uniform failure reproduced (census match) | full new-support class theorem |
| Rigidity | necessity re-confirmed (0 non-rigid maximal in cell); sufficiency fails 30x with gap detail | Lean kernel replay for the new cells |
| CI wiring | one-line step (below; workflow-scope token needed) | `L>=7`, alphabets `>=5`, larger `G` |

```yaml
      - name: Verify #259 fixed-x/uniform gap on realizable L6
        run: python3 scripts/verify_fixedx_gap_realizable_L6_259.py
```
