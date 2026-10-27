# Quinary-L3 realizable complete-support census (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_realizable_census_Q5L3_259.py` (no Lean import, no floats
in any comparison)._

This note covers one previously open `alphabet>=5` cell for the MB09 §6.1
fixed-external-`N` product-binomial surrogate: quinary (alphabet 5)
`L=3`, `G=5..6`.

| cell | genomes | distinct truth spectra | rigid & maximal | rigid & NOT maximal | non-rigid & maximal | non-rigid & NOT maximal |
|------|---------|------------------------|-----------------|---------------------|---------------------|-------------------------|
| quinary L=3, G=5 | necklaces | 629 | 629 | 0 | **0** | 0 |
| quinary L=3, G=6 | necklaces | 2625 | 2565 | **60** | **0** | 0 |

Total: **3254** new truth spectra, **0** non-rigid maximal
(rigidity-necessity holds in this cell), **60** rigid-but-beaten
(sufficiency fails, each beaten only by new-support candidates with an
explicit exact-integer witness).

## Method (exact)

Candidate length, normalization, support, sample size, and the
§6.1-vs-exact distinction are as in `docs/fixedx-product-binomial-259.md`
and `docs/product-binomial-rigidity-necessity-259.md` (same-length
universe `E` of `5^3 = 125` classes, fixed external `N = G`, truth
support `supp A`, free covered sample size `n >= N`, extra `(N-B_j)`
factors retained, including zero-count coordinates and boundary
probabilities `0`/`1` handled by the exact reduced comparison with a
dedicated `zero_on_support` guard).

Maximality is decided by the kernel-checked covered-sample iff: `A`
beats `B` iff `B` has a zero effective weight on `supp A` or is
pointwise dominated there. The comparison uses the exact reduction of
the earlier realizable census scripts (classes outside
`supp A ∪ supp B` contribute factor `N` on both sides and cancel), so
each comparison needs only `|supp A ∪ supp B| <= 2G` multiplications on
the 125-class universe.

Every recorded violation carries an explicit exact-integer witness
sample `x = A + t*e_i` with `F_B(x) > F_A(x)` (single-coordinate boost
on a strictly-beating class; `t` solved analytically from the log-ratio
then verified with exact integers). Example: `G=6`, covered sample at
`n=38` (`t=32`). A self-comparison plus a one-symbol-mutant pin prove
the verifier is not vacuous, and a comparison counter asserts the
census decided real cross-genome pairs.

## Reading of the results

- **Necessity holds**: zero non-rigid maximal truths in all 3254 spectra,
  confirming the Lean theorem `robust_iff_unique` computationally in a
  new `alphabet>=5` cell.
- **Sufficiency fails**: 60 rigid truths (all at `G=6`) are beaten by
  new-support candidates — rigidity is necessary but not sufficient, as
  predicted. At `G=5` every rigid truth is maximal (honest sub-cell
  with no sufficiency failure).
- Non-rigid truths are absent in these `G` ranges (small genomes yield
  rigid spectra); non-rigid coverage remains with the earlier binary
  L2..L4 census.

## Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Cells | quinary L3 G=5..6 (this note); earlier: binary L5, ternary L5, binary L7, binary/ternary L6, quaternary L4 (unmerged chain) | larger L/G, alphabets>=6 |
| Classification | realizable complete-support maximality via covered-sample iff | full new-support class theorem (sufficiency fails; no converse) |
| Verification | exact-integer census + explicit witnesses + mutation pins | kernel Lean theorem for the new cell (bounded evidence only) |

## CI wiring

```yaml
      - name: Verify #259 quinary-L3 realizable census
        run: python3 scripts/verify_realizable_census_Q5L3_259.py
```

(Runs in well under a minute on the 125-class universe;
workflow-scope token needed for `.github/workflows/ci.yml`, as noted in
earlier `#259` docs.)
