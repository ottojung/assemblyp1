# Binary-L7 realizable complete-support census (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_realizable_census_L7_259.py` (no Lean import, no floats
in any comparison)._

This note covers one previously open `L>=7` cell for the MB09 §6.1
fixed-external-`N` product-binomial surrogate: binary `L=7`, `G=8..12`.

| cell | genomes | distinct truth spectra | rigid & maximal | rigid & NOT maximal | non-rigid & maximal | non-rigid & NOT maximal |
|------|---------|------------------------|-----------------|---------------------|---------------------|-------------------------|
| binary L=7, G=8..12 | necklaces | 742 | 740 | **2** | **0** | 0 |

Total: **742** new truth spectra, **0** non-rigid maximal
(rigidity-necessity holds in this cell), **2** rigid-but-beaten
(sufficiency fails, both beaten only by new-support candidates).

## Method (exact)

Candidate length, normalization, support, sample size, and the
§6.1-vs-exact distinction are as in `docs/fixedx-product-binomial-259.md`
and `docs/product-binomial-rigidity-necessity-259.md` (same-length
universe `E`, fixed external `N = G`, truth support `supp A`, free covered
sample size `n >= N`, extra `(N-B_j)` factors retained).

Maximality is decided by the kernel-checked covered-sample iff: `A`
beats `B` iff `B` has a zero effective weight on `supp A` or is
pointwise dominated there. The comparison uses the exact reduction of
the L6/Q4 census (classes outside `supp A ∪ supp B` contribute factor
`N` on both sides and cancel), so each comparison needs only
`|supp A ∪ supp B| <= 2G` multiplications on the 128-class universe.

Every recorded violation carries an explicit exact-integer witness
sample `x = A + t*e_i` with `F_B(x) > F_A(x)` (single-coordinate boost
on a strictly-beating class; `t` solved analytically from the log-ratio
then verified with exact integers). Example: `G=12`, covered sample at
`n=100` (`t=88`). A self-comparison mutation control proves the
verifier is not vacuous.

## Reading of the results

- **Necessity holds**: zero non-rigid maximal truths in all 742 spectra,
  confirming the Lean theorem `robust_iff_unique` computationally in a
  new `L>=7` cell.
- **Sufficiency fails**: 2 rigid truths are beaten by new-support
  candidates — rigidity is necessary but not sufficient, as predicted.
- Non-rigid truths are absent in these `G` ranges (small genomes yield
  rigid spectra); non-rigid coverage remains with the earlier binary
  L2..L4 census.

## Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Cells | binary L7 (this note); earlier: binary L5, ternary L5, binary/ternary L6, quaternary L4 (unmerged chain) | larger L/G, alphabets>=5 |
| Classification | realizable complete-support maximality via covered-sample iff | full new-support class theorem (sufficiency fails; no converse) |
| Verification | exact-integer census + explicit witnesses + mutation control | kernel Lean theorem for the new cell (bounded evidence only) |

## CI wiring

```yaml
      - name: Verify #259 binary-L7 realizable census
        run: python3 scripts/verify_realizable_census_L7_259.py
```

(Runs in well under a minute; workflow-scope token needed for
`.github/workflows/ci.yml`, as noted in earlier `#259` docs.)
